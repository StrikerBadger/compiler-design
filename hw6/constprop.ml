open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let get_operand_symval (op:Ll.operand) =
    match op with
      | Ll.Const i -> SymConst.Const i
      | Ll.Id uid -> (
        match UidM.find_opt uid d with
          | Some x -> x
          | _ -> SymConst.UndefConst
        )
      | _ -> SymConst.NonConst
  in
  match i with 
    | Binop (bop, _, op1, op2) -> (
      let v1, v2 = get_operand_symval op1, get_operand_symval op2 in
      match (v1, v2) with
        | (SymConst.Const i1, SymConst.Const i2) -> (
          let res = 
            match Llinterp.interp_bop bop (VInt i1) (VInt i2) with
              | VInt i -> SymConst.Const i
              | _ -> failwith "Constprop.insn_flow: interp_bop returned non-integer"
          in
          UidM.add u res d
          )
        | (SymConst.UndefConst, _) | (_, SymConst.UndefConst) -> UidM.add u SymConst.UndefConst d
        | _ -> UidM.add u SymConst.NonConst d
      )
    | Icmp (con, _, op1, op2) -> (
      let v1, v2 = get_operand_symval op1, get_operand_symval op2 in
      match (v1, v2) with
        | (SymConst.Const i1, SymConst.Const i2) -> (
          let res = 
            match Llinterp.interp_cnd con (VInt i1) (VInt i2) with
              | VInt i -> SymConst.Const i
              | _ -> failwith "Constprop.insn_flow: interp_bop returned non-integer"
          in
          UidM.add u res d
          )
        | (SymConst.UndefConst, _) | (_, SymConst.UndefConst) -> UidM.add u SymConst.UndefConst d
        | _ -> UidM.add u SymConst.NonConst d
      )
    | Store _ | Call (Void, _, _) -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      let combine_two_symconst (f1:SymConst.t) (f2:SymConst.t) : SymConst.t =
        match f1, f2 with
          | SymConst.NonConst, _ | _, SymConst.NonConst -> SymConst.NonConst
          | SymConst.UndefConst, a | a, SymConst.UndefConst -> a
          | SymConst.Const i1, SymConst.Const i2 -> if i1 = i2 then SymConst.Const i1 else SymConst.NonConst
      in
      let merging_facts_function (k:UidM.key) (s1:SymConst.t option) (s2:SymConst.t option) =
        match s1, s2 with
          | Some f1, Some f2 -> Some (combine_two_symconst f1 f2)
          | Some f1, None -> Some f1
          | None, Some f2 -> Some f2
          | None, None -> None
      in
      List.fold_left (fun l r -> UidM.merge merging_facts_function l r) UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let convert_op (op:Ll.operand) (const_map:fact): Ll.operand =
      match op with
        | Ll.Id uid -> (
          match UidM.find_opt uid const_map with
            | Some x -> (
              match x with
                | SymConst.Const i -> Ll.Const i
                | _ -> op
              )
            | None -> op
          )
        | _ -> op
    in
    let convert_one_insn ((u,i):Ll.uid * Ll.insn) : Ll.uid * Ll.insn =
      let const_map = cb u in
      let ins = 
        match i with
          | Binop (bop, t, op1, op2) -> Binop (bop, t, convert_op op1 const_map, convert_op op2 const_map)
          | Icmp (con, t, op1, op2) -> Icmp (con, t, convert_op op1 const_map, convert_op op2 const_map)
          | Store (t, op1, op2) -> Store (t, convert_op op1 const_map, convert_op op2 const_map)
          | Call (t, op, args) -> Call (t, convert_op op const_map, List.map (fun (t,o) -> t, convert_op o const_map) args)
          | _ ->  i
      in
      u, ins
    in
    let transformed_terminator =
      let const_map = cb (fst b.term) in
      let term_uid = fst b.term in
      let terminator = snd b.term in
      match terminator with
        | Ret (ty, Some op) -> term_uid, Ret (ty, Some (convert_op op const_map))
        | Cbr (op, l1, l2) -> term_uid, Cbr (convert_op op const_map, l1, l2)
        | _ -> b.term
    in
    let transformed_block = { insns=List.map convert_one_insn b.insns; term=transformed_terminator } in
    { cfg with blocks = LblM.add l transformed_block cfg.blocks }
  in
  LblS.fold cp_block (Cfg.nodes cfg) cfg
