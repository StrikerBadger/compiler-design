(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)
let insn_flow ((u,i):uid * insn) (d:fact) : fact =
  match i with
    (* The result of an alloca is always unique *)
    | Alloca _ -> UidM.add u SymPtr.Unique d
    (* A pointer RETURNED by load may be aliased *)
    | Load ((Ptr (Ptr _)), _) -> UidM.add u SymPtr.MayAlias d
    (* A pointer passed as an argument to store may be aliased *)
    | Store (Ptr _, src_op , _) -> (
      match src_op with
        | Id uid -> UidM.add uid SymPtr.MayAlias d
        | _ -> d
    )
    (* A Pointer returned by a call may be aliased and pointer used as an argument may be aliased *)
    | Call (_, _, args) -> UidM.add u SymPtr.MayAlias (
      List.fold_left (fun d arg ->
        match arg with
          | Ptr _, Id uid -> UidM.add uid SymPtr.MayAlias d
          | _ -> d
      ) d args
    )
    (* A Pointer returned by a bitcast may be aliased and pointer used as an argument may be aliased *)
    | Bitcast (in_ty, src_op, out_ty) -> (
      match in_ty, out_ty with
        | Ptr _, Ptr _ -> UidM.add u SymPtr.MayAlias (
          match src_op with
            | Id uid -> UidM.add uid SymPtr.MayAlias d
            | _ -> d
        )
        | Ptr _, _ -> (
          match src_op with
            | Id uid -> UidM.add uid SymPtr.MayAlias d
            | _ -> d
          )
        | _, Ptr _ -> UidM.add u SymPtr.MayAlias d
        | _ -> d
    )
    (* A Pointer returned by a GEP may be aliased and pointer used as an argument may be aliased *)
    | Gep (in_ty, src_op, _) -> (
      match in_ty with
        | Ptr _ -> UidM.add u SymPtr.MayAlias (
          match src_op with
            | Id uid -> UidM.add uid SymPtr.MayAlias d
            | _ -> d
        )
        | _ -> (
          match src_op with 
            | Id uid -> UidM.add uid SymPtr.MayAlias d
            | _ -> d
          )
    )
    | _ -> UidM.add u SymPtr.UndefAlias d


(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)
    let combine (ds:fact list) : fact =
      let combine_two_symptr (f1:SymPtr.t) (f2:SymPtr.t) : SymPtr.t =
        match f1, f2 with
          | SymPtr.MayAlias, _ -> SymPtr.MayAlias
          | _, SymPtr.MayAlias -> SymPtr.MayAlias
          | SymPtr.Unique, SymPtr.Unique -> SymPtr.Unique
          | SymPtr.UndefAlias, f2 -> f2
          | f1, SymPtr.UndefAlias -> f1
      in
      let merging_facts_function (k:UidM.key) (s1:SymPtr.t option) (s2:SymPtr.t option) =
        match s1, s2 with
          | Some f1, Some f2 -> Some (combine_two_symptr f1 f2)
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
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

