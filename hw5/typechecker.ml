open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t2 with
    | TInt -> t1 = TInt
    | TBool -> t1 = TBool
    | TRef rty2 -> (
      match t1 with
        | TRef rty1 -> subtype_ref c rty1 rty2
        | _ -> false
      )
    | TNullRef rty2 -> (
      match t1 with
        | TNullRef rty1 -> subtype_ref c rty1 rty2
        | TRef rty1 -> subtype_ref c rty1 rty2
        | _ -> false
      )

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  let subtype_ret_ty (r1 : Ast.ret_ty) (r2 : Ast.ret_ty) : bool =
    match r1, r2 with
    | RetVoid, RetVoid -> true
    | RetVal t1, RetVal t2 -> subtype c t1 t2
    | _ -> false
  in
  match t2 with
    | RString -> t1 = RString
    | RArray arrty2 -> (
      match t1 with
        | RArray arrty1 -> arrty1 = arrty2
        | _ -> false
      )
    | RStruct id2 -> (
      let structfields2 = lookup_struct id2 c in
      match t1 with
        | RStruct id1 -> (
          let rec check_fields (fs2 : Ast.field list) : bool =
            match fs2 with
              | [] -> true
              | field::fs2' -> (lookup_field_option id1 field.fieldName c = Some field.ftyp) && (check_fields fs2')
          in
          check_fields structfields2
        )
        | _ -> false
      )
    | RFun (args2, ret2) -> (
      match t1 with
        | RFun (args1, ret1) -> (List.length args1 = List.length args2) &&
                                (List.for_all2 (fun t1 t2 -> subtype c t2 t1) args1 args2) &&
                                subtype_ret_ty ret1 ret2
        | _ -> false
      )


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
    | TBool | TInt -> ()
    | TRef rty | TNullRef rty -> typecheck_rty l tc rty

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  let typecheck_ret_ty (r : Ast.ret_ty) : unit =
    match r with
    | RetVoid -> ()
    | RetVal t -> typecheck_ty l tc t
  in
  match t with
    | RString -> ()
    | RArray arrty -> typecheck_ty l tc arrty
    | RStruct id -> (
      match lookup_struct_option id tc with
        | Some _ -> ()
        | None -> type_error l ("Undefined struct type " ^ id)
      )
    | RFun (args, ret) -> (
      List.iter (typecheck_ty l tc) args;
      typecheck_ret_ty ret
    )

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull rty ->  let ty = TNullRef rty in
                  typecheck_ty e c ty;
                  ty
  | CBool b -> TBool
  | CInt i -> TInt
  | CStr s -> TRef RString
  | Id id -> (
      let localty = lookup_local_option id c in
      match localty with
        | Some ty ->  typecheck_ty e c ty;
                      ty
        | None -> (
          let globalty = lookup_global_option id c in
          match globalty with
            | Some ty ->  typecheck_ty e c ty;
                          ty
            | None -> type_error e ("Id not in local or global context: " ^ id)
        )
    )
  | CArr (arrty, exps) -> (
      if List.for_all (fun x -> subtype c (typecheck_exp c x) arrty) exps then (
        typecheck_ty e c arrty;
        TRef (RArray arrty)
      ) else type_error e ("Array element expressions not subtypes")
    )
  | NewArr (arrty, lenexp, index, initexp) -> (
      typecheck_ty e c arrty;
      if typecheck_exp c lenexp <> TInt then 
        type_error e ("Array length expression not of type int");
      match lookup_local_option index c with
        | Some _ -> type_error e ("Index variable shadows a local")
        | None -> (
          let ctxt_with_index = (add_local c index TInt) in
          let init_expr_ty = typecheck_exp c initexp in
          if subtype ctxt_with_index init_expr_ty arrty then
            TRef (RArray arrty)
          else type_error e ("Array init expression not subtype of array type")
        )
    )
  | Index (arr_exp, index_exp) -> (
      let arrty = typecheck_exp c arr_exp in
      match arrty with
        | TRef (RArray arrty') -> (
          if typecheck_exp c index_exp <> TInt then
            type_error e ("Index expression not of type int");
          arrty'
          )
        | _ -> type_error e ("Index expression not of type array")
    )
  | Length exp -> (
      match typecheck_exp c exp with
        | TRef (RArray _) -> TInt
        | _ -> type_error e ("Length expression not of type array")
    )
  | CStruct (id, fields) -> (
      let structfields = lookup_struct_option id c in
      let rec check_fields (fs : Ast.field list) : unit =
        match fs with
          | [] -> ()
          | field::fs' -> (
            match lookup_field_option id field.fieldName c with
              | Some field' -> (
                if subtype c field.ftyp field' then
                  check_fields fs'
                else type_error e ("Field " ^ field.fieldName ^ " not subtype of struct field")
                )
              | None -> type_error e ("Field " ^ field.fieldName ^ " not in struct")
            )
      in
      match structfields with
        | Some structfields -> (
            if List.length structfields <> List.length fields then
              type_error e ("Wrong number of fields in struct");
            let fields =
              List.map (fun (id, exp) -> { fieldName=id; ftyp=(typecheck_exp c exp) }) fields
            in
            check_fields fields;
            TRef (RStruct id)
          )
        | None -> type_error e ("Struct type " ^ id ^ " not in context")
    )
  | Proj (exp, id) -> (
    match typecheck_exp c exp with
      | TRef (RStruct sid) -> (
        match lookup_struct_option sid c with
          | None -> type_error e "Struct on which field access was tried is not in context"
          | Some fields -> (
            match lookup_field_option sid id c with
              | None -> type_error e "Tried to access non-existing struct field"
              | Some ty -> ty
            )
        )
      | _ -> type_error e "Proj expression is not a struct"
    )
  | Call (fexp, argexps) -> (
    match typecheck_exp c fexp with
      | TRef (RFun (argtys, ret_ty)) -> (
        if List.length argtys <> List.length argexps then
          type_error e "Wrong number of arguments to function call";
        let rec check_args (argtys : Ast.ty list) (argexps : Ast.exp node list) : unit =
          match argtys, argexps with
            | [], [] -> ()
            | argty::argtys', argexp::argexps' -> (
              if subtype c (typecheck_exp c argexp) argty then
                check_args argtys' argexps'
              else type_error e "Argument expression not subtype of argument type"
              )
            | _, _ -> type_error e "Should never arrive here, check_args"
        in
        check_args argtys argexps;
        match ret_ty with
          | RetVoid -> failwith "what is the type of a void return?"
          | RetVal ty -> ty
        )
      | _ -> type_error e "Call expression is not a function"
    )
  | Bop (bop, exp1, exp2) -> (
    match bop with 
    | Eq | Neq -> (
      let t1 = typecheck_exp c exp1 in
      let t2 = typecheck_exp c exp2 in
      if subtype c t1 t2 && subtype c t2 t1 then
        TBool
      else type_error e "Expressions in equality comparison not subtypes of each other"
      )
    | _ -> (
      let (t1, t2, t3) = typ_of_binop bop in
      if subtype c (typecheck_exp c exp1) t1 then
        if subtype c (typecheck_exp c exp2) t2 then
          t3
        else type_error e "Second expression in binary operation not subtype of expected type"
      else type_error e "First expression in binary operation not subtype of expected type"
      )
    )
  | Uop (uop, exp) -> (
    let (t1, t2) = typ_of_unop uop in
    if (typecheck_exp c exp) = t1 then
      t2
    else type_error e "Expression in unary operation not of expected type"
    )

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return
        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with
    | Decl (id, exp) -> (
      if lookup_local_option id tc <> None then
        type_error s ("Variable " ^ id ^ " already declared in this scope")
      else 
        add_local tc id (typecheck_exp tc exp), false
      )
    | Assn (lhs_exp, rhs_exp) -> (
      match lhs_exp.elt with
        | Id id -> (
          match lookup_local_option id tc with
            | Some ty -> (
              if subtype tc (typecheck_exp tc rhs_exp) ty then
                tc, false
              else type_error s "Right hand side of assignment not subtype of left hand side"
              )
            | None -> (
              match lookup_global_option id tc with
                | Some (TRef (RFun (_, _))) | Some (TNullRef (RFun (_, _))) -> 
                  type_error s "Cannot assign to function"
                | Some ty -> (
                  if subtype tc (typecheck_exp tc rhs_exp) ty then
                    tc, false
                  else type_error s "Right hand side of assignment not subtype of left hand side"
                  )
                | None -> type_error s "Left hand side of assignment not in context"
              )
        )
        | _ -> type_error s "Left hand side of assignment is not an identifier"
      )
    | SCall (fexp, argexps) -> (
      match typecheck_exp tc fexp with
        | TRef (RFun (argtys, ret_ty)) -> (
          if List.length argtys <> List.length argexps then
            type_error s "Wrong number of arguments to function call";
          let rec check_args (argtys : Ast.ty list) (argexps : Ast.exp node list) : unit =
            match argtys, argexps with
              | [], [] -> ()
              | argty::argtys', argexp::argexps' -> (
                if subtype tc (typecheck_exp tc argexp) argty then
                  check_args argtys' argexps'
                else type_error s "Argument expression not subtype of argument type"
                )
              | _, _ -> type_error s "Should never arrive here, check_args"
          in
          check_args argtys argexps;
          match ret_ty with
            | RetVoid -> tc, false
            | _ -> type_error s "Call statement to function that returns a value"
          )
        | _ -> type_error s "Call expression is not a function"
      )
    | If (con_exp, true_block, false_block) -> ( (* NEEDS FIXING *)
        match con_exp.elt with
          | Bop (Eq, exp1, exp2) -> (
            let t1 = typecheck_exp tc exp1 in
            let t2 = typecheck_exp tc exp2 in
            match t1 with
              | TRef rty | TNullRef rty -> (
                match t2 with
                  TRef rty | TNullRef rty -> (
                    if not @@ subtype tc t2 t1 then
                      type_error s "Equality comparison between non-subtypes";
                    (* May need to add ref x to locals here*)
                    let (_, returns) = typecheck_block tc true_block to_ret in
                    let (_, returns') = typecheck_block tc false_block to_ret in
                    tc, returns && returns'
                    )
                  | _ -> type_error s "Equality comparison between non-references"
                )
              | _ -> type_error s "Equality comparison between non-references"
            )
          | _ -> type_error s "Condition expression in if statement is not an equality comparison"
      )
    | While (con_exp, block) -> (
        match typecheck_exp tc con_exp with
          | TBool -> (
            let (_, _) = typecheck_block tc block to_ret in
            tc,  false
            )
          | _ -> type_error s "Condition expression in while statement is not of type bool"
      )
    | For (vdecls, con_exp, inc_stmt, block) -> (
        let rec check_vdecls (c:Tctxt.t) (vdecls:Ast.vdecl list) : Tctxt.t =
          match vdecls with
            | [] -> c
            | vdecl::vdecls' -> (
              let (c', _) = typecheck_stmt c { elt=(Decl vdecl); loc=(snd vdecl).loc } to_ret in
              check_vdecls c' vdecls'
              )
        in
        let c' = check_vdecls tc vdecls in
        let con_exp = match con_exp with
          | None -> {elt=(CBool true); loc=s.loc}
          | Some con_exp -> con_exp
        in
        match typecheck_exp c' con_exp with
          | TBool -> (
            let (_, _) = typecheck_block c' block to_ret in
            match inc_stmt with
              | None -> tc, false
              | Some inc_stmt -> 
                let (c, _) = typecheck_stmt c' inc_stmt to_ret in
                c, false
            )
          | _ -> type_error s "Condition expression in for statement is not of type bool"
      )
    | Ret exp_opt -> (
      let ret_ty = match exp_opt with
        | None -> RetVoid
        | Some exp -> RetVal (typecheck_exp tc exp)
      in
      match ret_ty with
        | RetVoid -> tc, true
        | RetVal ty -> (
          match to_ret with
            | RetVoid -> type_error s "Return statement in void function"
            | RetVal to_ret_ty -> (
              if subtype tc ty to_ret_ty then
                tc, true
              else type_error s "Return expression not subtype of function return type"
              )
          )
      )
    | Cast _ -> failwith "Cast something you fucker"
  
and typecheck_block (c:Tctxt.t) (b:Ast.block) (to_ret:ret_ty) : Tctxt.t * bool =
  let rec check_stmts (c:Tctxt.t) (ss:Ast.block) (returns:bool) : Tctxt.t * bool =
    match ss with
      | [] -> c, false
      | s::[] -> typecheck_stmt c s to_ret
      | s::ss' -> (
        let (c', returns) = typecheck_stmt c s to_ret in
        if returns then
          type_error s "Early return"
        else
          let (c'', returns') = check_stmts c' ss' returns in
          c'', returns'
        )
  in
  check_stmts c b false


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let tc_with_args = List.fold_left (fun (ctxt : Tctxt.t) ((argty, argid) : ty * id) ->
    add_local ctxt argid argty) tc f.args
  in
  let rec check_args_for_duplicates (args : (ty * id) list) : unit =
    match args with
      | [] -> ()
      | (_, argid)::args' -> (
        if List.exists (fun id -> id = argid) (List.map snd args') then
          type_error l ("Duplicate argument name " ^ argid ^ " in function " ^ f.fname)
        else check_args_for_duplicates args'
        )
  in
  check_args_for_duplicates f.args;
  let (_, returns) = typecheck_block tc_with_args f.body f.frtyp in
  if not returns then
    type_error l ("Function " ^ f.fname ^ " does not return")
  else ()

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let empty_ctxt = { locals=[]; globals=[]; structs=[] } in
  List.fold_left (fun (ctxt : Tctxt.t) (d : Ast.decl) ->
    match d with
      | Gtdecl { elt=(id, fs); loc=l} -> (
        match lookup_struct_option id ctxt with
          | Some _ -> type_error { elt=(id, fs); loc=l} ("Duplicate struct type " ^ id)
          | None -> add_struct ctxt id fs
        )
      | _ -> ctxt (* Not a structdecl *)
    ) empty_ctxt p

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun (ctxt : Tctxt.t) (d : Ast.decl) ->
    match d with
      | Gfdecl { elt=f; loc=l } -> (
        match lookup_global_option f.fname ctxt with
          | Some _ -> type_error { elt=f; loc=l } ("Duplicate function " ^ f.fname)
          | None -> add_global ctxt f.fname (TRef (RFun (List.map fst f.args, f.frtyp)))
        )
      | _ -> ctxt (* Not a functiondecl *)
    ) tc p

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun (ctxt : Tctxt.t) (d : Ast.decl) ->
    match d with
      | Gvdecl { elt=gdecl; loc=l } -> (
        match lookup_global_option gdecl.name ctxt with
          | Some _ -> type_error { elt=gdecl; loc=l } ("Duplicate global " ^ gdecl.name)
          | None -> (
            let ctxt_without_globals = { ctxt with globals=[] } in
            let ty = typecheck_exp ctxt_without_globals gdecl.init in
            match ty with
              | TRef (RFun (_, _)) | TNullRef (RFun (_, _)) -> 
                type_error { elt=gdecl; loc=l } ("Global " ^ gdecl.name ^ " cannot be a function")
              | _ -> add_global ctxt gdecl.name ty
            )
        )
      | _ -> ctxt (* Not a globaldecl *)
    ) tc p


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
