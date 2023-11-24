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
    failwith "DONT KNOW WHAT TO DO HERE"
    )
  | _ -> failwith "todo: implement typecheck_exp"

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
  failwith "todo: implement typecheck_stmt"


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
  failwith "todo: typecheck_fdecl"

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
  failwith "todo: create_struct_ctxt"

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  failwith "todo: create_function_ctxt"


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
