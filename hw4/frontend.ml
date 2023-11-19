open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

let rec ll_typ_of_exp (c:Ctxt.t) (e:Ast.exp) : Ll.ty = 
  match e with
    | CNull rty -> cmp_ty @@ TRef rty
    | CBool _ -> cmp_ty @@ TBool
    | CInt _ -> cmp_ty @@ TInt
    | CStr _ -> cmp_ty @@ TRef RString
    | NewArr (ty, _) -> cmp_ty @@ TRef (RArray ty)
    | Id id -> fst @@ Ctxt.lookup id c
    | Index ({ elt=(NewArr (ty, _)); loc=_ }, index) -> cmp_ty ty  
    | Call (exp, _) -> ll_typ_of_exp c exp.elt
    | Bop (bop, _, _) -> (
      let (bop_ast_ty, _, _) = typ_of_binop bop in
      cmp_ty bop_ast_ty
    )
    | Uop (unop, _) -> cmp_ty @@ fst (typ_of_unop unop)
    | _ -> failwith "Unexpected type in type of exp"

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]


(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)
let get_ty_of_arr ty : Ll.ty =
  match ty with
  | Ptr Struct [_; Array (_, ty1)] -> ty1
  | _ -> failwith @@ "get_ty_of_arr Index not correct type " ^ string_of_ty ty

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull rty -> cmp_ty @@ TRef rty, Null, []
  | CInt i -> I64, Const i, []
  | CBool b -> (match b with 
          | true -> I1, Const 1L, []
          | false -> I1, Const 0L, [])
  | CStr s -> 
    let str_len = String.length s + 1 in
    let str_arr = gensym "str_arr" in
    let str_val = gensym "str_val" in


    let gep_ins = I (str_val, Gep (Ptr (Array (str_len, I8)), Ll.Gid str_arr, [Const 0L;Const 0L])) in    
    let global_ins = G (str_arr, (Array (str_len, I8), GString s)) in
    (Ptr I8), Ll.Id str_val, [gep_ins;global_ins]
  | CArr (t, es) -> 
    let size = List.length es in
    let size_op = Const (Int64.of_int size) in
    let (ty_arr, op_arr, s_arr) = oat_alloc_array t size_op in
    let rec cmp_arr (es : Ast.exp node list) (i : int) : stream =
      match es with
      | [] -> []
      | e :: es -> 
        let (ty, op, s_inside) = cmp_exp c e in
        let index = Const (Int64.of_int i) in

        let gep_var = gensym "gep_idx" in
        let gep_idx_ins = [I (gep_var, Gep (ty_arr, op_arr, [Const 0L; Const 1L; index]))] in
        let var = gensym "idx_carr" in

        let store = [I (var, (Store (ty, op, Ll.Id gep_var)))] in
        s_inside >@ gep_idx_ins >@ store >@ cmp_arr es (i + 1)
    in
    ty_arr, op_arr, s_arr >@ cmp_arr es 0
  | NewArr (t, e) -> 
    let (ty, size_op, size_s) = cmp_exp c e in 
    let (ty_arr, op_arr, s_arr) = oat_alloc_array t size_op in
    ty_arr, op_arr, size_s >@ s_arr
  | Id x -> 
    let ty, operand = Ctxt.lookup x c in

    (match ty with
    | Ptr (Fun (_, fty)) -> (fty, Ll.Gid x, [])
    | Ptr pty -> (
      let ptr_var = gensym "ptr" in
      (pty, Ll.Id ptr_var, [I (ptr_var, Ll.Load (Ptr pty, operand))])
    )
    (* The 2 cases below are git in globals test*)
    | I64 -> 
        let ptr_var = gensym "var_val_id" in
  
        (ty, Ll.Id ptr_var, [I (ptr_var, Ll.Load (Ptr I64, operand))])
  | I1 -> 
      let ptr_var = gensym "var_val_id" in
      (ty, Ll.Id ptr_var, [I (ptr_var, Ll.Load (Ptr I1, operand))])
    | _ -> failwith @@ "cmp_exp Id of ty: " ^ string_of_ty ty)
  | Index (e1, e2) -> 
    let (ty1, op1, s1) = cmp_exp c e1 in
    let (ty2, op2, s2) = cmp_exp c e2 in
    let end_ty = get_ty_of_arr ty1
    in
    let gep_idx = gensym "gep_idx" in
    let index_ptr = [I (gep_idx, Gep (ty1, op1, [Const 0L; Const 1L; op2]))] in
    let var = gensym "loaded_val" in
    (end_ty, Ll.Id var, s1 >@ s2 >@ index_ptr >@ [(I (var, Ll.Load (Ptr end_ty, Ll.Id gep_idx)))])
  | Call (f, es) -> 

    let call_return = gensym "call_return" in
    let (f_ty, f_op, f_s) = cmp_exp c f in


    let arg_info = List.map (fun e -> 
      let (ty, op, s_inside) = cmp_exp c e in
      ((ty, op), s_inside)
    ) es in
    let stream = List.flatten (List.map snd arg_info) in
    let arg_info = List.map fst arg_info in
    (f_ty, Ll.Id call_return, stream 
    >@ [(I (call_return, Ll.Call (f_ty, f_op, arg_info)))])

  | Bop (bop, e1, e2) -> 
    (* I hope this checks out somewhat *)
    let ty1, op1, s1 = cmp_exp c e1 in
    let ty2, op2, s2 = cmp_exp c e2 in
    let bop_ty1, bop_ty2, bop_ty_out = typ_of_binop bop in
    let insn = match bop with
      | Add -> Some Ll.Add, None
      | Sub -> Some Ll.Sub, None
      | Mul -> Some Ll.Mul, None
      (* Comparisons *) 
      | Eq -> None, Some Ll.Eq
      | Neq -> None, Some Ll.Ne
      | Lte -> None, Some Ll.Sle
      | Lt -> None, Some Ll.Slt
      | Gt -> None, Some Ll.Sgt
      | Gte -> None, Some Ll.Sge
      | IAnd -> Some Ll.And, None
      | IOr -> Some Ll.Or, None
      | Shl -> Some Ll.Shl, None
      | Shr -> Some Ll.Lshr, None
      | Sar -> Some Ll.Ashr, None
      | And -> Some Ll.And, None
      | Or -> Some Ll.Or, None
    in 
      let insn = match insn with 
      | None, Some x -> Icmp(x, cmp_ty bop_ty1, op1, op2)
      | Some x, None -> Binop(x, cmp_ty bop_ty1, op1, op2)
      | _ -> failwith "This case really should not occur...."
    in
    let var = gensym "bop" in
    (cmp_ty bop_ty_out, Ll.Id var, s1 >@ s2 >@ [I(var, insn)])
    

  | Uop (uop, e) -> 
    match uop with
    | Neg -> 
      let ty, op, s = cmp_exp c e in
      let var = gensym "neg" in
      (ty, Ll.Id var, s >@ [I(var, Binop(Ll.Sub, I64, Const 0L, op))])
    | Lognot ->
      let ty, op, s = cmp_exp c e in
      let var = gensym "not" in
      (ty, Ll.Id var, s >@ [I(var, Binop(Ll.Xor, I1, Const 1L, op))]) 
    | Bitnot ->
      let ty, op, s = cmp_exp c e in
      let var = gensym "ineg" in
      (ty, Ll.Id var, s >@ [I(var, Binop(Ll.Xor, I64, Const (-1L), op))])

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

 let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Ret (exp_opt) -> 
    (
    match exp_opt with
      | None -> c, [T(Ll.Ret(Ll.Void, None))]
      | Some exp -> 
        (* i have no idea what this mess is about but hey it compiles lul *)
        let ty, op, s = cmp_exp c exp in
        let ret_ty, ret_op = (match exp.elt with
        | Id x -> Ctxt.lookup x c
        | _ -> (I64, Const 1L)) in
        match ret_ty with
        | Void -> failwith "cmp_stmt Ret Some Void unimplemented"
        | I64 
        | I1 -> c, [T(Ll.Ret(ty, Some op))] @ s
        | Ptr ptr -> c, [T(Ll.Ret(ptr, Some op))] @ s
        | _ -> failwith "cmp_stmt Ret Some unimplemented"
    )
    (* Handle other cases here *)
    | _ -> failwith "cmp_stmt not implemented for this case"



(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
(* OCaml code for compiling the global context of an OAT program *)

let cmp_global_ctxt (c: Ctxt.t) (p: Ast.prog) : Ctxt.t =
  (* Helper function to compile a global declaration *)
  let cmp_gdecl (ctxt: Ctxt.t) (gdecl: Ast.decl) : Ctxt.t =
    match gdecl with
    | Ast.Gfdecl _ -> ctxt  (* Ignore function declarations *)
    | Ast.Gvdecl v -> (
        let name, init = v.elt.name, v.elt.init.elt in
        match init with
        | Ast.CNull ty -> Ctxt.add ctxt name (Ptr (cmp_ty (TRef ty)), Gid name)
        | Ast.CBool _ -> Ctxt.add ctxt name (Ptr (cmp_ty TBool), Gid name)
        | Ast.CInt _ -> Ctxt.add ctxt name (Ptr (cmp_ty TInt), Gid name)
        | Ast.CStr s -> Ctxt.add ctxt name (Ptr (cmp_ty (TRef RString)), Gid name)
        | Ast.CArr (t, es) -> Ctxt.add ctxt name (Ptr (cmp_ty (TRef (RArray t))), Gid name)
        | _ -> failwith "non global expression in global context"
      )
  in 
  (* Fold over the program with cmp_gdecl starting from the initial context c *)
  List.fold_left cmp_gdecl c p


(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

 let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  (* Build the Ll function type *)
  let returnty_ll = cmp_ret_ty f.elt.frtyp in
  let paramtys_ll = List.map (fun (ty, id) -> cmp_ty ty) f.elt.args in
  let fty_ll = (paramtys_ll, returnty_ll) in
  (* Allocate stack space per variable and store variable *)
  let handle_one_arg (arg:Ast.ty * Ast.id) : (elt list * Ctxt.t) = 
    let arg_ty, arg_id = fst arg, snd arg in
    let arg_ty_ll = cmp_ty arg_ty in
    let param_id = gensym @@ "param" ^ arg_id in
    let store_param_id = gensym @@ "param_store" ^ arg_id in
    let store_arg_insns = 
       [I (store_param_id, Store (arg_ty_ll, Id arg_id, Id param_id)); I (param_id, Alloca arg_ty_ll)]
    in
    store_arg_insns, Ctxt.add c arg_id (Ptr arg_ty_ll, Ll.Id param_id)
  in
  (* Handle the list of arguments *)
  let copy_args_insns, f_ctxt = 
    List.fold_left (fun ((insns, f_ctxt):(elt list) * Ctxt.t) (arg:Ast.ty * Ast.id)
      -> let arg_insns, arg_ctxt = handle_one_arg arg in
          insns >@ arg_insns, arg_ctxt) ([], c) f.elt.args
  in 
  let ctxt_body, stream_body = cmp_block f_ctxt returnty_ll f.elt.body in
  let arg_ids_ll = List.map (fun x -> snd x) f.elt.args in
  let cfg_ll, right_out_ll = cfg_of_stream (copy_args_insns >@ stream_body) in
  let fdecl_ll = { f_ty=fty_ll; f_param=arg_ids_ll; f_cfg=cfg_ll } in
  fdecl_ll, right_out_ll
(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
    | CNull retty -> (Ptr (cmp_rty retty), GNull), []
    | CBool b -> (I1, GInt (if b then 1L else 0L)), []
    | CInt i -> (I64, GInt i), []
    | CStr s -> 
       let gid = gensym "glob_str" in
       let strlen = String.length s + 1 in
       (Ptr I8, GBitcast (Ptr (Array (strlen, I8)), GGid gid, Ptr I8)),
       [(gid, (Array (strlen, I8), GString s))]
    | CArr (ty, es) ->
       let arr_ty = cmp_ty ty in
       let gid = gensym "glob_arr" in
       let arrlen = List.length es in
       let build_arr_struct (len:int) : Ll.ty =
        Struct [I64; Array (len, arr_ty)]
       in
       let gdecl_info, gdecls_info  = List.fold_left (fun (old_gdecl, old_gdecls) e -> 
        let gdecl, gdecls = cmp_gexp c e in
        [gdecl] >@ old_gdecl, old_gdecls >@ gdecls
       ) ([], []) es in
       (Ptr (build_arr_struct 0), GBitcast (Ptr (build_arr_struct arrlen), GGid gid, Ptr (build_arr_struct 0))),
       [(gid, (build_arr_struct arrlen, GStruct [(I64, (GInt (Int64.of_int arrlen))); (Array (arrlen, arr_ty), GArray gdecl_info)]))] >@ gdecls_info
    | _ -> failwith "Invalid global initializer"


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
