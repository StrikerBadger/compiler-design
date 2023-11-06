(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m

(*Function to get at most the first n elements of a list*)
let rec get_first_n (n:int) (lst:'a list) : 'a list =
  if n < 1 then [] else 
    match lst with
    | [] -> []
    | h::t -> if n = 0 then [] else h::(get_first_n (n-1) t)

(*Function to remove duplicates from a list (preserves ordering)*)
let rec remove_duplicates (lst:'a list) : 'a list =
  match lst with
    | [] -> []
    | h::tl -> h::remove_duplicates (List.filter (fun (e:'a) -> e <> h) tl)


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  function (operand:Ll.operand) ->
    match operand with
    | Null -> (Movq, [Imm (Lit 0L); dest])
    | Const c -> (Movq, [Imm (Lit c); dest])
    | Gid gid -> (Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); dest])
    | Id uid -> (Movq, [lookup ctxt.layout uid; dest])


(* compiling call  ---------------------------------------------------------- *)

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand = 
  let open Asm
  in
  match n with
    | 0 -> ~%Rdi
    | 1 -> ~%Rsi
    | 2 -> ~%Rdx
    | 3 -> ~%Rcx
    | 4 -> ~%R08
    | 5 -> ~%R09
    | _ -> Ind3 (Lit (Int64.of_int (8 * (n - 4))), Rbp)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)
let compile_call (ctxt:ctxt) (fnctn_pointer:Ll.operand) (args:Ll.operand list) : ins list = 
  let open Asm 
  in
  let args : operand list =
    let get_val_of_operand (op:Ll.operand) : operand =
      match op with
       | Null -> ~$0
       | Const c -> Imm (Lit c)
       | Gid gid -> Ind3 (Lbl (Platform.mangle gid), Rip)
       | Id uid -> lookup ctxt.layout uid
    in
    List.map get_val_of_operand args
  in
  let put_args : ins list = 
    let put_arg_to_reg (i:int) (argop:operand) : ins list =
      if i < 6 then 
        (
        match argop with
          | Ind3 (_, Rip) -> [(Leaq, [argop; arg_loc i])]
          | _ -> [(Movq, [argop; arg_loc i])]
        )
      else
        (
        failwith "argument index to high to put in reg"
        )
    in 
    let put_arg_on_stack (argop:operand) : ins list = 
      match argop with
          | Ind3 (_, Rip) -> [(Leaq, [argop; ~%Rax]); (Pushq, [~%Rax])]
          | _ -> [(Pushq, [argop])]
    in
    List.concat (List.mapi put_arg_to_reg (get_first_n 6 args) @ List.map put_arg_on_stack (get_first_n (List.length args - 6) (List.rev args)))
  in
  let call : ins list = 
    match fnctn_pointer with
      | Null -> failwith "tried to call Null"
      | Const c -> [(Callq, [Imm (Lit c)])]
      | Gid gid -> [(Callq, [Imm (Lbl (Platform.mangle gid))])]
      | Id uid -> [compile_operand ctxt ~%Rax fnctn_pointer; (Callq, [lookup ctxt.layout uid])]
  in
  [Andq, [Imm(Lit(-16L)); Reg Rsp]] @ put_args @ call



(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  match t with
    | Void | I8 | Fun _ -> 0
    | I1 | I64 | Ptr _ -> 8
    | Array(n, subt) -> n * (size_ty tdecls subt)
    | Namedt(tid) -> size_ty tdecls @@ lookup tdecls tid
    | Struct tys -> List.fold_left (+) 0 @@ List.map (size_ty tdecls) tys





(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) ((ty, op): Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  let open Asm 
  in
  let ty : Ll.ty = 
    match ty with
      | Ptr t -> t
      | _ -> failwith "gep operand not a pointer"
  in
  let ty : Ll.ty =
    match ty with
      | Namedt tid -> lookup ctxt.tdecls tid
      | _ -> ty
  in
  let get_base_adress : ins list = [compile_operand ctxt ~%Rax op]
  in
  let index_array : ins list = [compile_operand ctxt ~%Rbx (List.hd path); (Imulq, [~$(size_ty ctxt.tdecls ty); ~%Rbx]); (Addq, [~%Rbx; ~%Rax])]
  in
  let path : Ll.operand list = List.tl path
  in
  let rec index_subsequent (ty:Ll.ty) (path:Ll.operand list): ins list =
    if path = [] then [] else
    let ty : Ll.ty =
      match ty with
        | Namedt tid -> lookup ctxt.tdecls tid
        | _ -> ty
    in
    match ty with
      | Struct tys -> 
        (
        let rec get_offset (tys:Ll.ty list) (index:int) : int =
          match tys with
            | [] -> failwith "struct has no types"
            | h::t -> if index = 0 then 0 else size_ty ctxt.tdecls h + get_offset t (index - 1)
        in
        let index = match List.hd path with
                      | Const c -> Int64.to_int c
                      | _ -> failwith "index in struct not a constant"
        in
        let deeper_type : Ll.ty = List.nth tys index
        in
        let deeper_type : Ll.ty =
          match deeper_type with
            | Namedt tid -> lookup ctxt.tdecls tid
            | _ -> deeper_type
        in 
        [Addq, [~$(get_offset tys index); ~%Rax]] @ index_subsequent deeper_type (List.tl path)
        )
      | Array (n, subt) -> 
        (
        [compile_operand ctxt ~%Rbx (List.hd path); (Imulq, [~$(size_ty ctxt.tdecls subt); ~%Rbx]); (Addq, [~%Rbx; ~%Rax])] @ index_subsequent subt (List.tl path)
        )
      | _ ->  print_endline ("Failed at: " ^ Llutil.string_of_ty ty);
              failwith "path is invalid"
    in
    if path = [] then get_base_adress @ index_array else
      get_base_adress @ index_array @ index_subsequent ty path

  



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  let open Asm
  in
  (* If uid is not in dict, add it (0 default value) *)
  let pull_operands_and_execute = (
    match i with
      | Binop (bop, _, op1, op2) ->
        (
        let put_operands (xop1:operand) (xop2:operand) = [compile_operand ctxt xop1 op1; compile_operand ctxt xop2 op2]
        in
        match bop with
        | Add -> put_operands ~%Rbx ~%Rax @ [(Addq, [~%Rbx; ~%Rax])]
        | Sub -> put_operands ~%Rax ~%Rbx @ [(Subq, [~%Rbx; ~%Rax])]
        | Mul -> put_operands ~%Rbx ~%Rax @ [(Imulq, [~%Rbx; ~%Rax])]
        | Shl -> put_operands ~%Rax ~%Rcx @ [(Shlq, [~%Rcx; ~%Rax])]
        | Lshr -> put_operands ~%Rax ~%Rcx @ [(Shrq, [~%Rcx; ~%Rax])]
        | Ashr -> put_operands ~%Rax ~%Rcx @ [(Sarq, [~%Rcx; ~%Rax])]
        | And -> put_operands ~%Rbx ~%Rax @ [(Andq, [~%Rbx; ~%Rax])]
        | Or -> put_operands ~%Rbx ~%Rax @ [(Orq, [~%Rbx; ~%Rax])]
        | Xor -> put_operands ~%Rbx ~%Rax @ [(Xorq, [~%Rbx; ~%Rax])]
        )
      | Icmp (cnd, _, op1, op2) -> 
        ( 
        let put_operands (xop1:operand) (xop2:operand) = [compile_operand ctxt xop1 op1; compile_operand ctxt xop2 op2]
        in
        put_operands ~%Rbx ~%Rax @ [(Cmpq, [~%Rax; ~%Rbx]); (Movq, [~$0; ~%Rax]); (Set (compile_cnd cnd), [~%Rax])]
        )
      | Alloca _ -> [(Pushq, [~$0]); (Movq, [~%Rsp; ~%Rax])]
      | Load (_, op) -> 
        (
        match op with
          | Null -> failwith "tried to load from Null"
          | Const c -> [(Movq, [Ind1 (Lit c); ~%Rax])]
          | Gid gid -> [(Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); ~%Rax]); (Movq, [Ind2 Rax; ~%Rax])]
          | Id uid -> [(Movq, [lookup ctxt.layout uid; ~%Rax]); (Movq, [Ind2 Rax; ~%Rax])]
        )
      | Store (_, op1, op2) -> 
        (
        let put_val : ins list = 
          match op1 with
          | Null -> failwith "Null has no value"
          | Const c -> [(Movq, [Imm (Lit c); ~%Rax])]
          | Gid gid -> [(Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); ~%Rax]); (Movq, [Ind2 Rax; ~%Rax])]
          | Id uid -> [(Movq, [lookup ctxt.layout uid; ~%Rax])]
        in
        match op2 with
          | Null -> failwith "tried to store to Null"
          | Const c -> put_val @ [(Movq, [~%Rax; Ind1 (Lit c)])]
          | Gid gid -> put_val @ [(Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); ~%Rbx]); (Movq, [~%Rax; Ind2 Rbx])]
          | Id uid -> put_val @ [(Movq, [lookup ctxt.layout uid; ~%Rbx]); (Movq, [~%Rax; Ind2 Rbx])]
        )
      | Call (_, op1, args) -> compile_call ctxt op1 (List.map (fun ((ty, op):ty * Ll.operand) -> op) args)
      | Bitcast (_, op, _) -> [compile_operand ctxt ~%Rax op]
      | Gep (ty, base, path) -> compile_gep ctxt (ty, base) path
  )
  in
  let put_result = 
    match i with
      | Call (Void, _, _) -> []
      | _ -> [(Movq, [~%Rax; lookup ctxt.layout uid])]
  in
  pull_operands_and_execute @ put_result

(* compiling blocks --------------------------------------------------------- *)

(* A block is a sequence of instructions terminated by a terminator
   instruction.  The terminator instruction determines the control
   flow of the program.  For example, a terminator instruction might
   be a return instruction, which terminates the current function and
   returns control to the caller.

   The compilation of a block should generate a list of X86
   instructions that ends with a jump to the appropriate block
   label. (See compile_terminator below.)

   [ NOTE: the last instruction in a block should be a jump. ]

   [ NOTE: the LLVM IR ensures that every block ends with a
   terminator instruction. ] *)

(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let open Asm
  in
  let clean_stack = [(Movq, [~%Rbp; ~%Rsp]); (Popq, [~%Rbp]); (Retq, [])]
  in
  let handle_terminator = match t with
                            | Ret (_, None) -> clean_stack
                            | Ret (_, Some op) -> compile_operand ctxt ~%Rax op::clean_stack
                            | Br lbl -> [(Jmp, [~$$(mk_lbl fn lbl)])]
                            | Cbr (op, lbl1, lbl2) -> compile_operand ctxt ~%Rax op::[(Cmpq, [~$1; ~%Rax]);
                                                       (J X86.Eq, [~$$(mk_lbl fn lbl1)]);
                                                       (Jmp, [~$$(mk_lbl fn lbl2)])]
  in
  handle_terminator
(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
(*blk : { insns : (uid * insn) list; term : (uid * terminator) }*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  List.concat_map (compile_insn ctxt) blk.insns @ compile_terminator fn ctxt (snd blk.term)

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let extract_uids_from_block (b:block) : uid list =
    List.map (fun (uid_ins:uid * insn) -> fst uid_ins) b.insns
  in
  let extracted_uids : uid list = 
    extract_uids_from_block block @ List.concat_map (fun ((lbl, block):lbl * block) -> extract_uids_from_block block) lbled_blocks
  in
  let all_uids : uid list = remove_duplicates (args @ extracted_uids)
  in
  let rec build_layout (uids:uid list) : (uid * operand) list =
    match uids with
      | [] -> []
      | u::us -> (u, Ind3 (Lit (Int64.of_int (-8*(List.length all_uids - List.length us))), Rbp))::build_layout us
  in
  build_layout all_uids
(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  let open Asm
  in
  (*Get the stack layout*)
  let layout = stack_layout f_param f_cfg
  in
  let ctxt = { tdecls = tdecls; layout = layout }
  in
  (*Decrement stack pointer for locals storage and set new bp *)
  let dec_sp_and_set_bp = 
    [(Pushq, [~%Rbp]); (Movq, [~%Rsp; ~%Rbp]); (Subq, [Imm (Lit (Int64.of_int (8 * List.length layout))); ~%Rsp])]
  in
  (*Copy over the arguments from the argument locations*)
  let arg_indeces = List.mapi (fun i x -> (x, i)) f_param in (*Argument indeces*)
  let copy_one_arg = fun (uid_to_op_mapping:uid * operand) : ins list ->
    [(Movq, [arg_loc (lookup arg_indeces (fst uid_to_op_mapping)); ~%Rax]); (Movq, [~%Rax; (snd uid_to_op_mapping)])]
  in
  let copy_args = List.concat_map copy_one_arg (List.filter (fun ((uid, _):uid * operand) -> List.mem uid f_param) layout)
  in
  let compiled_lbl_blocks = 
    let acc_func = fun (elems:elem list) (lbl, blk) -> elems @ [(compile_lbl_block name lbl ctxt blk)]
    in
    List.fold_left acc_func [] (snd f_cfg)
  in
  let compile_entry = compile_block name ctxt (fst f_cfg)
  in
  (*Glue the program together and create the elem*)
  { lbl = name; global = true; asm = (Text (dec_sp_and_set_bp @ copy_args @ compile_entry))}::compiled_lbl_blocks


(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
