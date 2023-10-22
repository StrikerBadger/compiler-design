(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun (code:cnd) ->
  match code with
    | Eq -> fz
    | Neq -> not fz
    | Lt -> fs <> fo
    | Le -> (fs <> fo) || fz
    | Gt -> (fs == fo) && not fz
    | Ge -> fs == fo

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option = if addr >= mem_top || addr < mem_bot then None else
  Some (Int64.to_int (Int64.sub addr mem_bot))

let rec save_sbytes_to_mem_helper (i:int) (loc:quad) (data:sbyte list) (s:mach) : unit =
  match data with
    | [] -> ()
    | b::bs -> let mem_index = map_addr (Int64.add loc (Int64.of_int i)) in
                                match mem_index with
                                  | None -> ()
                                  | Some mem_index -> s.mem.(mem_index) <- b;
                                save_sbytes_to_mem_helper (i+1) loc bs s

let save_sbytes_to_mem (loc:quad) (data:sbyte list) (s:mach) : unit =
  save_sbytes_to_mem_helper 0 loc data s

let save_quad_to_mem (loc:quad) (data:quad) (s:mach) : unit = 
  save_sbytes_to_mem loc (sbytes_of_int64 data) s

(* IN: Operand
   OUT: unit
   DESCRIPTION: Put a quad into an operand/location*)
let put_quad (op:operand) (qd:quad) (s:mach) : unit = 
  match op with
    | Reg r -> s.regs.(rind r) <- qd
    | Ind1 (Lit q) -> save_quad_to_mem q qd s
    | Ind2 r -> save_quad_to_mem (s.regs.(rind r)) qd s
    | Ind3 ((Lit q), r) -> save_quad_to_mem (Int64.add q (s.regs.(rind r))) qd s
    | _ -> failwith "Unimplemented operand pattern in put_quad"

let take_sbytes_from_mem (loc:quad) (n:int) (s:mach) : sbyte list =
  let rec take_sbytes_from_mem_helper (i:int) (loc:quad) (n:int) (s:mach) : sbyte list =
    match n with
      | 0 -> []
      | _ -> let mem_index = map_addr (Int64.add loc (Int64.of_int i)) in
              match mem_index with
                | None -> []
                | Some mem_index -> s.mem.(mem_index)::(take_sbytes_from_mem_helper (i+1) loc (n-1) s)
  in take_sbytes_from_mem_helper 0 loc n s

let take_quad_from_mem (loc:quad) (s:mach) : quad =
  int64_of_sbytes (take_sbytes_from_mem loc 8 s)

(* IN: Operand
   OUT: quad
   DESCRIPTION: Take a quad from an operand/location*)
let take_quad (op:operand) (s:mach) : quad =
  match op with
    | Imm (Lit q) -> q
    | Reg r -> s.regs.(rind r)
    | Ind1 (Lit q) -> take_quad_from_mem q s
    | Ind2 r -> take_quad_from_mem (s.regs.(rind r)) s
    | Ind3 ((Lit q), r) -> take_quad_from_mem (Int64.add q (s.regs.(rind r))) s
    | _ -> failwith "Unimplemented operand pattern in take_quad"

let sign_of_int64 (i:int64) : int64 = if i < 0L then 1L else 0L

(* IN: Operand, Quad, Quad, Quad, mach,
   OUT: unit
   DESCRIPTION: Set the condition flags according to the operation*)
let set_cndtn_flags (op:opcode) (a:quad) (b:quad) (res:quad) (m:mach) : unit =
  match op with
    | Negq -> m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- Int64.equal res Int64.min_int
    | Addq -> m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- (sign_of_int64 a == sign_of_int64 b) && (sign_of_int64 res <> sign_of_int64 a)
    | Subq -> m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- ((sign_of_int64 (Int64.mul Int64.minus_one a) == sign_of_int64 b) && (sign_of_int64 res <> sign_of_int64 (Int64.mul a Int64.minus_one))) || (Int64.equal a Int64.min_int)
    | Imulq -> m.flags.fs <- false;
               m.flags.fz <- false;
               m.flags.fo <- ((a <> 0L) && (Int64.div res a <> b)) || ((b <> 0L) && (Int64.div res b <> a))
    | Andq -> m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- false
    | Orq ->  m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- false
    | Xorq -> m.flags.fs <- res < 0L;
              m.flags.fz <- Int64.equal res 0L;
              m.flags.fo <- false
    | Sarq -> m.flags.fs <- if a == 0L then m.flags.fs else res < 0L;
              m.flags.fz <- if a == 0L then m.flags.fz else Int64.equal res 0L;
              m.flags.fo <- if a == 1L then false else m.flags.fo
    | Shlq -> m.flags.fs <- if a == 0L then m.flags.fs else res < 0L;
              m.flags.fz <- if a == 0L then m.flags.fz else Int64.equal res 0L;
              let shifted_dest = Int64.shift_right_logical b 62 in
                m.flags.fo <- if a == 1L then (Int64.equal shifted_dest 2L) || (Int64.equal shifted_dest 1L) else m.flags.fo
    | Shrq -> m.flags.fs <- if a == 0L then m.flags.fs else false;
              m.flags.fz <- if a == 0L then m.flags.fz else Int64.equal res 0L;
              m.flags.fo <- if a == 1L then b < 0L else m.flags.fo
    | _ -> failwith "Tried to set condition flags for non-supported operation"
    

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit = if m.regs.(rind Rip) == exit_addr then () else
  let instruction = 
    match (List.hd (take_sbytes_from_mem m.regs.(rind Rip) 8 m)) with
      | InsB0 inst -> inst
      | Byte _ -> failwith "Byte"
      | InsFrag -> failwith "Instruction Fragment"
    in 
      (* Increment Rip *)
      m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L;
      (* Execute instruction *)
      let operation = fst instruction in
        let operands = snd instruction in
          match operation with
            (*Data-movement instructions*)
            | Leaq -> (
                      let ind = List.hd operands in
                        let dst = List.hd (List.tl operands) in
                          match ind with
                            | Ind1 (Lit q) -> put_quad dst q m
                            | Ind2 r -> put_quad dst m.regs.(rind r) m
                            | Ind3 ((Lit q), r) -> put_quad dst (Int64.add q (m.regs.(rind r))) m
                            | _ -> ()
                      )
            | Movq -> let src = List.hd operands in
                        let dst = List.hd (List.tl operands) in
                          put_quad dst (take_quad src m) m
            | Pushq -> let src = List.hd operands in
                          m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
                          put_quad (Ind2 Rsp) (take_quad src m) m 
            | Popq -> let dst = List.hd operands in
                        put_quad dst (take_quad (Ind2 Rsp) m) m;
                        m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
            (*Control-flow instructions*)
            | Cmpq -> let src1 = List.hd operands in
                        let src2 = List.hd (List.tl operands) in
                          set_cndtn_flags Subq (take_quad src1 m) (take_quad src2 m) (Int64.sub (take_quad src2 m) (take_quad src1 m)) m
            | Jmp -> let src = List.hd operands in
                        m.regs.(rind Rip) <- take_quad src m
            | Callq -> let src = List.hd operands in
                        m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
                        put_quad (Ind2 Rsp) m.regs.(rind Rip) m;
                        m.regs.(rind Rip) <- take_quad src m
            | Retq -> m.regs.(rind Rip) <- take_quad (Ind2 Rsp) m;
                      m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
            | J cc -> let src = List.hd operands in
                        if interp_cnd m.flags cc then m.regs.(rind Rip) <- take_quad src m else ()
            (*Arithmetic instructions*)
            | Negq -> let dst = List.hd operands in
                        let res = Int64.mul (take_quad dst m) Int64.minus_one in
                          set_cndtn_flags Negq 0L 0L res m;
                          put_quad dst res m
            | Addq -> let src = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.add (take_quad dst m) (take_quad src m) in
                            set_cndtn_flags Addq (take_quad src m) (take_quad dst m) res m;
                            put_quad dst res m
            | Subq -> let src = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.sub (take_quad dst m) (take_quad src m) in
                            set_cndtn_flags Subq (take_quad src m) (take_quad dst m) res m;
                            put_quad dst res m
            | Imulq -> let src = (List.hd operands) in
                        let reg = (List.hd (List.tl operands)) in
                          let res = Int64.mul (take_quad reg m) (take_quad src m) in
                            set_cndtn_flags Imulq (take_quad src m) (take_quad reg m) res m;
                            put_quad reg res m
            | Incq -> let src = (List.hd operands) in
                        let res = Int64.add 1L (take_quad src m) in
                          set_cndtn_flags Addq (take_quad src m) 1L res m;
                          put_quad src res m
            | Decq -> let src = (List.hd operands) in
                        let res = Int64.sub (take_quad src m) 1L in
                          set_cndtn_flags Subq (take_quad src m) 1L res m;
                          put_quad src res m
            (*Logic Instructions*)
            | Notq -> let dst = (List.hd operands) in
                        let res = Int64.lognot (take_quad dst m) in
                          put_quad dst res m
            | Andq -> let src = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.logand (take_quad dst m) (take_quad src m) in
                            set_cndtn_flags Andq (take_quad src m) (take_quad dst m) res m;
                            put_quad dst res m
            | Orq -> let src = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.logor (take_quad dst m) (take_quad src m) in
                            set_cndtn_flags Orq (take_quad src m) (take_quad dst m) res m;
                            put_quad dst res m
            | Xorq -> let src = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.logxor (take_quad dst m) (take_quad src m) in
                            set_cndtn_flags Xorq (take_quad src m) (take_quad dst m) res m;
                            put_quad dst res m
            (*Bit-manipulation Instructions*)
            | Sarq -> let amt = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.shift_right (take_quad dst m) (Int64.to_int (take_quad amt m)) in
                            set_cndtn_flags Sarq (take_quad amt m) (take_quad dst m) res m;
                            put_quad dst res m
            | Shlq -> let amt = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.shift_left (take_quad dst m) (Int64.to_int (take_quad amt m)) in
                            set_cndtn_flags Shlq (take_quad amt m) (take_quad dst m) res m;
                            put_quad dst res m
            | Shrq -> let amt = (List.hd operands) in
                        let dst = (List.hd (List.tl operands)) in
                          let res = Int64.shift_right_logical (take_quad dst m) (Int64.to_int (take_quad amt m)) in
                            set_cndtn_flags Shrq (take_quad amt m) (take_quad dst m) res m;
                            put_quad dst res m
            | Set cc -> let dst = (List.hd operands) in
                          let lower_byte_mask = Int64.shift_left Int64.minus_one 8 in
                            let res = Int64.logand (take_quad dst m) lower_byte_mask in
                              if interp_cnd m.flags cc then put_quad dst (Int64.add res 1L) m else put_quad dst res m

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)

(* Helper function to determine the size of a labeled block of
   either text or data (selected using opt int) *)
let get_size (opt : int) (size : int64) (e : elem) : int64 =
  (* Data size is computed differently for different data types *)
  let data_size (d_size : int64) (d : data) : int64 =
    match d with
      | Asciz a -> Int64.add d_size @@ Int64.succ @@ (Int64.of_int (String.length a))
      | Quad (Lit i) -> Int64.add d_size 8L
      | _ -> size
    in
    (* text size is just 4 times the length of the ins list *)
    match opt, e.asm with
    | 0, Text t -> Int64.add size @@ Int64.of_int ((List.length t) * 8)
    | 1, Data d -> Int64.add size @@ List.fold_left data_size 0L d
    | _, _ -> size


(* Symbol table to keep track of all labels and their respective addresses *)
type sym_tab = lbl * quad


(* Find label to address mapping in symbol table, return address or
   if not present, then -1L or raise exception depending on opt *)
let rec find_label (st : sym_tab list) (l : lbl) (opt : int) : int64 =
  match st with
  | (a, b) :: tail -> if a = l then b else find_label tail l opt
  | [] -> if opt = 0 then (-1L) else raise (Undefined_sym l)


(* Translate the labels into the addresses that they will be found in *)
let translate_labels (opt : int) (st, addr_acc) (e : elem) : ((sym_tab list) * int64) =
  let data_size (d_size : int64) (d : data) : int64 =
    match d with
    | Asciz a -> Int64.add d_size @@ Int64.succ @@ Int64.of_int (String.length a)
    | Quad (Lit i) -> Int64.add d_size 8L
    | _ -> addr_acc
  in
    match opt, e.asm with
    | 0, Text t ->
        let new_acc = Int64.add addr_acc (Int64.of_int ((List.length t) * 8)) in
        let addr = find_label st e.lbl 0 in
          begin match addr with 
            | -1L -> List.append st [(e.lbl, addr_acc)], new_acc
            | _ -> raise (Redefined_sym e.lbl)
          end
    | 1, Data d ->
        let new_acc = Int64.add addr_acc (List.fold_left data_size 0L d) in
        let addr = find_label st e.lbl 0 in
          begin match addr with
            | -1L -> List.append st [(e.lbl, addr_acc)], new_acc
            | _ -> raise (Redefined_sym e.lbl)
          end
    | _, _ -> (st, addr_acc)


(* Top level replace function to be called in assemble function
   Replaces all labels in the text and data segment with their address *)
let replace (opt : int) (st : sym_tab list) (byte_list : sbyte list) (e : elem) :
  sbyte list =
  (* Helper function to replace labels in operands of instruction with their address *)
  let replace_operands (byte_list : sbyte list)
    ((opcode, operlst) : ins) : sbyte list =
    (* Helper-Helper function to replace labels in operands *)
    let rec replace_aux (operlst : operand list) : operand list =
      match operlst with
        | Imm (Lbl l) :: tail -> [Imm (Lit (find_label st l 1))] @ (replace_aux tail)
        | Ind1 (Lbl l) :: tail -> [Ind1 (Lit (find_label st l 1))] @ (replace_aux tail)
        | Ind3 ((Lbl l), r) :: tail -> [Ind3 ((Lit (find_label st l 1)), r)] @ (replace_aux tail)
        | [] -> []
        | r :: tail -> [r] @ (replace_aux tail)
    in
      List.append byte_list @@ sbytes_of_ins (opcode, (replace_aux operlst))
  in
  (* Helper function to replace labels in data with their address *)
  let replace_data (byte_list : sbyte list) (d : data) : sbyte list =
    match d with
    | Quad (Lit i) -> List.append byte_list (sbytes_of_data d)
    | Asciz s -> List.append byte_list (sbytes_of_data d)
    | Quad (Lbl l) -> List.append byte_list @@ sbytes_of_data @@ Quad (Lit (find_label st l 1))
  in
  (*  *)
  match opt, e.asm with
    | 0, Text t -> List.append byte_list @@ List.fold_left replace_operands [] t
    | 1, Data d -> List.append byte_list @@ List.fold_left replace_data [] d
    | _, _ -> byte_list


let assemble (p:prog) : exec =
  (* Get size of text and data segments *)
  let text_size = List.fold_left (get_size 0) 0L p in
  (* Create symbol table by scanning over text and data segment
     Since the text segment comes before the data segment in memory, start with text *)
  let (addr, size) = List.fold_left (translate_labels 0) ([], 0x400000L) p in
  let (addr2, size2) = List.fold_left (translate_labels 1) (addr, size) p in
  (* sbytes list of patched data and ins *)
  let text_segment = List.fold_left (replace 0 addr2) [] p in
  let data_segment = List.fold_left (replace 1 addr2) [] p
  in
    {
      entry = find_label addr "main" 1;
      text_pos = 0x400000L;
      data_pos = Int64.add 0x400000L text_size;
      text_seg = text_segment;
      data_seg = data_segment;
    }


(* Helper function to initialise an empty machine state *)
(*let init_mach : mach =
  let flags = {fo=false; fs=false; fz=false} in
  let regs = Array.make nregs 0L in
  let mem = Array.make mem_size 0L in
  let m = {flags; regs; mem} in
  m*)

  (* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let tmp_mem = Array.make 0xFFF8 InsFrag in
  let t_n_d_segs = Array.append (Array.of_list text_seg) (Array.of_list data_seg)
  in
    (Array.blit t_n_d_segs 0 tmp_mem 0 (Array.length t_n_d_segs);
    let exit_addr_array = Array.of_list (sbytes_of_int64 exit_addr) in
    let memory = Array.append tmp_mem exit_addr_array in
    (* Set all flags to false at initialisation *)
    let flgs = { fo = false; fs = false; fz = false; } in
    (* Create 17 registers, fill Rip and Rsp *)
    let registers = Array.make 17 0L
    in
      (Array.set registers (rind Rip) entry;
        Array.set registers (rind Rsp) 0x40FFF8L;
        { flags = flgs; regs = registers; mem = memory; }))
