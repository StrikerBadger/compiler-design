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
(* eq -> fz=1, neq -> fz!=1, lt -> (fs=1 and fo=0) or (fs=0 and fo=1), le -> lt or eq, gt -> not le
   ge -> not lt*)
let interp_cnd {fo; fs; fz} : cnd -> bool =
  let rec interp_aux code = 
    begin match code with
      | Eq -> fz
      | Neq -> not fz
      | Gt -> not (interp_aux Le)
      | Ge -> not (interp_aux Lt)
      | Lt -> fs <> fo
      | Le -> (interp_aux Lt) || (interp_aux Eq)
    end
  in interp_aux

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if (addr < mem_bot) || (addr > mem_top) then None
  else Some ((Int64.to_int addr) - (Int64.to_int mem_bot))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let step_ins_decode (i:sbyte) : (X86.ins) =
  begin match i with
    | InsB0 (ins, operands) -> (ins, operands)
    | _ -> failwith "instruction decode wrong"
  end


let step (m:mach) : unit =
  let rip = Int64.to_int (m.regs.(rind Rip)) in (* rip is index (for mem array) to indicate where the next instr is *)
  (* get opcode and operands of instruction *)
  let (op, operands) = step_ins_decode m.mem.(rip) in
  (* helper function to read register contents *)
  let get_reg_val (r:reg) : int64 = m.regs.(rind r) in
  (* helper function to set register contents *)
  let set_reg_val (r:reg) (value:int64) : unit = m.regs.(rind r) <- value in
  (* helper function to check sign bit of an int64 *)
  let sign_bit n = Int64.(n < 0L) in

  (* helper function to read from memory *)
  let read_memory address size =
    (* bounds checking and raise X86lite_segfault if needed *)
    match map_addr address with
    | Some index ->
      (* read 'size' bytes from memory starting at the given index *)
      let bytes = Array.sub m.mem index size in
      int64_of_sbytes (Array.to_list bytes)
    | None -> raise X86lite_segfault
  in

  (* helper function to write to memory *)
  let write_memory address value size =
    (* bounds checking and raise X86lite_segfault if needed *)
    match map_addr address with
    | Some index ->
      (* Serialize the value into 'size' bytes and write to memory starting at the index *)
      let bytes = sbytes_of_int64 value in
      Array.blit (Array.of_list bytes) 0 m.mem index size
    | None -> raise X86lite_segfault
  in

  let get_operand_val = function
    | Imm (Lit i) -> i
    | Imm (Lbl _) -> failwith "Labels not supported as immediate operands during execution"
    | Reg r -> get_reg_val r
    | Ind1 (Lit i) -> read_memory i 8
    | Ind1 (Lbl _) -> failwith "Labels not supported in indirect addressing during execution"
    | Ind2 r -> read_memory (get_reg_val r) 8
    | Ind3 (Lit i, r) -> read_memory (Int64.add i (get_reg_val r)) 8
    | Ind3 (Lbl _, _) -> failwith "Labels not supported in indirect addressing during execution"
  in

  let set_operand_val oper value = match oper with
    | Reg r -> set_reg_val r value
    | Ind1 (Lit i) -> write_memory i value 8
    | Ind1 (Lbl _) -> failwith "Labels not supported in indirect addressing during execution"
    | Ind2 r -> write_memory (get_reg_val r) value 8
    | Ind3 (Lit i, r) -> write_memory (Int64.add i (get_reg_val r)) value 8
    | Ind3 (Lbl _, _) -> failwith "Labels not supported in indirect addressing during execution"
    | Imm _ -> failwith "Cannot write to immediate operand"
  in
 
  let update_flags v1 v2 res = 
    m.flags.fo <- (sign_bit v1 = sign_bit v2) && (sign_bit v1 <> sign_bit res);
    m.flags.fs <- sign_bit res;
    m.flags.fz <- res = 0L;
  in

  let binop f = match operands with
    | [src; dst] -> 
      let v1 = get_operand_val src in
      let v2 = get_operand_val dst in
      let res = f v2 v1 in
      update_flags v1 v2 res;
      set_operand_val dst res
    | _ -> failwith "Invalid operands for binary operation"
  in
  
  let unop f = match operands with
    | [src] ->
      let v = get_operand_val src in
      let res = f v in
      (* update flags manually *)
      set_operand_val src res
    | _ -> failwith "Invalid operands for unary operation"

  (match op with
  | Movq -> 
    begin
      match operands with
      | [src; dst] -> 
        let value = get_operand_val src in
        set_operand_val dst value
      | _ -> failwith "Invalid operands for Movq"
    end
  | Pushq ->
    begin match operands with
      | [src] ->
        let value = get_operand_val src in
        let rsp = get_reg_val Rsp in
        let new_rsp = Int64.sub rsp 8L in
        set_reg_val Rsp (new_rsp);
        write_memory (new_rsp) src 8
      | _ -> failwith "Invalid operands for Pushq"
    end
  | Popq ->
    begin match operands with
      | [dst] ->
        let value = get_operand_val dst in
        let rsp = get_reg_val Rsp in
        let new_rsp = Int64.add rsp 8L in
        let mem_val = read_memory new_rsp 8 in
        set_reg_val Rsp (new_rsp);
        set_reg_val dst mem_val
      | _ -> failwith "Invalid operands for Popq"
    end
  | Leaq -> 
    begin match operands with
      | [Ind1 (Lit i); dst] -> set_reg_val dst i
      | [Ind1 (Lbl _); _] -> failwith "Labels not supported in indirect addressing during execution"
      | [Ind2 r; dst] -> set_reg_val dst (get_reg_val r)
      | [Ind3 (Lit i, r); dst] -> set_reg_val dst (Int64.add i (get_reg_val r))
      | [Ind3 (Lbl _, _); _] -> failwith "Labels not supported in indirect addressing during execution"
    end
  | Incq -> unop Int64.succ
  | Decq -> unop Int64.pred
  | Negq -> unop Int64.neg
  | Notq -> unop Int64.lognot
  | Addq -> binop Int64.add
  | Subq -> binop Int64.sub
  | Andq -> binop Int64.logand
  | Orq  -> binop Int64.logor
  | Xorq -> binop Int64.logxor
  | Imulq -> binop Int64.mul
  | _ -> failwith "end of match block");
  
  set_reg_val Rip (Int64.add (get_reg_val Rip) 8L)


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
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

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
failwith "load unimplemented"
