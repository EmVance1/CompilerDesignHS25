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
let interp_cnd {fo; fs; fz} : cnd -> bool = function
  | Eq  -> fz
  | Neq -> not fz
  | Gt  -> not fz && (fs = fo)
  | Ge  -> fs = fo
  | Lt  -> fs <> fo
  | Le  -> fz || (fs <> fo)
  (* fun x -> failwith "interp_cnd unimplemented" *)

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr < mem_bot || addr >= mem_top then
    None
  else
    let offset = Int64.sub addr mem_bot in
    Some (Int64.to_int offset)


let rec imm_valueof (imm:imm) : quad =
    match imm with
      | Lit l -> l
      | Lbl _ -> failwith "label is not a numerical value"


(* use to convert value-type operands to qwords *)
let eval_num_opnd (op:operand) (mach:mach) : quad = 
  match op with
    | Imm imm -> imm_valueof imm
    | Reg reg -> mach.regs.(rind reg)
    | Ind1 imm -> let addr = imm_valueof imm in
        let ptr = (match (map_addr addr) with
          | Some ptr -> ptr
          | None -> raise X86lite_segfault) in
            int64_of_sbytes (Array.to_list (Array.sub mach.mem ptr 8))
    | Ind2 reg -> let reg = mach.regs.(rind reg) in
        let ptr = (match (map_addr reg) with
          | Some ptr -> ptr
          | None -> raise X86lite_segfault) in
            int64_of_sbytes (Array.to_list (Array.sub mach.mem ptr 8))
    | Ind3 (imm, reg) -> let reg = mach.regs.(rind reg) in
        let addr = Int64.add reg (imm_valueof imm) in
        let ptr = (match (map_addr addr) with
          | Some ptr -> ptr
          | None -> raise X86lite_segfault) in
            int64_of_sbytes (Array.to_list (Array.sub mach.mem ptr 8))
    | _ -> failwith "operand was not a valid number"

(* use to convert address-type operands to qwords, unfinished *)
let eval_addr_opnd (op:operand) (mach:mach) : quad =
  match op with
    | Imm imm -> imm_valueof imm
    | Reg reg -> mach.regs.(rind reg)
    | Ind1 imm -> imm_valueof imm
    | Ind2 reg -> mach.regs.(rind reg)
    | Ind3 (imm, reg) ->
        let basic_addr = mach.regs.(rind reg) in
        let offset = imm_valueof imm in
        Int64.add basic_addr offset

    | _ -> failwith "operand was not an indirect address"


let arith_set_flags ((quad, fo):(quad * bool)) (flags:flags) : quad =
    flags.fz <- quad = 0L;
    flags.fs <- quad < 0L;
    flags.fo <- fo;
    quad;;

let rec mem_write_i64 (mem:mem) (idx:int) (value:sbyte list) : unit =
    match value with
      | [] -> ()
      | h::tl -> mem.(idx) <- h; mem_write_i64 mem (idx+1) tl

(* writes a computed result to its destination *)
let writeback (dest:operand) (value:quad) (mach:mach) : unit =
  match dest with
    | Imm _ -> failwith "cannot write to an immediate value"
    | Reg reg -> mach.regs.(rind reg) <- value
    | Ind1 imm -> failwith "unimplemented"
    | Ind2 reg -> (
        let reg = mach.regs.(rind reg) in
        let ptr = (match (map_addr reg) with
          | Some ptr -> ptr
          | None -> raise X86lite_segfault) in

          mem_write_i64 mach.mem ptr (sbytes_of_int64 value)
    )
    | Ind3 (imm, reg) -> (
        let reg = mach.regs.(rind reg) in
        let ptr = (match (map_addr reg) with
          | Some ptr -> ptr + (Int64.to_int (imm_valueof imm))
          | None -> raise X86lite_segfault) in

          mem_write_i64 mach.mem ptr (sbytes_of_int64 value)
    )


(*
let sign_bit (quad:quad) : quad = Int64.logand (Int64.shift_right quad 63) 1L

(* determines the status of the 'FO' register after an operation *)
let arith_sets_fo (ins:opcode) (s64:quad) (d64:quad) (r64:quad) (fo:bool) : bool =
  match ins with
    | Addq  -> sign_bit d64 = sign_bit s64 && sign_bit r64 <> sign_bit s64
    | Subq  -> (sign_bit d64 = sign_bit (Int64.neg s64) && sign_bit r64 <> sign_bit (Int64.neg s64)) || s64 = Int64.min_int
    | Imulq -> 
      let open Int64 in
      let r_sign = logand (shift_right r64 63) 1L in
      let d_sign = logand (shift_right d64 63) 1L in
      let s_sign = logand (shift_right s64 63) 1L in
      let expected_sign = logxor d_sign s_sign in
      r_sign <> expected_sign
    | Incq  -> sign_bit d64 = 0L && sign_bit r64 <> 0L
    | Decq  -> sign_bit d64 = 1L && sign_bit r64 <> 1L
    | Negq  -> d64 = Int64.min_int
    | Notq  -> fo
    | Xorq | Orq | Andq -> false
    | _ -> failwith "opcode is not an arithmetic/logic operation"
*)


(* determines the status of the 'FO' register after a shift operation *)
let shift_sets_fo (ins:opcode) (a32:int) (d64:quad) (fo:bool) : bool =
  if a32 <> 1 then fo else
  match ins with
    | Shlq -> false
    | Sarq ->
        let b1 = (Int64.logand (Int64.shift_right d64 62) 1L) in
        let b2 = (Int64.logand (Int64.shift_right d64 63) 1L) in
            b1 = b2
    | Shrq -> d64 < 0L
    | _ -> failwith "opcode is not an shift operation"


(* the function to be applied to operands for unary operations *)
let arith_func_unary (ins:opcode) (fo:bool) : quad -> Int64_overflow.t =
  match ins with
    | Incq  -> Int64_overflow.succ
    | Decq  -> Int64_overflow.pred
    | Negq  -> Int64_overflow.neg
    | Notq  -> fun v -> { value = if v = 0L then 1L else 0L; overflow = fo }
    | _ -> failwith "opcode is not an arithmetic/logic operation"

(* the function to be applied to operands for binary operations *)
let arith_func_binary (ins:opcode) : quad -> quad -> Int64_overflow.t =
  match ins with
    | Addq  -> Int64_overflow.add
    | Subq  -> fun x y -> Int64_overflow.sub y x
    | Imulq -> Int64_overflow.mul
    | Xorq  -> fun a b -> { value = Int64.logxor a b; overflow = false }
    | Orq   -> fun a b -> { value = Int64.logor  a b; overflow = false }
    | Andq  -> fun a b -> { value = Int64.logand a b; overflow = false }
    | _ -> failwith "opcode is not an arithmetic/logic operation"

(* the function to be applied to operands for shift operations *)
let arith_func_shift (ins:opcode) : quad -> int -> quad =
  match ins with
    | Shlq  -> Int64.shift_left
    | Sarq  -> Int64.shift_right
    | Shrq  -> Int64.shift_right_logical
    | _ -> failwith "opcode is not an shift operation"


let eval_instr ((ins, ops):(opcode * operand list)) (mach:mach) : unit =
  match ins with
    | Movq -> (
      match ops with
        | [src; dest] ->
            let s64 = eval_num_opnd src mach in
                writeback dest s64 mach
        | _ -> failwith "move instruction expects 1 src and 1 dest operand"
    )
    | Pushq -> (
      match ops with
        | [src] ->
            let s64  = eval_num_opnd src mach in
            let dec  = Int64.sub mach.regs.(rind Rsp) 8L in
            let dest = Ind2 Rsp in
                mach.regs.(rind Rsp) <- dec;
                writeback dest s64 mach
        | _ -> failwith "move instruction expects 1 src and 1 dest operand"
    )
    | Popq -> (
      match ops with
        | [dest] ->
            let src = Ind2 Rsp in
            let s64 = eval_num_opnd src mach in
            let inc = Int64.add mach.regs.(rind Rsp) 8L in
                mach.regs.(rind Rsp) <- inc;
                writeback dest s64 mach
        | _ -> failwith "move instruction expects 1 src and 1 dest operand"
    )
    | Leaq -> (
      match ops with
        | [ind; dest] ->
            let addr = eval_addr_opnd ind mach in
                writeback dest addr mach
        | _ -> failwith "leaq instruction expects 1 src and 1 dest operand"
    )
    | Incq | Decq | Negq | Notq -> (
      match ops with
        | [dest] ->
            let d64 = eval_num_opnd dest mach in
            let r64 = (arith_func_unary ins mach.flags.fo) d64 in
                writeback dest (arith_set_flags (r64.value, r64.overflow) mach.flags) mach
        | _ -> failwith "unary math instruction expects 1 operand"
    )
    | Addq | Subq | Imulq | Xorq | Orq | Andq -> (
      match ops with
        | [src; dest] ->
            let s64 = eval_num_opnd src mach in
            let d64 = eval_num_opnd dest mach in
            let r64 = (arith_func_binary ins) s64 d64 in
                writeback dest (arith_set_flags (r64.value, r64.overflow) mach.flags) mach
        | _ -> failwith "binary math instruction expects 2 operands"
    )
    | Shlq | Sarq | Shrq -> (
      match ops with
        | [amt; dest] ->
            let a32 = Int64.to_int (eval_num_opnd amt mach) in
            let d64 = eval_num_opnd dest mach in
            let sh = (arith_func_shift ins) d64 a32 in
            let fo  = shift_sets_fo ins a32 d64 mach.flags.fo in
                if a32 <> 0 then writeback dest (arith_set_flags (sh, fo) mach.flags) mach
        | _ -> failwith "shift instruction expects 1 amd and 1 dest operand"
    )
    | Jmp -> (
      match ops with
        | [src] ->
            let addr = eval_addr_opnd src mach in
            let rip  = rind Rip in
                mach.regs.(rip) <- addr
        | _ -> failwith "jmp instruction expects an address"
    )
    | J cnd -> (
      match ops with
        | [src] ->
            let addr = eval_addr_opnd src mach in
            let rip  = rind Rip in
            let op   = interp_cnd mach.flags in
                if (op cnd) then mach.regs.(rip) <- addr
        | _ -> failwith "jmp instruction expects an address"
    )
    | Cmpq -> (
      match ops with
        | [src; dest] ->
            let s64 = eval_num_opnd src mach in
            let d64 = eval_num_opnd dest mach in
            let r64 = Int64_overflow.sub d64 s64 in
                ignore (arith_set_flags (r64.value, r64.overflow) mach.flags)
        | _ -> failwith "cmp instruction expects 2 operands"
    )
    | Set cnd -> (
      match ops with
        | [dest] ->
            let op  = interp_cnd mach.flags in
            let v64 = if (op cnd) then 1L else 0L in
                writeback dest v64 mach
        | _ -> failwith "set instruction expects 1 operand"
    )
    | Callq -> (
      match ops with
        | [src] ->
            let addr = eval_addr_opnd src mach in
            let rip  = rind Rip in
            let ret  = Int64.add mach.regs.(rip) ins_size in
            let dest = Ind2 Rsp in
            let dec  = Int64.sub mach.regs.(rind Rsp) 8L in
                mach.regs.(rind Rsp) <- dec;
                writeback dest ret mach;
                mach.regs.(rip) <- addr
        | _ -> failwith "callq instruction expects an address"
    )
    | Retq -> (
        let src = Ind2 Rsp in
        let ret = eval_num_opnd src mach in
        let inc = Int64.add mach.regs.(rind Rsp) 8L in
            mach.regs.(rind Rsp) <- inc;
            mach.regs.(rind Rip) <- ret
    )
    | _ -> failwith "unknown instruction"

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step { flags: flags; regs: regs; mem: mem } : unit =
  let rip_val = regs.(rind Rip) in
  let mem_loc = (match (map_addr rip_val) with
    | Some loc -> loc
    | None -> raise X86lite_segfault) in
  let ins = mem.(mem_loc) in
    begin match ins with
      | InsB0 ins -> regs.(rind Rip) <- Int64.add rip_val 8L;
            eval_instr ins { flags=flags; regs=regs; mem=mem }
      | _ -> failwith "rip did not point to valid instruction"
    end

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

(* include null byte for strings *)
let data_length (d:data) : int =
    match d with
      | Asciz s -> String.length s + 1
      | Quad _  -> 8

type symbols = (lbl * quad) list

let collect_labels (p:prog) (off:quad) : symbols =
    let rec collect_impl prog acc n =
      begin match prog with
        | [] -> acc
        | h::tl -> (match h.asm with
                                               (* addr = sum prior + offset *)       (* sum prior = sum prior + datasize *)
          | Text t -> collect_impl tl ((h.lbl, Int64.add (Int64.of_int n) off)::acc) (n + (List.length t) * 8)
          | Data d -> collect_impl tl ((h.lbl, Int64.add (Int64.of_int n) off)::acc) (n + (List.fold_left (+) 0 (List.map data_length d)))
        )
      end in
        collect_impl p [] 0

let rec lookup_symbols (syms:symbols) (lbl:lbl) : quad =
    match syms with
      | [] -> raise (Undefined_sym lbl)
      | (l, addr)::tl -> if l = lbl then addr else lookup_symbols tl lbl

(* expand single basic block to sbyte list, symbol lookup provided *)
let asm_block (syms:(lbl -> quad)) (elem:elem) : sbyte list = failwith "unimplemented"


(* splits and orders text and data according to layout, computes starts, collects symbols, constructs exec record *)
let assemble (p:prog) : exec =
    let is_text a = match a.asm with
      | Text _ -> true
      | Data _ -> false
    in

    let text = (List.filter is_text p) in
    let data = (List.filter (fun x -> not (is_text x)) p) in
    let data_offset = Int64.add mem_bot (Int64.of_int (8 * List.length text)) in
    let symbols = lookup_symbols ((collect_labels text mem_bot) @ (collect_labels data data_offset)) in
        { entry = symbols "main";
          text_pos = mem_bot;
          data_pos = data_offset;
          (* map 'elem' list to 'sbyte list' list, fold-left-concatenate *)
          text_seg = List.fold_left (@) [] (List.map (asm_block symbols) text);
          data_seg = List.fold_left (@) [] (List.map (asm_block symbols) data);
        }

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
    let mem = Array.make 0x10000 (Byte '\x00') in
    let text = Array.of_list text_seg in
    let text_addr = (match map_addr text_pos with
        | Some addr -> addr
        | None -> raise X86lite_segfault) in
    Array.blit text 0 mem text_addr (Array.length text);
    let data = Array.of_list data_seg in
    let data_addr = (match map_addr data_pos with
        | Some addr -> addr
        | None -> raise X86lite_segfault) in
    Array.blit data 0 mem data_addr (Array.length data);
    let regs = Array.make 17 0L in
    regs.(rind Rip) <- entry;
    regs.(rind Rsp) <- Int64.sub mem_top 8L;
    mem_write_i64 mem (0x10000 - 8) (sbytes_of_int64 exit_addr);
        { flags={ fs=false; fz=false; fo=false }; regs=regs; mem=mem }

