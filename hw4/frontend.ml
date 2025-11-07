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

let has_terminator (s:stream) : bool =
  List.exists (function | T _ -> true | _ -> false) s

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CInt i -> (I64, Const i, [])
  | CBool b -> (I1, Const (if b then 1L else 0L), [])
  | CNull rty -> (cmp_ty (TRef rty), Null, [])

  | CStr s ->
      let gid = gensym "str" in
      let str_ty = Array (String.length s + 1, I8) in
      let str_gdecl = (str_ty, GString s) in
      
      let uid = gensym "str_ptr" in
      let ptr_ty = Ptr I8 in
      
      let stream =
        [ G (gid, str_gdecl)
        ; I (uid, Gep(Ptr str_ty, Gid gid, [Const 0L; Const 0L]))
        ]
      in
      (ptr_ty, Id uid, stream)
  
  | Id id ->
      let ptr_ty, addr_op = Ctxt.lookup id c in
      begin match ptr_ty with
      | Ptr (Fun (_, _)) ->
          (ptr_ty, addr_op, [])
      | Ptr ty ->
          let res_uid = gensym id in
          let stream = [I (res_uid, Load (ptr_ty, addr_op))] in
          (ty, Id res_uid, stream)
      | _ -> failwith "Id is not a pointer type in context"
      end

  | Bop (bop, e1, e2) ->
      let t1, _, t_out = typ_of_binop bop in
      let op_ty = cmp_ty t1 in
      let res_ty = cmp_ty t_out in

      let _, op1, code1 = cmp_exp c e1 in
      let _, op2, code2 = cmp_exp c e2 in

      let res_uid = gensym "bop" in
      let stream = code1 >@ code2 in

      begin match bop with
      | Add | Sub | Mul | IAnd | IOr | Shl | Shr | Sar ->
          let ll_bop = match bop with
            | Add -> Ll.Add | Sub -> Ll.Sub | Mul -> Ll.Mul
            | IAnd -> Ll.And | IOr -> Ll.Or | Shl -> Ll.Shl
            | Shr -> Ll.Lshr| Sar -> Ll.Ashr
            | _ -> failwith "impossible"
          in
          (res_ty, Id res_uid, stream >:: I (res_uid, Binop (ll_bop, op_ty, op1, op2)))

      | Eq | Neq | Lt | Lte | Gt | Gte ->
          let ll_cnd = match bop with
            | Eq -> Ll.Eq | Neq -> Ll.Ne | Lt -> Ll.Slt
            | Lte -> Ll.Sle | Gt -> Ll.Sgt | Gte -> Ll.Sge
            | _ -> failwith "impossible"
          in
          (res_ty, Id res_uid, stream >:: I (res_uid, Icmp (ll_cnd, op_ty, op1, op2)))

      | And | Or ->
          let ll_bop = match bop with
            | And -> Ll.And
            | Or -> Ll.Or
            | _ -> failwith "impossible"
          in
          (res_ty, Id res_uid, stream >:: I (res_uid, Binop (ll_bop, op_ty, op1, op2)))
      end

  | Uop (uop, e) ->
      let t_in, t_out = typ_of_unop uop in
      let op_ty = cmp_ty t_in in
      let res_ty = cmp_ty t_out in
      let _, op, code = cmp_exp c e in
      let res_uid = gensym "uop" in
      let stream = 
        match uop with
        | Neg -> code >:: I (res_uid, Binop (Sub, op_ty, Const 0L, op))
        | Lognot -> code >:: I (res_uid, Binop (Xor, op_ty, op, Const 1L))
        | Bitnot -> code >:: I (res_uid, Binop (Xor, op_ty, op, Const (-1L)))
      in
      (res_ty, Id res_uid, stream)

  | Call (f_exp, args) ->
      let f_ptr_ty, f_op, f_code = cmp_exp c f_exp in
      let f_ty = match f_ptr_ty with
        | Ptr t -> t
        | _ -> failwith "Call on non-function-pointer type" in
        
      let arg_tys, ret_ty = match f_ty with
        | Fun (args, ret) -> (args, ret)
        | _ -> failwith "Call on non-function type" in

      let codes, args_with_tys =
        List.fold_right (fun (arg_exp, arg_ty) (codes, args) ->
          let _, arg_op, arg_code = cmp_exp c arg_exp in
          (arg_code @ codes, (arg_ty, arg_op) :: args)
        ) (List.combine args arg_tys) ([], [])
      in
      
      let res_uid = gensym "call" in
      let stream = f_code >@ codes >:: I (res_uid, Call (ret_ty, f_op, args_with_tys)) in
      (ret_ty, Id res_uid, stream)

  | CArr (ty, exp_node_list) ->
    let arr_len = (Ll.Const (Int64.of_int (List.length exp_node_list))) in
    let arr_ty, arr_op, arr_strm = oat_alloc_array ty arr_len in
    let streams, _ = List.fold_left (fun (s,i) el ->
        let index_op = Ll.Const (Int64.of_int (i)) in
        let el_ty, el_op, el_st = cmp_exp c el in
        let arr_el_id = gensym "arr_el_gep" in 
        let strm = el_st 
        >@ [I (arr_el_id, Ll.Gep (arr_ty, arr_op, [Ll.Const (0L); Ll.Const (1L); index_op]))]
        >@ [I (arr_el_id, Ll.Store (el_ty, el_op, Ll.Id arr_el_id))] in
        (s >@ strm, i + 1)
      ) (arr_strm, 0) exp_node_list in
    (arr_ty, arr_op, streams)

  | NewArr (ty, len_exp) ->
      let _, len_op, len_code = cmp_exp c len_exp in
      
      let alloc_fn_op = Gid "oat_alloc_array" in
      let return_ty_from_alloc = Ptr I64 in

      let raw_ptr_uid = gensym "raw_arr" in
      let arr_ptr_uid = gensym "arr_ptr" in
      let final_arr_ptr_ty = cmp_ty (TRef (RArray ty)) in
      
      let stream =
        len_code
        >@ [
             I (raw_ptr_uid, Call (return_ty_from_alloc, alloc_fn_op, [(I64, len_op)]))
           ; I (arr_ptr_uid, Bitcast (return_ty_from_alloc, Id raw_ptr_uid, final_arr_ptr_ty))
           ]
      in
      (final_arr_ptr_ty, Id arr_ptr_uid, stream)

  | Index (arr_exp, idx_exp) ->
      let (elem_ty, addr_op), addr_code = cmp_lhs c exp in
      
      let res_uid = gensym "index_val" in
      
      let addr_ty = Ptr elem_ty in
      let load_ins = I (res_uid, Load (addr_ty, addr_op)) in
      
      (elem_ty, Id res_uid, addr_code >@ [load_ins])


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
 and cmp_lhs (c:Ctxt.t) (exp:Ast.exp node) : (Ll.ty * Ll.operand) * stream =
  match exp.elt with
  | Id id ->
      let ty, op = Ctxt.lookup id c in
      begin match ty with
      | Ptr t -> ((t, op), [])
      | _ -> failwith "cmp_lhs: Id is not a pointer"
      end

  | Index (arr_exp, idx_exp) ->
      let arr_ptr_ty, arr_op, arr_code = cmp_exp c arr_exp in
      
      let arr_ty = match arr_ptr_ty with
        | Ptr t -> t
        | _ -> failwith "Indexing on a non-pointer type"
      in
      let elem_ty = match arr_ty with
        | Struct [_; Array (_, t)] -> t
        | _ -> failwith "Indexing on a non-array-struct type"
      in
      let _, idx_op, idx_code = cmp_exp c idx_exp in
      let res_uid = gensym "elem_ptr" in
      
      let gep_ins = I (res_uid, Gep (arr_ptr_ty, arr_op, [Const 0L; Const 1L; idx_op])) in
      let stream = arr_code >@ idx_code >@ [gep_ins] in
      
      ((elem_ty, Id res_uid), stream)

  | _ -> failwith "Invalid LHS expression"

and cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Ret None ->
      (c, [T (Ret (Void, None))])

  | Ret (Some e) ->
      let ty, op, code = cmp_exp c e in
      let stream = code >:: T (Ret (ty, Some op)) in
      (c, stream)

  | Decl (id, init_exp) ->
      let ll_ty, op, init_code = cmp_exp c init_exp in
      let slot_id = gensym id in
      let alloca_ins = E (slot_id, Alloca ll_ty) in
      let store_ins = I (gensym "store", Store (ll_ty, op, Id slot_id)) in
      let new_c = Ctxt.add c id (Ptr ll_ty, Id slot_id) in
      let stream = init_code >@ [alloca_ins; store_ins] in
      (new_c, stream)

  | Assn (lhs_exp, rhs_exp) ->
      let val_ty, val_op, rhs_code = cmp_exp c rhs_exp in
      let (addr_ty, addr_op), lhs_code = cmp_lhs c lhs_exp in
      let store_ins = I (gensym "store", Store (val_ty, val_op, addr_op)) in
      let stream = rhs_code >@ lhs_code >:: store_ins in
      (c, stream)

  | If (cond, then_block, else_block) ->
    let t, cond_op, cond_code = cmp_exp c cond in
    let cmp_then_block = cmp_block c rt then_block in
    let cmp_else_block = cmp_block c rt else_block in
    let l1 = gensym "en" in
    let l2 = gensym "else" in
    let l3 = gensym "end_if" in
    let new_op, load_strm =
      match t with
      | I1 -> (cond_op, cond_code)
      | _ ->
          let new_uid = gensym "cond_bool" in
          let load_ins = I (new_uid, Icmp (Ne, t, cond_op, Const 0L)) in
          (Id new_uid, cond_code >:: load_ins)
    in
    let strm = cond_code 
      >@ [T (Cbr (new_op, l1, l2))]
      >@ [L l1] 
      >@ snd cmp_then_block 
      >@ [T (Br l3)]
      >@ [L l2] 
      >@ snd cmp_else_block 
      >@ [T (Br l3)]
      >@ [L l3]
    in
    (c, strm)

  | While (cond, body_block) ->
    let header_lbl = gensym "while_header" in
    let body_lbl = gensym "while_body" in
    let exit_lbl = gensym "while_exit" in

    let _, body_code = cmp_block c rt body_block in
    let body_stream = body_code >@ [T (Br header_lbl)] in

    let _, cond_op, cond_code = cmp_exp c cond in
    let header_stream = cond_code >@ [T (Cbr (cond_op, body_lbl, exit_lbl))] in
    
    let stream =
      [T (Br header_lbl)]
      >@ [L header_lbl] >@ header_stream
      >@ [L body_lbl] >@ body_stream
      >@ [L exit_lbl]
    in
    (c, stream)

  | SCall (f, args) ->
      let _, _, code = cmp_exp c (no_loc (Call (f, args))) in
      (c, code)

  | For (decls, cond, post, body) ->
      let c_after_decls, decl_code =
        List.fold_left (fun (c_acc, code_acc) decl ->
          let new_c, new_code = cmp_stmt c_acc rt (no_loc (Decl decl)) in
          (new_c, code_acc >@ new_code)
        ) (c, []) decls
      in
      let while_cond = Option.value cond ~default:(no_loc (CBool true)) in
      let while_body = body @ (Option.to_list post) in
      let while_stmt = no_loc (While (while_cond, while_body)) in
      let _, while_code = cmp_stmt c_after_decls rt while_stmt in
      
      (c, decl_code >@ while_code)

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
let type_of_gexp (e: Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull rty -> TRef rty
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | CArr (ty, _) -> TRef (RArray ty)
  | _ -> failwith "Invalid global initializer"

let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c_acc decl ->
    match decl with
    | Ast.Gvdecl { elt = { name; init } } ->
        let oat_ty = type_of_gexp init in
        let ll_ty = Ptr (cmp_ty oat_ty) in
        let operand = Gid name in
        Ctxt.add c_acc name (ll_ty, operand)
    | Ast.Gfdecl _ ->
        c_acc
  ) c p


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
  let { frtyp; args; body } = f.elt in
  let f_ty = cmp_fty (List.map fst args, frtyp) in
  let ret_ty = cmp_ret_ty frtyp in
  let oat_param_tys, oat_param_ids = List.split args in
  let ll_param_ids = List.map (fun id -> gensym id) oat_param_ids in
  let c_with_args, param_setup_stream =
    List.fold_left2
      (fun (c_acc, code_stream_acc) (oat_ty, oat_id) ll_id ->
        let ll_ty = cmp_ty oat_ty in
        let slot_id = gensym oat_id in
        let new_c = Ctxt.add c_acc oat_id (Ptr ll_ty, Id slot_id) in
        let param_code =
          [ E (slot_id, Alloca ll_ty)
          ; I (gensym "store", Store (ll_ty, Id ll_id, Id slot_id)) ]
        in
        (new_c, code_stream_acc >@ param_code)
      )
      (c, [])
      (List.combine oat_param_tys oat_param_ids)
      ll_param_ids
  in
  let _, body_code = cmp_block c_with_args ret_ty body in
  let default_op =
    match ret_ty with
    | Ptr _ -> Null
    | _ -> Const 0L
  in
  let terminator =
    T (match ret_ty with
      | Void -> Ret (Void, None)
      | _ -> Ret (ret_ty, Some default_op)
    )

  in
  let final_stream = param_setup_stream >@ body_code >:: terminator in
  let f_cfg, hoisted_globals = cfg_of_stream final_stream in
  let fdecl = {
    f_ty = f_ty;
    f_param = ll_param_ids;
    f_cfg = f_cfg
  } in
  (fdecl, hoisted_globals)

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
  | CInt i ->
      ((I64, GInt i), [])
  | CBool b ->
      let v = if b then 1L else 0L in
      ((I1, GInt v), [])
  | CNull rty ->
      let ll_ty = cmp_ty (TRef rty) in
      ((ll_ty, GNull), [])

  | CStr s ->
      let str_gid = gensym "str" in
      let str_len = String.length s + 1 in 
      let str_ty = Array (str_len, I8) in
      let str_gdecl = (str_ty, GString s) in
      let ptr_to_str_arr_ty = Ptr str_ty in
      let i8_ptr_ty = Ptr I8 in
      let init_val = GBitcast (ptr_to_str_arr_ty, GGid str_gid, i8_ptr_ty) in
      ((i8_ptr_ty, init_val), [ (str_gid, str_gdecl) ])

  | CArr (ty, es) ->
      let ll_ty = cmp_ty ty in
      let len = List.length es in
      let (ginits, aux_gdecls) =
        List.fold_right (fun e (gs, decls) ->
          let (gdecl, new_decls) = cmp_gexp c e in
          let (_, ginit) = gdecl in
          (ginit :: gs, new_decls @ decls)
        ) es ([], [])
      in
      let arr_data_gid = gensym "global_arr_data" in
      let concrete_arr_ty = Struct [I64; Array (len, ll_ty)] in
      let concrete_arr_ginit =
        GStruct [
          (I64, GInt (Int64.of_int len));
          (Array (len, ll_ty), GArray (List.map (fun g -> (ll_ty, g)) ginits))
        ]
      in
      let arr_data_gdecl = (concrete_arr_ty, concrete_arr_ginit) in
      let generic_ptr_ty = cmp_ty (TRef (RArray ty)) in
      let ptr_to_concrete_ty = Ptr concrete_arr_ty in
      let public_ginit = GBitcast (ptr_to_concrete_ty, GGid arr_data_gid, generic_ptr_ty) in
      let public_gdecl = (generic_ptr_ty, public_ginit) in
      (public_gdecl, (arr_data_gid, arr_data_gdecl) :: aux_gdecls)

  | _ -> failwith "Invalid global initializer as per OAT specification"




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
