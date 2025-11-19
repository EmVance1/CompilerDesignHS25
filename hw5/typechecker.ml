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
let rec subtype_ret (c : Tctxt.t) (rt1 : Ast.ret_ty) (rt2 : Ast.ret_ty) : bool =
  match (rt1, rt2) with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype c t1 t2
  | _, _ -> false

and subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match (t1, t2) with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TRef r1, TRef r2 -> subtype_ref c r1 r2
  | TRef r1, TNullRef r2 -> subtype_ref c r1 r2
  | TNullRef r1, TNullRef r2 -> subtype_ref c r1 r2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match (t1, t2) with
  | RString, RString -> true
  | RArray at1, RArray at2 -> at1 = at2
  | RStruct id1, RStruct id2 ->
    let fs1 = Tctxt.lookup_struct id1 c in
    let fs2 = Tctxt.lookup_struct id2 c in
    let rec check_fields f1 f2 =
      match (f1, f2) with
      | _, [] -> true
      | [], _ -> false
      | h1::t1, h2::t2 ->
        if h1.fieldName = h2.fieldName && h1.ftyp = h2.ftyp
        then check_fields t1 t2
        else false
    in
    check_fields fs1 fs2
  | RFun (args1, ret1), RFun (args2, ret2) ->
    if List.length args1 <> List.length args2 then false
    else
      let args_subtype =
        List.for_all2 (fun arg_sub arg_super -> subtype c arg_super arg_sub) args1 args2
      in
      let ret_subtype = subtype_ret c ret1 ret2 in
      args_subtype && ret_subtype
  | _ -> false


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
  | TInt -> ()
  | TBool -> ()
  | TRef r
  | TNullRef r -> typecheck_ref l tc r

and typecheck_ref (l : 'a Ast.node) (tc : Tctxt.t) (r : Ast.rty) : unit =
  match r with
  | RString -> ()
  | RArray at -> typecheck_ty l tc at
  | RStruct id ->
    (match Tctxt.lookup_struct_option id tc with
       | Some _ -> ()
       | None -> type_error l ("Unknown struct type: " ^ id))
  | RFun (args, ret) ->
    List.iter (typecheck_ty l tc) args;
    typecheck_ret_ty l tc ret

and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (rt : Ast.ret_ty) : unit =
  match rt with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l tc t


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
  | CNull r -> 
      typecheck_ref e c r; 
      TNullRef r
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Id id ->
    (match Tctxt.lookup_local_option id c with
    | Some ty -> ty
    | None -> 
      (match Tctxt.lookup_global_option id c with
       | Some ty -> ty
       | None -> type_error e ("Unknown identifier: " ^ id)))
  | CArr (ty, exprs) ->
      typecheck_ty e c ty;
      List.iter (fun ex ->
        let ex_ty = typecheck_exp c ex in
        if not (subtype c ex_ty ty)
          then type_error ex "Array element type mismatch") exprs;
        TRef (RArray ty)
  | NewArr (ty, len_exp, id, init_exp) ->
      typecheck_ty e c ty;
      let t_len = typecheck_exp c len_exp in
      if t_len <> TInt then type_error len_exp "Array length must be an integer";
      (match Tctxt.lookup_local_option id c with
      | Some _ -> type_error e ("Array initializer index " ^ id ^ " shadows a local variable")
      | None -> ());
      let c2 = Tctxt.add_local c id TInt in
      let t_init = typecheck_exp c2 init_exp in
      if not (subtype c t_init ty) then type_error init_exp "Array initializer type mismatch";
      TRef (RArray ty)
  | Length ex ->
      let t_ex = typecheck_exp c ex in
      (match t_ex with
      | TRef (RArray _) -> TInt
      | _ -> type_error ex "Length operation requires an array")
  | Index (arr_exp, idx_exp) ->
      let t_idx = typecheck_exp c idx_exp in
      if t_idx <> TInt then type_error idx_exp "Array index must be an integer";
      let t_arr = typecheck_exp c arr_exp in
      (match t_arr with
      | TRef (RArray at) -> at
      | _ -> type_error arr_exp "Indexing requires an array")
  | CStruct (id, fields) ->
      let struct_def =
        match Tctxt.lookup_struct_option id c with
        | Some fs -> fs
        | None -> type_error e ("Unknown struct type: " ^ id)
      in
      if List.length fields <> List.length struct_def then
        type_error e "Struct field count mismatch";
      let sorted_init = List.sort (fun (n1, _) (n2, _) -> String.compare n1 n2) fields in
      let sorted_def = List.sort (fun f1 f2 -> String.compare f1.fieldName f2.fieldName) struct_def in
      List.iter2 (fun (init_name, init_e) def_field ->
        if init_name <> def_field.fieldName then
          type_error e ("Struct field name mismatch: expected " ^ def_field.fieldName ^ " but got " ^ init_name);
        let t_init = typecheck_exp c init_e in
        if not (subtype c t_init def_field.ftyp) then
          type_error init_e ("Struct field type mismatch for field " ^ init_name)
      ) sorted_init sorted_def;
      TRef (RStruct id)
  | Proj (struct_exp, field_name) ->
      let t_struct = typecheck_exp c struct_exp in
      (match t_struct with
      | TRef (RStruct id) ->
          (match Tctxt.lookup_field_option id field_name c with
          | Some t -> t
          | None -> type_error e ("Unknown field " ^ field_name ^ " in struct " ^ id))
      | _ -> type_error struct_exp "Projection requires a struct type")
  | Call (fun_exp, args) ->
      let t_fun = typecheck_exp c fun_exp in
      (match t_fun with
      | TRef (RFun (param_tys, ret_ty)) ->
          if List.length param_tys <> List.length args then
            type_error e "Function argument count mismatch";
          List.iter2 (fun param_ty arg_exp ->
            let t_arg = typecheck_exp c arg_exp in
            if not (subtype c t_arg param_ty) then
              type_error arg_exp "Function argument type mismatch"
          ) param_tys args;
          (match ret_ty with
          | RetVoid -> type_error e "Void function cannot be used in an expression context"
          | RetVal t -> t)
      | _ -> type_error fun_exp "Call requires a function type")
  | Bop (Eq, e1, e2)
  | Bop (Neq, e1, e2) ->
      let t1 = typecheck_exp c e1 in
      let t2 = typecheck_exp c e2 in
      if (subtype c t1 t2) && (subtype c t2 t1) then TBool
      else type_error e "Inequality operands must be of compatible types"
  | Bop (op, e1, e2) ->
      let (ty1, ty2, ret_ty) = typ_of_binop op in
      let t1 = typecheck_exp c e1 in
      let t2 = typecheck_exp c e2 in
      if t1 = ty1 && t2 = ty2 then ret_ty
      else type_error e "Binary operation type mismatch"
  | Uop (op, ex) ->
      let (ty_in, ty_out) = typ_of_unop op in
      let t_ex = typecheck_exp c ex in
      if t_ex = ty_in then ty_out
      else type_error e "Unary operation type mismatch"

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
let check_lhs_assignable (tc : Tctxt.t) (lhs : Ast.exp node) : unit =
  match lhs.elt with
  | Id id ->
      (match Tctxt.lookup_local_option id tc with
       | Some _ -> ()
       | None ->
           (match Tctxt.lookup_global_option id tc with
            | Some t ->
                (match t with
                 | TRef (RFun _) -> type_error lhs ("Cannot assign to global function: " ^ id)
                 | _ -> ())
            | None -> type_error lhs ("Unknown identifier: " ^ id)))
  | _ -> ()

let rec typecheck_block (tc : Tctxt.t) (stmts : Ast.block) (rt : Ast.ret_ty) : bool =
  match stmts with
  | [] -> false
  | s :: rest ->
      let (tc', returns) = typecheck_stmt tc s rt in
      if returns then 
        match rest with
        | [] -> true
        | _ -> type_error s "Unreachable code: statement after a return" 
      else typecheck_block tc' rest rt

and typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  begin match s.elt with
  | Assn (lhs, rhs) -> 
      let t1 = typecheck_exp tc lhs in
      let t2 = typecheck_exp tc rhs in
      check_lhs_assignable tc lhs;
      if not (subtype tc t2 t1) then
        type_error s "Assignment type mismatch"
      else (tc, false)    
  | Decl (id, init) -> 
      (match Tctxt.lookup_local_option id tc with
      | Some _ -> type_error s ("Variable " ^ id ^ " redeclared in local scope")
      | None -> ());
      let t = typecheck_exp tc init in 
      (Tctxt.add_local tc id t, false)
  | Ret e_opt -> 
    (match to_ret, e_opt with
       | RetVoid, None -> (tc, true)
       | RetVal t_expect, Some ex ->
           let t_act = typecheck_exp tc ex in
           if not (subtype tc t_act t_expect) 
           then type_error s "Return value type mismatch"
           else (tc, true)
       | RetVoid, Some _ -> type_error s "Void function cannot return a value"
       | RetVal _, None -> type_error s "Function must return a value")
  | SCall (e, e_lst) -> 
      begin match typecheck_exp tc e with
      | TRef (RFun (ty_list, RetVoid)) 
      | TNullRef (RFun (ty_list, RetVoid)) ->
        if (List.length e_lst) <> (List.length ty_list) then 
          type_error s "Argument count mismatch"
        else
          let flag = List.for_all2 (fun ex t -> 
            let t_arg = typecheck_exp tc ex in
            subtype tc t_arg t
          ) e_lst ty_list in
          if not flag then
            type_error s "Argument type mismatch"
          else
            (tc, false) 
      | _ -> type_error s "Expression must be a function returning void"
      end
  | For (vd_lst, e_opt, stmt_opt, blk) -> 
      let (l2_ctxt, _) =
        List.fold_left 
          (fun (ctxt,_) vd -> 
            typecheck_stmt ctxt (no_loc (Decl vd)) to_ret) (tc, false) vd_lst in
      let e_bool = begin match e_opt with
        | Some s1 -> typecheck_exp l2_ctxt s1
        | None -> TBool
      end in
      begin match e_bool with
      | TBool -> 
          begin match stmt_opt with
          | Some s2 -> 
              let (_, returns) = typecheck_stmt l2_ctxt s2 to_ret in
              if returns then 
                type_error s2 "For-loop increment statement must not return"
              else ()
          | None -> ()
        end;
        let _ = typecheck_block l2_ctxt blk to_ret in
        (tc, false)
      | _ -> type_error s "Expression must be of type bool"
      end
  | While (e_n, blk) -> 
      begin match typecheck_exp tc e_n with
      | TBool ->
        let _ = typecheck_block tc blk to_ret in
        (tc, false)
      | _ -> type_error s "Expression must be of type bool"
      end
  | If (e_n, b1, b2) -> 
      begin match typecheck_exp tc e_n with
      | TBool ->
        let st_ty1 = typecheck_block tc b1 to_ret in
        let st_ty2 = typecheck_block tc b2 to_ret in
        begin match st_ty1, st_ty2 with
        | true, true -> (tc, true)
        | _ -> (tc, false)
        end
      | _ -> type_error s "Expression must be of type bool"
      end
  | Cast (rty, id, exp, b_then, b_else) ->
      let t_exp = typecheck_exp tc exp in
      (match t_exp with
       | TNullRef r | TRef r ->
           if not (subtype_ref tc r rty) 
           then type_error exp "Invalid reference downcast type";
           let tc_then = Tctxt.add_local tc id (TRef rty) in
           let ret1 = typecheck_block tc_then b_then to_ret in
           let ret2 = typecheck_block tc b_else to_ret in
           (tc, ret1 && ret2)
       | _ -> type_error exp "Null check requires a reference type")
  end



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
let check_dups_args (args : (Ast.ty * Ast.id) list) : bool =
  let rec check seen = function
    | [] -> false
    | (_, id) :: tl ->
        if List.exists (fun id' -> id = id') seen then true
        else check (id :: seen) tl
  in
  check [] args

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  if check_dups_args f.args then
    type_error l ("Duplicate argument names in function " ^ f.fname);
  let tc_local =
    List.fold_left (fun c (ty, id) ->
      typecheck_ty l c ty;
      Tctxt.add_local c id ty
    ) tc f.args
  in
  let returns = typecheck_block tc_local f.body f.frtyp in
  match f.frtyp with
  | RetVoid -> ()
  | RetVal t ->
      if not returns then
        type_error l ("Function " ^ f.fname ^ " might not return a value")



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
  let tc = Tctxt.empty in
  List.fold_left (fun acc_ctx p ->
    match p with
    | Gtdecl ({elt=(id, fs)} as l) ->
        (match Tctxt.lookup_struct_option id acc_ctx with
        | Some _ -> type_error l ("Duplicate struct declaration: " ^ id)
        | None ->
            if check_dups fs then
              type_error l ("Repeated fields in struct declaration: " ^ id)
            else
              Tctxt.add_struct acc_ctx id fs)
    | _ -> acc_ctx) tc p

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let tc_with_builtins = 
    List.fold_left (fun c (name, (arg_tys, ret_ty)) ->
      let fun_ty = TRef (RFun (arg_tys, ret_ty)) in
      Tctxt.add_global c name fun_ty
    ) tc builtins
  in
  List.fold_left (fun c d ->
    match d with
    | Gfdecl ({ elt=f } as l) ->
        if Tctxt.lookup_global_option f.fname c <> None then
          type_error l ("Duplicate function declaration: " ^ f.fname)
        else
          let arg_tys = List.map (fun (t, _) -> t) f.args in
          let fun_ty = TRef (RFun (arg_tys, f.frtyp)) in
          Tctxt.add_global c f.fname fun_ty
    | Gtdecl _ | Gvdecl _ -> c
  ) tc_with_builtins p


let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun c d ->
    match d with
    | Gvdecl ({elt=g} as l) ->
      (match Tctxt.lookup_global_option g.name c with
        | Some _ -> type_error l ("Global variable " ^ g.name ^ " is redefined")
        | None ->
            let t = typecheck_exp tc g.init in
            Tctxt.add_global c g.name t
      )
    | Gfdecl _ | Gtdecl _ -> c
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
