open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let bop_fn = function
  | Add  -> Int64.add
  | Sub  -> Int64.sub
  | Mul  -> Int64.mul
  | Shl  -> fun a b -> Int64.shift_left a (Int64.to_int b)
  | Lshr -> fun a b -> Int64.shift_right_logical a (Int64.to_int b)
  | Ashr -> fun a b -> Int64.shift_right a (Int64.to_int b)
  | And  -> Int64.logand
  | Or   -> Int64.logor
  | Xor  -> Int64.logxor

let cmp_fn = function
  | Eq  -> fun a b -> if Int64.equal a b then 1L else 0L
  | Ne  -> fun a b -> if not @@ Int64.equal a b then 1L else 0L
  | Slt -> fun a b -> if Int64.compare a b <  0 then 1L else 0L
  | Sle -> fun a b -> if Int64.compare a b <= 0 then 1L else 0L
  | Sgt -> fun a b -> if Int64.compare a b >  0 then 1L else 0L
  | Sge -> fun a b -> if Int64.compare a b >= 0 then 1L else 0L


let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let get_sym = function
    | Gid id -> UidM.find_or SymConst.UndefConst d id
    | Id  id -> UidM.find_or SymConst.UndefConst d id
    | Const i -> SymConst.Const i
    | Null    -> SymConst.Const 0L in

  let get_vals a b bin = (match a, b with
    | SymConst.Const c1, SymConst.Const c2 -> SymConst.Const (bin c1 c2)
    | SymConst.UndefConst, _ -> SymConst.UndefConst
    | SymConst.NonConst,   _ -> SymConst.NonConst
    | _, SymConst.UndefConst -> SymConst.UndefConst
    | _, SymConst.NonConst   -> SymConst.NonConst) in

  match i with
    | Ll.Binop(bop, _, op1, op2) -> (
      let c1 = get_sym op1 in
      let c2 = get_sym op2 in
        UidM.add u (get_vals c1 c2 (bop_fn bop)) d
    )
    | Ll.Icmp(cnd, _, op1, op2) -> (
      let c1 = get_sym op1 in
      let c2 = get_sym op2 in
        UidM.add u (get_vals c1 c2 (cmp_fn cnd)) d
    )
    | Ll.Call(Void, _, _) | Ll.Store _ -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d


(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let join = UidM.merge (fun _ a b ->
      match a, b with
        | Some a, Some b -> Some (match a, b with
          | SymConst.Const a, SymConst.Const b -> if a = b then SymConst.Const a else SymConst.NonConst
          | SymConst.NonConst, _ -> SymConst.NonConst
          | _, SymConst.NonConst -> SymConst.NonConst
          | _ -> SymConst.UndefConst
        )
        | Some a, None   -> Some a
        | None, Some b   -> Some b
        | None, None     -> None)

    let combine (ds:fact list) : fact =
      List.fold_left join (UidM.empty) ds

  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let prop (cb:uid -> fact) (t:uid) (op:operand) : operand = match op with
  | Id id -> (
    let con = UidM.find_or SymConst.NonConst (cb t) id in
    match con with
      | SymConst.Const i -> Const i
      | _ -> op
  )
  | Gid id -> (
    let con = UidM.find_or SymConst.NonConst (cb t) id in
    match con with
      | SymConst.Const i -> Const i
      | _ -> op
  )
  | op -> op

let prop_insn (cb:uid -> fact) : (uid * insn) -> (uid * insn) = function
  | u, Binop(bop, ty, op1, op2) -> u, Binop(bop, ty, prop cb u op1, prop cb u op2)
  | u, Load(ty, op)             -> u, Load(ty, prop cb u op)
  | u, Store(ty, v, dest)       -> u, Store(ty, prop cb u v, dest)
  | u, Icmp(cnd, ty, op1, op2)  -> u, Icmp(cnd, ty, prop cb u op1, prop cb u op2)
  | u, Call(ty, op, args)       -> u, Call(ty, op, List.map (fun (ty, op) -> ty, prop cb u op) args)
  | u, Bitcast(t1, op, t2)      -> u, Bitcast(t1, prop cb u op, t2)
  | u, Gep(ty, op, args)        -> u, Gep(ty, op, List.map (prop cb u) args)
  | u, i -> u, i

let prop_term (cb:uid -> fact) : (gid * terminator) -> (gid * terminator) = function
  | g, Ret (ty, op) -> (match op with
    | Some op -> g, Ret(ty, Some(prop cb g op))
    | None    -> g, Ret(ty, None)
  )
  | g, Cbr (op, l1, l2) -> g, Cbr(prop cb g op, l1, l2)
  | g, i -> g, i


let prop_block (cb:uid -> fact) (b:Ll.block) : Ll.block =
  { insns=List.map (prop_insn cb) b.insns; term=prop_term cb b.term }


let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in

    (* compute constants at each program point for the block *)
    let cb = Graph.uid_out cg l in

    (* compute optimized block *)
    let b' = prop_block cb b in
    Cfg.add_block l b' cfg
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
