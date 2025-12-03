(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let is_alive (lb:uid -> Liveness.Fact.t) (ab:uid -> Alias.fact) : (uid * insn) -> bool = function
  | _, Call _ -> true
  | u, Store(_, _, op) -> (match op with
    | Id id  -> (
      let live   = UidS.mem id @@ lb u in
      let al_opt = UidM.find_opt id @@ ab u in
      let alias  = (match al_opt with
        | Some p -> p = Alias.SymPtr.MayAlias
        | None -> false) in
        live || alias
    )
    | _ -> false
  )
  | u, _ -> UidS.mem u @@ lb u
  

let dce_block (lb:uid -> Liveness.Fact.t) (ab:uid -> Alias.fact) (b:Ll.block) : Ll.block =
  { insns=List.filter (is_alive lb ab) b.insns; term=b.term }


let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

