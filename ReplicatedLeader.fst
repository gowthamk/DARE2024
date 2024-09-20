(*
 * One-shot leader election protocol written using an 
 * weakly-consistent replicated state abstraction instead
 * of explicit message passing. `is_safe` is still the safety
 * condition, but instead of proving it directly, we prove it
 * via convergence and monotonicity of leader decision (see vc1-4).
 * This approach does not require additional inductive invariant,
 * but it does require an update pre-condition (`update_pre`).
 *)

module ReplicatedLeader

module M = FStar.Map

module N = Node

module L = ListQ

type eff = 
  | Vote: Node.t -> Node.t -> eff

noeq type state = {vote_map: M.t Node.t (option Node.t)}

(*
 * Assume a node called self
 *)
assume val self: Node.t
(*
 * Assume a set of voters
 *)
assume val voters: list Node.t  
(*
 * Assume a function to determine quorums
 *)
assume val is_quorum : list Node.t -> bool
(*
 * Quorum intersection axiom
 *)
val axm_quorum_intersection: q1: list Node.t -> q2: list Node.t 
  -> Lemma (requires is_quorum q1 && is_quorum q2)
           (ensures (exists n. (*{:pattern (L.mem n q1); (L.mem n q2)} *)
                      L.mem n q1 /\ L.mem n q2))
           [SMTPat (is_quorum q1); 
            SMTPat (is_quorum q2)]
let axm_quorum_intersection q1 q2 = admit()

(*
 * Quorum monotonicity axiom. This cannot be proven just from quorum intersection since the lemma only goes one way.
 *)
val axm_quorum_monotonic: q1:list Node.t -> q2:list Node.t
  -> Lemma(requires (is_quorum q1) 
            /\ (forall x. (*{:pattern (L.mem n q1); (L.mem n q2)}*)
                  L.mem x q1 ==> L.mem x q2))
          (ensures is_quorum q2)
          [SMTPat (is_quorum q1);
           SMTPat (is_quorum q2)]
let axm_quorum_monotonic q1 q2 = admit()

(*
 * Initial state and its safety
 *)
let init_state = {vote_map = M.const None}

(*
 * Cast_vote is the operation that generates the Vote eff.
 *)
val cast_vote: state -> Node.t -> option eff
let cast_vote s cand = 
  let my_vote = M.sel s.vote_map self in
  match my_vote with
    | Some _ -> None
    | None -> Some (Vote self cand)

(*
 * handle_vote handles the Vote eff.
 *)
val handle_vote: state -> eff -> (option eff & state)
let handle_vote s (Vote n1 n2) = 
  let s' = {vote_map = M.upd s.vote_map n1 (Some n2)} in
  let eff = cast_vote s' n2 in
  (eff,s')

(*
 * is_elected s voters ldr returns true iff ldr has a 
 * quorum of votes in s. 
 *)
val is_elected: state -> Node.t -> bool
let is_elected s ldr = 
  let ldr_voters = L.filter 
                  (fun v -> M.sel s.vote_map v = Some ldr)
                  voters in
  is_quorum ldr_voters

(*
 * Z3 options
 *)
#set-options "--query_stats --split_queries always"
#set-options "--z3rlimit 10000"

(*
 * The monotonicity of leader election
 *)
val mono_ldr: state -> state -> Node.t -> prop
let mono_ldr s1 s2 ldr = 
  is_elected s1 ldr ==> is_elected s2 ldr

(*
 * The update precondition for every possible update.
 * We have just one possible update: Vote.
 *)
val update_pre: Node.t -> eff -> state -> bool
let update_pre n (Vote n1 n2) s =  
    n=n1 && (M.sel s.vote_map n = None)

(*
 * The first verification condition checks that the 
 * update precondition is indeed a pre-condition, i.e., 
 * update is generated only if it is satisfied.
 *)
val vc1: s:state -> n:Node.t -> eff:eff ->
  Lemma (requires cast_vote s n = Some eff)
        (ensures update_pre self eff s)
let vc1 s n eff = ()

(*
 * VC2 checks that an update applied in any state s1
 * satisfying the pre-condition will result in state s2
 * that preserves the monotonicity of leader election.
 *)
val vc2: s1:state -> n1:Node.t -> eff:eff 
  -> ldr:Node.t 
  ->  Lemma (requires update_pre n1 eff s1)
            (ensures 
              mono_ldr s1 ((handle_vote s1 eff)._2) ldr)
let vc2 s1 n1 eff dr = ()

(*
 * VC3 checks that update pre-condition is stable w.r.t 
 * concurrent effects. In particular, if state s1 satsifes 
 * the pre-condition of two effects, eff1 and eff2, from 
 * distinct origins (i.e., they are concurrent), then the 
 * state s2 resulting from applying eff2 to s1 will continue
 * satisfying the pre-condition of eff1. In other words, the 
 * concurrent effect eff2 is not blocking eff1 at a remote replica.
 * Note that vice-versa is also true due to symmetry.
 *)
val vc3: s1:state -> orig1:Node.t -> orig2:Node.t 
  -> eff1:eff -> eff2:eff
  -> Lemma (requires    update_pre orig1 eff1 s1
                     /\ update_pre orig2 eff2 s1
                     /\ orig1 <> orig2)
           (ensures update_pre orig1 eff1 (handle_vote s1 eff2)._2) 
let vc3 s1 orig1 orig2 eff1 eff2 = ()

(*
 * VC4 is the "CRDT VC": it checks that if effects eff1 and eff2
 * can be concurrent, i.e., their origins are different and there
 * exists a state s1 that satisfies both their pre-conditions,
 * then the order in which the effects are applied shouldn't matter.
 *)
val vc4: s1:state -> orig1:Node.t -> orig2:Node.t 
  -> eff1:eff -> eff2:eff
  -> Lemma (requires    update_pre orig1 eff1 s1
                     /\ update_pre orig2 eff2 s1
                     /\ orig1 <> orig2)
            (ensures 
              (let s12 = (handle_vote (handle_vote s1 eff1)._2 eff2)._2 in
               let s21 = (handle_vote (handle_vote s1 eff2)._2 eff1)._2 in
               M.equal s12.vote_map s21.vote_map))
let vc4 s1 orig1 orig2 eff1 eff2 = ()

(* Auxiliary VCs *)
(* Soundness requires our monotonicity relation (`mono_ldr`) 
 * to be reflexive and transitive, i.e., it must be a pre-order.
 * Ideally we have to check these properties too. I am eliding them here.)