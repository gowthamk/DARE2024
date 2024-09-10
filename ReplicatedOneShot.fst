module ReplicatedOneShot

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
 * is_elected s voters ldr returns true iff ldr has a quorum of votes in s. 
 *)
val is_elected: state -> Node.t -> bool
let is_elected s ldr = 
  let ldr_voters = L.filter 
                  (fun v -> M.sel s.vote_map v = Some ldr)
                  voters in
  is_quorum ldr_voters

#set-options "--query_stats --split_queries always"
#set-options "--z3rlimit 10000"

val mono_ldr: state -> state -> Node.t -> prop
let mono_ldr s1 s2 ldr = 
  is_elected s1 ldr ==> is_elected s2 ldr

val update_pre: Node.t -> eff -> state -> bool
let update_pre n (Vote n1 n2) s =  
    n=n1 && (M.sel s.vote_map n = None)

val vc1: s:state -> n:Node.t -> eff:eff ->
  Lemma (requires cast_vote s n = Some eff)
        (ensures update_pre self eff s)
let vc1 s n eff = ()

val vc2: s1:state -> n1:Node.t -> n2:Node.t -> n3:Node.t 
  -> ldr:Node.t 
  ->  Lemma (requires update_pre n1 (Vote n2 n3) s1)
            (ensures 
              mono_ldr s1 ((handle_vote s1 (Vote n2 n3))._2) ldr)
let vc2 s1 n1 n2 n3 ldr = ()

val vc3: s1: 