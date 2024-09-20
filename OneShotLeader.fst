(*
 * This module describes one-shot leader election protocol.
 * This is a simplified version of Paxos with only one round. 
 * It relies on asynchronous message passing. Prop `is_safe`
 * is the safety condition. Props `inv2-7` are needed to
 * discharge the safety proof.
 *)

module OneShotLeader

module M = FStar.Map

module S = FStar.Set

module L = ListQ

type msg = 
  | Vote: Node.t -> Node.t -> msg
  | Leader: Node.t -> msg

(*
 * M.sel s.leader A = None
 *)

noeq type state = {leader: M.t Node.t (option Node.t);
                    (* In any state s, s.leader[A] is who A thinks is the
                    leader *)
                   voted: M.t Node.t bool;
                   (* In any state s, s.voted[A] = true <=> A has already voted.
                    *)
                   votes: M.t Node.t (list Node.t);
                   (*
                     In any state s, s.votes[A] is the set of nodes who
                     voted for A.
                    *)
                    
                   msgs: list msg
                   (* 
                   In any state s, if m ∈ s.msgs, then some node sent the
                   message m on network. 
                     *)}

(*
 * Assume a node called self
 *)
assume val self: Node.t
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

let is_safe s = 
  forall n1 n2. (*{:pattern (M.sel leader n1);(M.sel leader n2)} *)
      M.sel s.leader n1 = None \/ M.sel s.leader n2 = None 
                \/ M.sel s.leader n1 = M.sel s.leader n2

let inv2 {msgs;votes} =
    forall n. L.mem (Leader n) msgs ==> is_quorum (M.sel votes n)

let inv3 ({leader;msgs})  =
  forall n1 n2. (M.sel leader n1 = Some n2) ==> L.mem (Leader n2) msgs

let inv4 ({votes;msgs})  = 
  forall n1 n2. L.mem n2 (M.sel votes n1)  ==> L.mem (Vote n2 n1) msgs

let inv5 ({msgs}) = 
  forall n1 n2 n3. L.mem (Vote n1 n2) msgs /\ L.mem (Vote n1 n3) msgs  
        ==> n2 = n3

let inv6 ({msgs;voted}) = 
  forall n1 n2. L.mem (Vote n1 n2) msgs ==> M.sel voted n1

let  inv7 ({msgs})  = 
  forall n1 n2. L.mem (Leader n1) msgs /\ L.mem (Leader n2) msgs 
          ==> n1 = n2  

#set-options "--query_stats --split_queries always"
#set-options "--z3rlimit 10000"

(*
 * Initial state and its safety
 *)
let init_state = {leader = M.const None;
                  voted = M.const false;
                  votes = M.const [];
                  msgs = []}

val init_state_safe: (n:Node.t) ->
  Lemma (is_safe init_state (*/\ inv2 init_state*))
let init_state_safe n = ()


(*
 * Actions and their safety
 *)
let cast_vote n s = 
  if not (M.sel s.voted self) then
    let msgs' = (Vote self n )::s.msgs in
    let voted' = M.upd s.voted self true in
    {s with voted=voted'; msgs=msgs'}
  else
    s

val cast_vote_safe: n:Node.t -> s:state ->
    Lemma(requires is_safe s /\ inv2 s /\ inv3 s 
                    /\ inv4 s /\ inv5 s /\ inv6 s /\ inv7 s)
         (ensures is_safe (cast_vote n s) 
               /\ inv2 (cast_vote n s)
               /\ inv3 (cast_vote n s)
               /\ inv4 (cast_vote n s)
               /\ inv5 (cast_vote n s)
               /\ inv6 (cast_vote n s)
               /\ inv7 (cast_vote n s))
let cast_vote_safe n s = ()

(* recv_vote *)

val recv_vote: s:state -> s':state{
       (forall n x.  L.mem x (M.sel s.votes n) 
            ==> L.mem x (M.sel s'.votes n)) 
    /\ (forall n. L.mem (Leader n) s'.msgs ==> L.mem (Leader n) s.msgs)}
let recv_vote s = 
  let is_my_vote m = match m with
    | Vote frm to -> (to = self) && not(L.mem frm (M.sel s.votes self))
    | _ -> false in
  let my_vote = L.find is_my_vote s.msgs in
  match my_vote with
    | Some (Vote frm _) -> 
      let votes' = M.upd s.votes self 
            (L.concat [frm] (M.sel s.votes self)) in
      {s with votes=votes'}
    | _ -> s

val recv_vote_safe: s:state ->  
    Lemma(requires is_safe s /\ inv2 s /\ inv3 s
                    /\ inv4 s /\ inv5 s /\ inv6 s /\ inv7 s)
         (ensures is_safe (recv_vote s) 
                /\ inv2 (recv_vote s)
                /\ inv3 (recv_vote s)
                /\ inv4 (recv_vote s)
                /\ inv5 (recv_vote s)
                /\ inv6 (recv_vote s)
                /\ inv7 (recv_vote s))
let recv_vote_safe s = 
  ()

(*
 * Declare Leader
 *)

val declare_leader: state -> state
let declare_leader s = 
  let my_votes = M.sel s.votes self in
  if is_quorum my_votes then
    {s with msgs = (Leader self)::s.msgs}
  else s

val declare_leader_safe: s:state -> 
    n1:Node.t -> n2:Node.t -> 
    Lemma(requires is_safe s /\ inv2 s /\ inv3 s
                    /\ inv4 s /\ inv5 s /\ inv6 s
                    /\ inv7 s)
         (ensures is_safe (declare_leader s) 
                /\ inv2 (declare_leader s)
                /\ inv3 (declare_leader s)
                /\ inv4 (declare_leader s)
                /\ inv5 (declare_leader s)
                /\ inv6 (declare_leader s)
                /\ inv7 (declare_leader s))
let declare_leader_safe s n1 n2 = ()

(*
 * Register Leader
 *)

val register_leader: state -> state
let register_leader s = 
  match L.find (function (Leader _) -> true 
                        | _ -> false) s.msgs with
  | Some (Leader n) ->
      let _ = assert(L.mem (Leader n) s.msgs) in 
      let _ = assert(inv7 s ==> 
                (forall n'. L.mem (Leader n') s.msgs ==> n'=n)) in
      {s with leader = M.upd s.leader self (Some n)}
  | _ -> s

val register_leader_safe: s:state ->
    Lemma(requires is_safe s  /\ inv2 s/\ inv3 s
                    /\ inv4 s /\ inv5 s /\ inv6 s
                    /\ inv7 s)
         (ensures is_safe (register_leader s)
                  /\ inv2 (register_leader s)
                  /\ inv3 (register_leader s)
                  /\ inv4 (register_leader s)
                  /\ inv5 (register_leader s)
                  /\ inv6 (register_leader s)
                  /\ inv7 (register_leader s))
let register_leader_safe s =
  let {leader; msgs} = s in
  let s' = register_leader s in
  (*
   * Somehow the theorem needs to be restated for F* to prove.
   *)
  let _ = assert(forall n1 n2 n3 n4. M.sel s'.leader n1 = Some n2
                  /\ M.sel s'.leader n3 = Some n4 ==> n2 = n4) in
  ()

let t = true
