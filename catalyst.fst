module Catalyst

module S = FStar.Set


val set_equal: #a:eqtype -> S.set a -> S.set a -> prop
let set_equal #a s1 s2 = forall x. S.mem x s1 <==> S.mem x s2

let (=.) = set_equal

val mem : #a:eqtype -> list a -> S.set a
let rec mem #a l = match l with
  | [] -> S.empty
  | x::xs -> S.add x (mem xs)


val dotp : #a:eqtype -> x:a -> l:list a 
        -> s:(S.set (a&a)){forall y. {:pattern (S.mem (x,y) s)}
                S.mem y (mem l) <==> S.mem #(a&a) (x,y) s}
let rec dotp #a x l = match l with
  | [] -> S.empty
  | y::ys -> S.add (x,y) (dotp x ys)

val dotp_is_correct: #a:eqtype -> x:a -> l:list a -> y:a -> z:a
        -> Lemma ((y = x && S.mem z (mem l))
                    == S.mem (y,z) (dotp x l))
                 [SMTPat (S.mem (y,z) (dotp x l))]
let rec dotp_is_correct #a x l y z =
  match l with
  | [] -> ()
  | hd :: tl ->
    dotp_is_correct x tl y z

val cartp_prop: #a:eqtype -> list a -> list a -> S.set (a&a) -> prop
let cartp_prop #a l1 l2 s = 
    forall x y. S.mem (x,y) s <==> S.mem x (mem l1) /\ S.mem y (mem l2)  

#push-options "--query_stats --split_queries always"
#set-options "--z3rlimit 1000"

val cartp: #a:eqtype -> l1:list a -> l2:list a -> 
      s:S.set (a&a){cartp_prop l1 l2 s}
let rec cartp #a l1 l2 = match l1 with
  | [] -> S.empty #(a&a)
  | x::xs -> S.union (dotp x l2) (cartp xs l2)

val ob_ord : #a:eqtype -> list a -> S.set (a & a)
let rec ob_ord #a l = match l with
  | [] -> S.empty
  | x::xs -> S.union (dotp x xs) (ob_ord xs)

val oa_ord : #a:eqtype -> list a -> S.set (a & a)
let rec oa_ord #a l = match l with
  | [] -> S.empty
  | x::xs -> S.union (cartp xs [x]) (oa_ord xs)

(*
 * When using the provided set equality: `==`
 * If you change `S.union (mem xs) (S.singleton x)` to 
 * `S.union (S.singleton x) (mem xs)`, type checking would 
 * fail because commutativity of set union w.r.t `==` is 
 * never asserted.
 * Using `=.` defined above fixes this problem as it is 
 * defined in terms of `S.mem`, which is related to set 
 * operations through a variety of lemmas.
 *)
val cons: #a:eqtype -> x:a -> xs:list a 
  -> l:list a{mem l =. S.union (S.singleton x) (mem xs)
          /\ ob_ord l =. S.union (dotp x xs) (ob_ord xs)
          /\ oa_ord l =. S.union (cartp xs [x]) (oa_ord xs)}
let cons x xs = x::xs

let append_prop l1 l2 l = 
  (mem l =. S.union (mem l1) (mem l2)) /\
  (ob_ord l =. S.union (S.union (ob_ord l1) (ob_ord l2)) (cartp l1 l2)) /\
  (oa_ord l =. S.union (S.union (oa_ord l1) (oa_ord l2)) (cartp l2 l1))

val append: #a:eqtype -> l1:list a -> l2:list a 
        -> l:list a{append_prop l1 l2 l}
let rec append l1 l2 = match l1 with
  | [] -> l2
  | x::xs -> x::(append xs l2)

val rev: #a:eqtype -> l1:list a 
        -> l:list a{mem l =. mem l1 
              /\ ob_ord l =. oa_ord l1 
              /\ oa_ord l =. ob_ord l1} 
let rec rev l1 = match l1 with
  | [] -> []
  | x::xs -> append (rev xs) [x]

val filter_prop:#a:eqtype -> list a -> (a->bool) -> list a -> prop
let filter_prop #a l1 f l =
      (forall x. S.mem x (mem l) <==> S.mem x (mem l1) /\ f x)
  /\  (forall x y. S.mem (x,y) (ob_ord l) 
          <==> S.mem (x,y) (ob_ord l1) /\ f x /\ f y) 

val filter: #a:eqtype -> f:(a -> bool) -> l1:list a
      -> l:list a{filter_prop l1 f l}
let rec filter #a f l1 = match l1 with
  | [] -> []
  | x::xs -> if f x then x::(filter f xs) else (filter f xs)

  
