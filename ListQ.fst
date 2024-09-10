module ListQ

module L = FStar.List.Tot

type t a = list a

let mem = L.mem

val concat: #a:eqtype -> l1:list a -> l2:list a 
  ->l:(list a){forall x. mem x l <==> mem x l1 \/ mem x l2}
let rec concat #a l1 l2 = match l1 with
  | [] -> l2 
  | x::xs -> x::(concat xs l2)

let (@) = concat

val rev: #a:eqtype -> l1:list a 
  -> l:list a{forall x. mem x l <==> mem x l1}
let rec rev l1 = match l1 with
  | [] -> []
  | x::xs -> (rev xs)@[x]
  

val filter: #a:eqtype -> f:(a -> bool) -> l1:list a
    -> l:list a{forall x. mem x l <==> mem x l1 /\ f x}
let rec filter #a f l1 = match l1 with
  | [] -> []
  | x::xs -> if f x then x::(filter f xs)
             else filter f xs

val partition: #a:eqtype -> f:(a -> bool) -> l:list a
    -> p:(list a * list a){let (l1,l2) = p in 
        forall x. (*{:pattern (mem x l1); (mem x l2); (mem x l)}*)
          mem x l <==> mem x l1 \/ mem x l2}
let rec partition #a f l = match l with
  | [] -> ([], [])
  | x::xs -> let (s1,s2) = partition f xs in
      if f x then ((x::s1),s2) else (s1,x::s2)

val partition_mem_l1: #a:eqtype -> f:(a -> bool) -> l:list a
    ->x:a 
    ->Lemma(let (l1,l2) = partition f l in 
              (mem x l1 ==> mem x l) /\ (mem x l2 ==> mem x l))
let rec partition_mem_l1 #a f l x = ()

val find: #a:eqtype -> f:(a -> bool) -> l:list a 
      -> v:option a{match v with 
          | Some x -> mem x l /\ f x
          | None -> forall x. mem x l ==> not (f x)}
let rec find #a f l = match l with
  | [] -> None
  | x::xs -> if f x then Some x else find f xs