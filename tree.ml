(* Author: Charlie Bloomfield. *)

type 'a bintree = Empty | Node of 'a * 'a bintree * 'a bintree
type 'a narytree = NNode of 'a * ('a narytree) list

(* test trees *)
let t1 = Node(1, Node(7, Empty, Empty), Node(3, Node(4, Empty, Empty), Empty))
let t2 = NNode(1, [NNode(2, []); NNode(6,[]); NNode(4, [NNode(5, [])])])

(* less than 5 function *)
let lt5 x = x < 5

(* standard binary tree fold *)
let rec btreefold f e t = match t with
	|Empty -> e
	|Node(x, l, r) -> f x (btreefold f e l) (btreefold f e r)

(* binary tree fold with continuations *)
let btreefoldcont f e t =
	let rec btfc t cont = match t with
		|Empty -> cont e
		|Node(x, left, right) -> btfc left (fun l -> btfc right (fun r -> cont (f x l r) ))
	in btfc t (fun e -> e)

(* spice mix with treefold*)
let rec spicemix t = btreefoldcont (fun x l r -> 
	[x]::(List.map(fun el -> x::el) l) @ (List.map (fun el -> x::el) r)) [] t

(* binary tree map with continuations *)
let btreemapcont f t =
	let rec btmc t cont = match t with
		|Empty -> cont Empty
		|Node(x, left, right) -> btmc left (fun l -> btmc right (fun r -> cont (Node(f x, l, r)) ))
	in btmc t (fun tree -> tree)

(* binary tree collect with continuations : output to list*)
let rec bcollectcont p t =
	let rec bcollect' t cont = match t with
		|Empty -> cont []
		|Node(x, left, right) -> 
			if p x then bcollect' left (fun l1 -> bcollect' right (fun l2 -> (cont l1@x::l2) ))
			else bcollect' left (fun l1 -> bcollect' right (fun l2 -> (cont l1@l2) ))
	in bcollect' t (fun l -> l)

(* btreecollect with exceptions *)
exception Answer of (int list)
let bcollectexn p t =
	let rec bcollectexn' t = match t with
		|Empty -> raise (Answer([]))
		|Node(x, left, right) -> try bcollectexn' left with
			|Answer(l) -> try bcollectexn' right with
				|Answer(r) -> if p x then raise (Answer(l@x::r)) else raise (Answer(l@r))
	in try bcollectexn' t with Answer(l) -> l

(* insert node into tree : just a helper function *)
let rec insert n t = match t with
	|Empty -> Node(n, Empty, Empty)
	|Node(x, left, right) -> if n < x then Node(x, insert n left, right) else Node(x, left, insert n right)

(* binary tree collect with continuations : output to tree *)
let bcollectconttotree p t =
	let rec bcollectconttotree' t cont = match t with
		|Empty -> cont Empty
		|Node(x, left, right) -> 
			if p x then bcollectconttotree' left (fun l -> bcollectconttotree' right (fun r -> cont (Node(x, l, r))))
			else bcollectconttotree' left (fun l -> bcollectconttotree' right (fun r -> cont (mergeTrees l r)))
	and mergeTrees t1 t2 = match t1, t2 with
		|Empty, Empty -> Empty
		|Empty, Node(x, l, r) -> t2
		|Node(x, l, r), Empty -> t1
		|Node(x1, l1, r1), Node(x2, l2, r2) -> mergeTrees r1 (mergeTrees l1 (insert x1 t2))
	in bcollectconttotree' t (fun tree -> tree)

(* binary tree collect with accumulators : output to tree *)
let bcollectacctotree p t =
	let rec bcollectacctotree' t acc = match t with
		|Empty -> acc
		|Node(x, left, right) -> if p x then bcollectacctotree' left (bcollectacctotree' right (insert x acc))
			else bcollectacctotree' left (bcollectacctotree' right acc)
	in bcollectacctotree' t Empty

(* binary tree collect with accumulator *)
let rec bcollectacc p t =
	let rec bcollect_acc' t acc = match t with
		|Empty -> acc
		|Node(x, left, right) -> 
			if p x then bcollect_acc' left (bcollect_acc' right (x::acc))
			else bcollect_acc' left (bcollect_acc' right acc)
	in bcollect_acc' t []

(* binary tree collect with standard recursion *)
let rec bcollectshitty p t = match t with
	|Empty -> []
	|Node(x, l, r) -> if p x then (bcollectshitty p l) @ (x::(bcollectshitty p r)) else (bcollectshitty p l)@(bcollectshitty p r)

(* nary tree find with continuations *)
let nfindcont p t =
	let rec nfind' t c = match t with	
		|NNode (x, children) -> if p x then Some x else nfindchildren children c
	and nfindchildren tlist c = match tlist with
		|[] -> c ()
		|t::ts -> nfind' t (fun () -> nfindchildren ts c)
	in nfind' t (fun () -> None)

(* nary treefold ('a -> 'a list -> 'b) -> 'a -> ('a * 'a list) -> 'b *)
let ntreefold f b t =
	let rec ntreefold' t = match t with
		|NNode(x, children) -> f x (ntreefoldchildren children) 
	and ntreefoldchildren tlist = match tlist with
		|[] -> [b]
		|t::ts -> (ntreefold' t)::(ntreefoldchildren ts)
	in ntreefold' t

(* nary tree collect with standard recursion *)
let weirdncollect p t = 
	let rec weirdncollect' t = match t with
		|NNode(x, children) -> if p x then x::(weirdncollectchildren children) else weirdncollectchildren children
	and weirdncollectchildren tlist = match tlist with
		|[] -> []
		|_ -> List.flatten (List.map (fun t -> weirdncollect' t) tlist)
	in weirdncollect' t

(* nary tree collect with exceptions *)
let ncollectexn p t = 
	let rec ncollectexn' t = match t with
		|NNode(x, children) -> 
			try ncollectexnchildren children with
				|Answer(l) -> if p x then raise (Answer(x::l)) else raise (Answer(l)) 
	and ncollectexnchildren tlist = match tlist with
		|[] -> raise (Answer([]))
		|t::ts -> try ncollectexn' t with
			|Answer(l) -> try ncollectexnchildren ts with
				|Answer(r) -> raise (Answer(l@r))
	in try ncollectexn' t with Answer(l) -> l

(* narytree collect with continuations *)
let ncollectcont p t =
	let rec ncollect' t c = match t with
		|NNode (x, children) -> 
			if p x then ncollectchildren children (fun l -> c (x::l))
			else ncollectchildren children c
	and ncollectchildren tlist c = match tlist with
		|[] -> c []
		|t::ts -> ncollect' t (fun l -> l@(ncollectchildren ts c))
	in ncollect' t (fun l -> l)

(* nary tree collect with accumulator *)
let ncollectacc p t =
	let rec ncollect_acc' t acc = match t with
		|NNode(x, children) -> 
			if p x then ncollectchildren_acc children (x::acc)
			else ncollectchildren_acc children acc
	and ncollectchildren_acc tlist acc = match tlist with
		|[] -> acc
		|t::ts -> ncollectchildren_acc ts (ncollect_acc' t acc)
	in ncollect_acc' t []
