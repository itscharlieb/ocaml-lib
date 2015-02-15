(* List Things *)
let max3 x y z = if x > y && x > z then x else if y > x && y > z then y else z
let max2 x y = if x > y then x else y

let rec lcs s1 s2 = match s1, s2 with
	|x::xs, y::ys -> max2 (if x = y then (1 + (lcs xs ys)) else 0) (max3 (lcs xs s1) (lcs s1 ys) (lcs xs ys))
	|_, _ -> 0

let rec insSort l = match l with 
	|[] -> []
	|x::xs -> insert x (insSort xs)
and insert x l = match l with 
	|[] -> [x]
	|h::t -> if x < h then x::l else h::(insert x t)

let factcont n = 
	let rec factcont' n cont = match n with
		|0 -> cont 1
		|n -> factcont' (n-1) (fun x -> cont (n * x))
	in factcont' n (fun x -> x)

let foldcont f b l = 
	let rec lfcont l cont = match l with
		|[] -> cont b
		|h::t -> lfcont t (fun x -> cont (f h x))
	in lfcont l (fun x -> x)

let rec stagedfoldright l = match l with
	|[] -> fun f b -> b
	|h::t -> let subfold = stagedfoldright t in
		fun f b -> f h (subfold f b)

let rec stagedfoldleft l = match l with
	|[] -> fun f b -> b
	|h::t -> let subfold = stagedfoldleft t in
		fun f b -> subfold f (f h b)

let rec foldleft f b l = match l with
	|[] -> b
	|h::t -> foldleft f (f h b) t

let rec foldright f b l = match l with
	|[] -> b
	|h::t -> f h (foldright f b t)

let filtercont f l =
	let rec filtercont' l cont = match l with
		|[] -> cont []
		|h::t -> filtercont' t (fun l -> if f h then cont(h::l) else cont l)
	in filtercont' l (fun l -> l) 

let copy l = List.fold_left (fun acc el -> acc@[el]) [] l

let flattencont m = 
	let rec f' m c = match m with 
		|[] -> c []
		|l::ls -> f' ls (fun t -> c (l @ t))
	in f' m (fun l -> l)

let rec flatten m = match m with
	|[] -> []
	|l::ls -> l @ flatten ls

let rec interleave x l = match l with 
	|[] -> [[x]]
	|h::t -> (x::l) :: (List.map (fun s -> h::s) (interleave x t))

let rec permutations l = match l with
	|[] -> [[]]
	|x::xs -> flattencont (List.map (interleave x) (permutations xs))

let rec subseq i l = match l with
	|[] -> 0
	|x::xs -> if i < x then subseq i xs else
		max (1 + subseq (i - x) xs) (subseq i xs)

let longestIncreasingSubsequence l = 
	let rec lis i l = match l with
		|[] -> 0
		|x::xs -> if i < x then max (1 + (lis x xs)) (lis i xs) else lis i xs
	in lis 0 l

let rec sublist i l = match l with
	|[] -> []
	|x::xs -> if i < x then sublist i xs else x::(sublist (i - x) xs)

let rec sublist_cont' i l cont = match l with 
	|[] -> cont []
	|x::xs -> if i < x then sublist_cont' i xs cont else sublist_cont' (i - x) xs (fun t -> cont (x::t))

let sublist_cont i l = sublist_cont' i l (fun l -> l)