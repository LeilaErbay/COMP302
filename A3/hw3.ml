(* Submitted by Leila Erbay, 260672158
   Collaborated Richard Gao, 260729805 *)
   


(* Question 1 - Unfolding *)

(* This is the function unfold, take some time to compare it it fold.
   If fold_left and fold_right take lists to generate a value, this
   function takes a value that will generate a list. The relation
   between folds and unfolds is the beginning of a wonderful tale in
   computer science. But let's not get ahead of ourselves.

   Unfold takes a function that from a seed value it generates a new
   element of the list, and a the seed for the next element, another
   function to stop the generation, and an initial seed.
*)

let rec unfold (f: 'seed -> ('a * 'seed)) (stop : 'b -> bool) (b : 'seed) : 'a list =
  if stop b then []
  else let x, b' = f b in
       x :: (unfold f stop b')

let nats max = unfold (fun b -> b, b + 1) (fun x -> x > max) 0


(* Q1.1: Return the even numbers up-to max *)
let evens max = unfold (fun b -> b, b+2) (fun b -> max < b ) 0


(* Q1.2: Return the Fibonacci sequence up-to max *)
(* using references to store the first and second 
   fib values and updating b each time call to unfold  *)
let fib max =
 let rec fib1 = ref 0 in
  unfold (fun b  -> let fib2 = !fib1 in fib1 := b; b,b+(fib2)) 
         (fun b ->  b > max ) 1


(* Q1.3: Return the list of rows of the Pascal triangle that are shorter than ma*)
(* created a function inside pascal that adds a 0 to the beginning and end of the same
    row and adds the two rows together. 
    Example if l = [1;1] then combine works with List.map2 [0;1;1] [1;1;0] -> [1;2;1] *)

let pascal max =
 let combine l = match l with
  | [] -> []
  | h :: t -> List.map2 (+) ([0] @ l) (l @ [0])  
 in
  unfold (fun l  -> l, combine l  ) (fun row -> List.length row > max-1) [1]    


let rec zip (l1 : 'a list) (l2 : 'b list) :  ('a * 'b) list =
match l1, l2 with
| [], _ -> []
| _, [] -> []
| x::xs, y::ys -> (x, y):: zip xs ys

(* (Extra credit) Optional: implement zip with a single call to unfold *)
(* used similar matching as zip  *)
let zip' l1 l2 = unfold (fun (l1,l2) -> match (l1,l2) with
                                                | [],_ -> ((None, None), ([],[]))
                                                | _,[] -> ((None, None), ([],[]))
                                                | (h1::t1,h2::t2) ->(h1,h2) , (t1,t2)) 
                        (fun (l1, l2) ->  List.length l1 == 0 || List.length l2 == 0 ) (l1,l2) 

(* Question 2 *)
let counter = ref 0;;
let ugly x =
  counter := !counter+1;
  let rec ackermann m n = match (m , n) with
    | 0 , n -> n+1
    | m , 0 -> ackermann (m-1) 1
    | m , n -> ackermann (m-1) (ackermann m (n-1))
  in
  ackermann 3 x

let memo_zero (f : 'a -> 'b) : 'a -> 'b = f


(* Q2.1: Write a function that memoizes the last value called. *)
(* Memo_one uses a ref tuple to store the previous result. If ref tuple is empty then update the ref tuple. 
   Else if the ref tuple is not empty, it returns the fx. If the ref tuple is not empty but the value 
   searched for doesn't exist then update the ref tuple   *)
let memo_one (f : 'a -> 'b) : ('a -> 'b) = 
 let ref_tuple = ref (None,None) in 
(fun input ->  
  let r = f input in
  match !ref_tuple with
  | None, None -> (ref_tuple := (Some input, Some r); r)
  | Some x, None -> assert false
  | None, Some x -> assert false
  | Some x, Some fx -> if input = x then fx
      else (ref_tuple := (Some input, Some r);
      r))
  
(*
let ugly' = memo_one ugly

let u1 = ugly' 3                (* this one calls ugly with 3 *)
let u2 = ugly' 3                (* this one uses the stored value *)
let u3 = ugly' 1                (* the stored value is for 3 so it calls ugly *)
let u4 = ugly' 2                (* the stored value is for 1 so it calls ugly *)
let u5 = ugly' 10               (* the stored value is for 2 so it calls ugly and takes a couple of seconds *)
let u6 = ugly' 10               (* the one uses the stored value and returns immediately *)
*)

(* Q2.2: Write a function that memoizes the last value called. *)
(* Used a ref list that will contain tuples. Using List.assoc I search through ref_list with x 
   to see if a pair is found containg x. If so, then return the associated value. Else if the length
   of the list inputted by the user is greater than the length of the ref_list then there is room to add
   add an x, fx into the list. Else if n <= length of ref list then remove head and add the x, fx to the end
   of the list*)
let memo_many (n : int) (f : 'a -> 'b) : 'a -> 'b =
 let ref_list = ref [] in
  (fun x -> 
   try 
     match List.assoc x !ref_list with
     | fx -> fx
   with Not_found -> 
     let f_x = f x in
     if n > List.length !ref_list then
      (ref_list := !ref_list @ [(x, f_x)]; f_x)
     else match !ref_list with
      | [] -> assert false	 
      | h::t -> (ref_list := t @ [(x, f_x)]; f_x )) 



(* Question 3: Doubly-linked circular lists  *)

(* Circular doubly linked lists *)
 
(* The type of a cell (a non-empty circular list) *)
type 'a cell = { mutable p : 'a cell; data : 'a ; mutable n : 'a cell}

(* The type of possibly empty circular lists *)
type 'a circlist = 'a cell option

(* An empty circular list *)
let empty :'a circlist = None

(* A singleton list that contains a single element *)
let singl (x : 'a) : 'a circlist =
  let rec pointer = {p = pointer ; data = x ; n = pointer} in
  Some pointer

(* Rotate a list to next element *)
let next : 'a circlist -> 'a circlist = function
  | None -> None
  | Some cl -> Some (cl.n)

(* Rotate a list to previous element *)
let prev : 'a circlist -> 'a circlist = function
  | None -> None
  | Some cl -> Some (cl.p)

(* Q3.1: Write a function that add a new element at the beginning of a list *)
(* Cons returns either a singleton of x if xs is empty. But if xs is not empty then have x stored in a cell whose 
   previous points to the end of xs and next points to the current head. Update the the head of xs and last elem of 
   xs to point to the new cell *)
let cons (x : 'a)  (xs : 'a circlist) : 'a circlist = match xs with
   |None -> singl x
   |Some head ->
     let rec new_head = {p = head.p; data = x ;n =head} in
       head.p.n <- new_head;
       head.p <- new_head;
       Some head

(* Q3.2: Write a function that computes the length of a list (Careful with the infinite loops)  *)
let rec length (l : 'a circlist) : int = 
(* If l is empty then its length is 0. Else keep a copy of it's original head and next element *) 
match l with 
 | None -> 0
 | Some head -> 
  let orig_head =  head in
  let next_h = head.n in

(* Using tail-rec, compare if the next head is the same as the original head (saved outside of tl rec function)
   if they are the same then return acc, if not then shift the list to the next head and compare the next next head to 
   the original  *)
   let rec length' l next_head  acc =
    match l with
     |None ->  acc
     |Some head ->   
      if next_head == orig_head then acc
      else  length' (next l) (next_head.n)  (acc+1)
   in length' l next_h 1 


(* Q3.3: Write a function that produces an immutable list from a circular list *)
let to_list (l : 'a circlist)  : 'a list = 
(* similar saving of original head and next element as 3.2 *) 
match l with
 | None -> []
 | Some head -> 
  let orig_head = head in
  let next_c = head.n in
  
(* Using tail-rec, if l is empty then it will return an empty list from previous lines. Otherwise
   see if the next cell is the original head if so return acc. Else shift the list and the next head and
   add the cell of the cell next to the current head *)
   let rec to_list' l  next_cell acc =   
    match l with
    |None -> acc
    |Some head ->
      if next_cell == orig_head then acc
      else to_list' (next l)  (next_cell.n) (acc @[next_cell.data])
   in to_list' l  next_c [orig_head.data] 

(* Once you've written cons you can use this function to quickly populate your lists *)
let rec from_list : 'a list -> 'a circlist = function
  | [] -> empty
  | x::xs -> cons x (from_list xs)

(* Q3.4: Write a function that reverses all the directions of the list *)

(* Use a temp to store the next cell. Update the next cell to point to the previous
   and the previous to point to the next using a swap method. Do this as long as the length
   is greater than 0 *)
let rev (l : 'a circlist) : 'a circlist =
 let rec rev' l len = match l with 
    |None ->  l
    |Some cell ->             
              if len > 0 then 
                  let temp = cell.n in
                  cell.n <- cell.p;
                  cell.p <- temp;
                  (rev'  (prev l) (len-1))
              else l  
 in rev' (next l) (length l)

   
(* (Extra credit) OPTIONAL: Write the map function as applied to lists *)
let map (f : 'a -> 'b) : 'a circlist -> ' b circlist = assert false

(* Some possibly useful functions (Wink, wink!) *)

(* A function that returns the Greatest Common Denominator of two numbers *)
let rec gcd (u : int) (v : int) : int =
  if v <> 0 then (gcd v (u mod v))
  else (abs u)

(* A function that returns the least common multiple of two numbers *)
let lcm (m : int) (n : int) : int  =
  match m, n with
  | 0, _ | _, 0 -> 0
  | m, n -> abs (m * n) / (gcd m n)

(* (Extra credit) OPTIONAL A function that compares two lists ignoring the rotation *)
let eq (l1 : 'a circlist) (l2 : 'a circlist) : bool = assert false



(* Some examples *)
(*
let ex = cons 12 (cons 43 (cons 34 (singl 3)))
let lex = to_list ex

let l1 = from_list [true; true ; false]
let l3 = from_list [true; true ; false ; true; true ; false]

let l4 = from_list ['a'; 'b'; 'a'; 'b']
let l5 = from_list ['a'; 'b'; 'a'; 'b'; 'a'; 'b']

let l6 = from_list ['a'; 'a']
let l7 = from_list ['a'; 'a'; 'a']

let l8 = from_list [1 ; 2 ; 3]
let l9 = from_list [3 ; 1 ; 2]  (* eq l8 l9 = true *)

let l10 = from_list [1 ; 2 ; 3]
let l11 = from_list [3 ; 2 ; 1]  (* eq l10 l11 = false *)
*)
