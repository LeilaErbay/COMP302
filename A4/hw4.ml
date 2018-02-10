(* STUDENT: LEILA ERBAY
   ID: 260672158 
*)

(* Q1: A Rose by any Other Name Would Smell as Sweet *)

type 'a rose_tree = Node of 'a * ('a rose_tree) list

(* Find with exceptions *)

exception BackTrack

(* Q1.1 write a function that finds an element of the tree using backtracking with exceptions *)

let rec find_e (p : 'a -> bool) (t : 'a rose_tree) : 'a = match t with
 (* Function with exceptions *)
(* if e is a match then return e, else match on next node and its list as well as whole list *)
 | Node(e, l) ->
    if (p e) then e

    else match l with
     | [] -> raise BackTrack
     | Node(elem,rt)::tl -> if p elem then elem
        else try find_e p (Node(elem, tl)) with BackTrack -> find_e p (Node(elem, rt))

(* Q1.1: write this function and it helper functions *)
let find (p : 'a -> bool)  (t : 'a rose_tree) : 'a option =
   (* call find_e and handle the exceptions *)
 (try Some ( find_e p t) with BackTrack -> None)

(*--------------------------------------------------------------------------------------*)

(* Find with failure continuations *)

let rec find_k (p : 'a -> bool) (t : 'a rose_tree) (k : unit -> 'a option) : 'a option =
 match t with
(* if e is a match then return e, else match on next node and its list as well as whole list *)
  | Node(e,l) ->
    if (p e) then Some e

    else match l with
    | [] -> k ()
    | (Node(elem, rt)::tl) ->
       if (p elem) then Some elem
       else  (find_k p (Node(elem,tl)) (fun () -> find_k p (Node(elem,rt)) k ))


(* Q1.2: write this function and it helper functions *)
let find' (p : 'a -> bool)  (t : 'a rose_tree) : 'a option =
(*  call find_k with the appropriate inital continuation *)
 find_k p t (fun () -> None)



(*---------------------------------------------------------------------------------------*)

(* Find all with continuations *)
let rec find_all_k  (p : 'a -> bool) (t : 'a rose_tree) (k : 'a list -> 'b) : 'b =
 match t with
 | Node(e,l) ->
   match l with
   | [] ->  k[]
   | (Node(elem,rt)::tl) ->
       (if (p elem) then
         find_all_k p (Node(elem,tl)) (fun el -> find_all_k p (Node(elem,rt)) (fun er -> k (el@(elem::er))))
       else
         find_all_k p (Node(elem,tl)) (fun el -> find_all_k p (Node(elem,rt)) (fun er -> k (el @ er)))
       )
(* Q1.3: write this function and it helper functions *)
let find_all p t = find_all_k p t (fun el -> match el with [] -> [] | _ -> el)


(* An example to use *)

let example = Node (7, [ Node (1, [])
                         ; Node (2, [Node (16, [])])
                         ; Node (4, [])
                         ; Node (9, [])
                         ; Node (11, [])
                         ; Node (15, [])
                         ])


let is_big x =  x > 10

(*-----------------------------------------------------------------------------------------------------*)


(* Q2 : Rational Numbers Two Ways *)

type fraction = int * int

module type Arith =
  sig
    type t
    val epsilon : t             (* A suitable tiny value, like epsilon_float for floats *)

    val plus : t -> t -> t      (* Addition *)
    val minus : t -> t -> t     (* Substraction *)
    val prod : t -> t -> t      (* Multiplication *)
    val div : t -> t -> t       (* Division *)
    val abs : t -> t            (* Absolute value *)
    val lt : t -> t -> bool     (* < *)
    val le : t -> t -> bool     (* <= *)
    val gt : t -> t -> bool     (* > *)
    val ge : t -> t -> bool     (* >= *)
    val eq : t -> t -> bool     (* = *)
    val from_fraction : fraction -> t (* conversion from a fraction type *)
    val to_string : t -> string        (* generate a string *)
  end

module FloatArith : Arith =
struct
  type t = float
  let epsilon = epsilon_float
  let from_fraction (num, den) = float_of_int num /. float_of_int den

  let plus = (+.)
  let minus = (-.)
  let prod = ( *. )
  let div = ( /. )
  let abs = abs_float
  let lt = (<)
  let le = (<=)
  let gt = (>)
  let ge = (>=)
  let eq = (=)
  let to_string x = string_of_float x
end

(*----------------------------------------------------------------------------------------------------*)
(* Q2.1: Implement the Arith module using rational numbers (t = fraction) *)

module FractionArith: Arith = 
 struct
   type t = fraction
   let epsilon = (1, 1000000)

(* gcd and simplify used to simplify fractions or else squareroot is not functional *)
  let rec gcd (nom : int) (denom : int) : int =
   if denom <> 0 then (gcd denom (nom mod denom))
   else (abs nom)

 let simplify nom denom =
  let gcd_val = (gcd nom denom) in (nom / gcd_val, denom/ gcd_val)

   let plus (n1, d1) (n2, d2) =
     let d_final = d1 * d2 in
     let n3 = n1 * d2 in
     let n4 = n2 * d1 in
     let n_final = n3 + n4 in
     match ((n1, d1), (n2,d2)) with
      | (0, _), (_, _) -> (n2, d2)
      | (_, _), (0, _) -> (n1, d1)
      | (_, _), (_, _) -> simplify n_final  d_final

   let minus (n1, d1) (n2, d2) =
     let d_final = d1 * d2 in
     let n3 = n1 * d2 in
     let n4 = n2 * d1 in
     let n_final = n3 - n4 in
     match ((n1, d1), (n2,d2)) with
      | (0, _), (_, _) -> ((0-n2), d2)
      | (_, _), (0, _) -> (n1, d1)
      | (_, _), (_, _) -> simplify n_final d_final


   let prod (n1, d1) (n2, d2) =
    let d_final = d1 * d2 in
    let n_final = n1 * n2 in
    match ((n1,d1),(n2,d2)) with
     | (0, _), (_, _) -> (0,d_final)
     | (_, _), (0, _) -> (0, d_final)
     | (_, _), (_, _) -> simplify n_final d_final

   let div (n1, d1) (n2, d2) =
    let temp = n2 in
    let n2_new =  d2 in
    let d2_new = temp in
    prod (n1,d1) (n2_new, d2_new)

  let abs (n, d) = simplify (abs n) (abs d)


   let lt (n1, d1) (n2, d2) =
    let n3=  n1*d2 in
    let n4 = n2*d1 in
    if (n3  <  n4) then true else false

  let le (n1, d1) (n2, d2) =
    let n3 = n1 * d2 in
    let n4 = n2 * d1 in
    if ( n3 <= n4 ) then true else false

   let gt (n1, d1) (n2, d2) =
    let n3 = n1 * d2 in
    let n4 = n2 * d1 in
    if (n3 > n4) then true else false


   let ge (n1, d1) (n2, d2) =
    let n3 = n1 * d2 in
    let n4 = n2 * d1 in
    if (n3 >= n4) then true else false


   let eq (n1, d1) (n2, d2) =
    let n3 = n1 * d2 in
    let n4 = n2 * d1 in
    if (n3 = n4) then true else false

   let from_fraction (n,d) = (n,d)

   let to_string (n,d) =
    let n_str = string_of_int n in
    let div_sym = "/" in
    let d_str = string_of_int d in
    let str_l = n_str::div_sym::[d_str] in
    String.concat " " str_l
 end


(*--------------------------------------------------------------------------------*)

module type NewtonSolver =
  sig
    type t

    val square_root : t -> t
  end

(* Q2.2: Implement a function that approximates the square root using  the Newton-Raphson method *)

module Newton (A : Arith) : (NewtonSolver with type t = A.t) =
 struct
   type t = A.t

   let convert n = A.from_fraction (n, 1)

   let square_root a =
    let rec findroot x acc =
     let next = A.div (A.plus(A.div a x) x) (convert 2) in
      if A.lt ((A.abs(A.minus x next))) acc then A.abs x
      else findroot next acc
     in findroot (convert 1) A.epsilon
 end

(* Examples *)
(*
 module FloatNewton = Newton (FloatArith)
 module RationalNewton = Newton (FractionArith) 

let sqrt2 = FloatNewton.square_root (FloatArith.from_fraction (2, 1)) 
let sqrt2_r = RationalNewton.square_root (FractionArith.from_fraction (2, 1))

let sqrt5_r = RationalNewton.square_root (FractionArith.from_fraction (5, 1))
let sqrt64_r = RationalNewton.square_root (FractionArith.from_fraction (64, 1))

let sqrt9_r = RationalNewton.square_root (FractionArith.from_fraction (9, 1))


let sqrt4 = FloatNewton.square_root (FloatArith.from_fraction (4, 1))
let sqrt4_r = RationalNewton.square_root (FractionArith.from_fraction (4, 1))
*)
(*----------------------------------------------------------------------------------------------------------*)

(* Q3 : Real Real Numbers, for Real! *)

type 'a stream =
 { head : 'a  ;
   tail : unit -> 'a stream }

let rec nth z = function
  | 0 -> z.head
  | n -> nth (z.tail()) (n - 1)

let rec constant x =
 { head = x ;
   tail = fun () -> constant x }

(* Some examples *)

let sqrt2 =
  {head = 1 ;
   tail = fun () -> constant 2} (* 1,2,2,2,2... *)

let golden_ratio = constant 1   (* 1,1,1,1,1,1 *)

let rec take n z =
  if n = 1 then [z.head]
  else z.head::(take (n-1) (z.tail()))

(* Q3.1: implement the function q as explained in the pdf *)
let rec q z n =
 match n with
  | 0 -> 1
  | 1 -> nth z 1
  | _ -> (((nth z (n)) * (q z (n-1))) + (q z (n-2)))

(*In Q3.2 & Q3.3 there are chances of division by zero so those have been accounted for *)

(* Q3.2: implement the function r as in the notes *)
let rec r z n = match n with
  | 0 -> float (nth z 0)
  | _ ->
        let q_n_1 = (float(q z (n-1))) in
        let q_n= (float(q z n)) in
        let num = (-1.0) ** float(n-1) in

        let x_n =  num /. (q_n_1 *. q_n) in
        let x_n_1 = (r z (n-1)) in

         if q_n_1 = 0.0 || q_n = 0.0 || x_n =0.0 then x_n_1
         else x_n_1 +. x_n

(* Q3.3: implement the error function *)
let error z n =
 if n= 0 ||  (q z n) = 0 || ((q z n) + (q z (n-1))) = 0 then 0.0
 else (1.0 /. (float (q z n) *. (float (q z n) +. float (q z (n-1)))))

(* Q3.4: implement a function that computes a rational approximation of a real number *)
let rat_of_real z approx =
 let rec rat' z approx n =
  if (error z n) < approx then r z n
  else rat' z approx (n+1)
 in rat' z approx 1


let real_of_int n =
  { head = n ;
    tail = fun () -> constant 0 }



(* Q3.5: implement a function that computes the real representation of a rational number   *)
let rec real_of_rat r =
 { head = int_of_float (floor r);
   tail = fun () ->
                    let diff = r -. (floor r) in
                     if diff < epsilon_float || diff = 0.0 then constant 0
                     else real_of_rat (1.0/. diff)
 }



(* Examples *)
(*
(* Approximations of the  irrational numbers we have *)
let er2 = error (constant 2) 10

let sqrt_2_rat = rat_of_real sqrt2 1.e-5

let golden_ratio_rat = rat_of_real golden_ratio 1.e-5

(* To test the representation of rationals we can try this *)
 let to_real_and_back n = rat_of_real (real_of_rat n) 0.0001 

(* e1 should be very close to 10 (it is exactly 10 in the model solution) *)
 let e1 = to_real_and_back 10.0 

(* this is the float approximation of pi, not the real number pi *)
 let not_pi = 2. *. acos 0.

(* This should share the same 4 decimals with not_pi *)
 let not_pi' = to_real_and_back not_pi 
*)

