(* Student information:

   Enter your name, and if you chose to work in pairs, the name of the
   student you worked with (both students MUST submit the solution to
   myCourses):

   Name: Leila Erbay
   McGill ID: 260672158

   If you worked in pairs, the name of the other student.

   Name: Richard Gao
   McGill ID: 260729805


 *)

(* Notice: by submitting as part of team, you declare that you worked
   together on the solution. Submissions in pairs are allowed to
   foster team work, they have to be developed by both students *)

(* Homework 1 - Questions 2 and 3 *)

(* First, some utility functions and declarations that you can use. Be
   sure to check Ocaml's documentation to find more functions
   available to you.

   You can start checking the documentation at:
   https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html
 *)

(* the value of pi *)
let pi : float =  acos ~-.1.0

(* a function to compare floats that allows for some imprecision *)
let cmp n m = abs_float (n -. m) < 0.0001

(* a simple test of positivity *)
let positive a = a > 0.0

(* a function to check if a is multiple of b *)
let is_multiple_of (a : float) (b : float) : bool =
  let m = a /. b in
  cmp (m -. floor m) 0.0

(* a function to check if a is between plus/minus b *)
let abs_btwn a b = a < b && a > ~-.b

(* Question 2: Triangles are the best *)

type side = float

type tr_by_sides = side * side * side

type tr_kind
  = Scalene
  | Equilateral
  | Isosceles


(* Question 2.1 *)

(* well_formed_by_sides: 'a tr_by_sides -> 'b bool
   checks if sum of 2 sides is greater than the third side *)
let well_formed_by_sides (a, b, c : tr_by_sides) : bool = 
 if (positive a && positive b && positive c) then  
   if ((a +. b > c) || (a +. c > b) || (b +. c > a)) then true
   else false 
 else false
;; 


(* Question 2.2 *)

(* create_triangle: 'a tr_kind -> 'b float -> 'c tr_by_sides 
   based on triangle type and area returns 3 side values for a valid triangle *)
let create_triangle (kind : tr_kind) (area : float) : tr_by_sides =  
 let w : float = sqrt(area /. sqrt(3.0)) in 
 let y : float = sqrt(area) in
 let z : float = sqrt((2.0 *. area) /. (1.0 +. (sqrt(3.0)))) in 
 match (kind, area) with
  | (Equilateral, _) -> (2.0 *. w, 2.0 *. w, 2.0 *. w)
  | (Isosceles, _) -> (2.0 *. y, sqrt(2.0) *. y, sqrt(2.0) *. y)
  | (Scalene, _) -> (z +. (sqrt(3.0) *. z), sqrt(2.0) *. z, 2.0 *. z)
;;


(* Question 2.3 *)
type angle = float

type tr_by_angle = side * side * angle

let sq (x : float) = x *. x

let well_formed_by_angle (a, b, gamma) : bool =
  (positive a && positive b && positive gamma) &&
    (not (is_multiple_of gamma pi))


(* sides_to_angle: 'a tr_by_sides -> 'b tr_by_angle options
   depending on validity either None or Some combo of SSA is returned *)
let sides_to_angle (a, b, c : tr_by_sides) : tr_by_angle option = 
 let (rad : float) = acos((sq a +. sq b -. sq c) /. (2.0 *. a *. b)) in 
 if not(well_formed_by_sides(a, b, c)) then None
 else Some (a, b, rad)
;;

(* angle_to_sides: 'a tr_by_angle -> 'b tr_by_sides
   using cosine law, find the third side of the triangle.*) 
let angle_to_sides (a, b, gamma : tr_by_angle) : tr_by_sides option = 
 let (some_side : float) =  sqrt(sq a +. sq b -. 2.0 *. a *. b *. cos(gamma)) in
 if not(well_formed_by_sides(a, b, some_side)) then None
 else Some (a, b, some_side)
;;



(* Now that you implemented Q2.2 and saw the new representation of
   triangles by two sides and the angle between them, also ponder on
   how one represents Q2.2 using this representation. The idea is to
   think about how the representation helps make illegal states hard
   to represent and how easy and hard it is to implement the
   algorithm. *)

(* Question 3: Flexing recursion and lists *)

let even (n : int) : bool = n mod 2 = 0
(* Question 3.1 *)

(* evens_first: 'a int list -> 'a int list 
   if the 1st int is even then add it to the acc & recurse on rest of list
   if 1st int is odd add it to the end of acc & recurse on rest of list *) 
let evens_first (l : int list) : int list =
 let rec evens_list l (acc: int list)  = match l with
  | [] -> acc
  | h::t -> if even h then evens_list t (h::acc)
            else  evens_list t (acc @ [h])
 in evens_list l [] 
;;


let ex_1 = evens_first [7 ; 5 ; 2; 4; 6; 3; 4; 2; 1]
(* val ex_1 : int list = [2; 4; 6; 4; 2; 7; 5; 3; 1] *)

(* Question 3.2 *)
(* even_streak: 'a int list -> 'a int 
   Compares a current streak of evens to a longest streak of evens. If current
   streak is greater than longest streak recurse using current streak. If streak
   hits an odd recurse with longest streak at set current streak to 0 *)
let even_streak (l : int list) : int =
 let rec streak l (longest_streak :int) (current_streak :int) : int  = 
  match l with
   | [] -> longest_streak
   | h::t -> if even h then 
              if (current_streak+1) > longest_streak 
               then streak t (current_streak+1) (current_streak+1)
              else streak t longest_streak (current_streak+1)
             else streak t longest_streak 0
 in streak l 0 0
;;

let ex_2 = even_streak [7; 2; 4; 6; 3; 4; 2; 1]

(* val ex_2 : int = 3 *)


(* Question 3.3 *)

type nucleobase = A | G | C | T

(* compress: 'l nucleobase list -> ('a int * 'b nucleobase) list 
   If nucleobase (NB) list only has 1 NB, append it to acc & increase the num
   value in its tuple. If 1st & 2nd NBs are the same, increase num value of the
   NB type & recurse on rest of list. If not the same, add only the 1st NB to 
   acc & set ctr to 0 so recursion will add a new type of NB  *)
let compress (l : nucleobase list) : (int * nucleobase) list =
 let rec compress_rec l (ctr : int) (acc : (int * nucleobase) list) = 
  match l with
   | [] -> acc
   | [h] -> (acc @ [(ctr+1,h)])
   | h1 :: (h2:: _ as t) -> if h1 = h2 then compress_rec t (ctr+1) acc 
                            else compress_rec t 0 (acc @ [(ctr+1),h1])
 in compress_rec l 0 []
;;


(* decompress: ('a int * 'a nucleobase) list -> 'b nucleobase list
   If the amount associated with a NB is greater than 1, recurse on that tuple
   until the value of that NB is < 1. If amount associated with a NB is not 
   greater than 1, then just add it to the acc and move to the next NB.*) 
let rec decompress (l : (int * nucleobase) list) : nucleobase list =
 let rec decompress_rec l (acc : nucleobase list) = match l with
  | [] -> acc
  | (num,elem) :: t -> if num > 1 
                        then decompress_rec ((num-1,elem)::t) (acc @ [elem])
                       else decompress_rec t (acc @ [elem])
 in decompress_rec l []
;;
   
let sample_dna : nucleobase list = [A;A;A;A;G;G;A;T;T;T;C;T;C]

let ex_3 = compress sample_dna

let ex_4 = decompress ex_3


let res_3_4 = sample_dna = ex_4 (* This should be true if everything went well *)
