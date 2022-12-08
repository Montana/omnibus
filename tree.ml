(* val max : int -> int -> int *)
let max (x:int) y = if x >= y then x else y

type tree = L | N of int * tree * tree

type idxtree = IL | IN of (int * int list * string) * idxtree * idxtree

(* val depth : tree -> int *)
(* contract depth = {t | true} -> {y | y >=0} *)
let rec depth t = match t with 
| L -> 0
| N(x, t1, t2) -> (max (depth t1) (depth t2)) + 1

axiom depth : forall t: tree. depth t >= 0

(* val abs : int -> int *)
contract abs = {x | true} -> {y | y >=0}
let abs x = if x >= 0 then x else 0-x

axiom depth2 : forall t, u, t1, t2: tree. forall x:int. 
                (t = N(x, t1, t2) && abs(depth t1 - depth t2) <= 1 &&
                depth t - depth u > 1) -> not(depth t1 = depth t2)

(* val notL : tree -> bool *)
let notL a = match a with
| L -> false
| N (x,t1,t2) -> true

axiom depth_notL : forall t: tree.  depth t > 0 -> notL t

let rec map f xs = match xs with
              | [] -> []
              | (h::t) -> f h :: map f t

let rec append xs ys = match xs with
| [] -> ys
| x::l -> x :: append l ys

let rec flatten xs = match xs with
  | [] -> []
  | l::r -> append l (flatten r)

let not x = if x then false else true

let null xs = match xs with
    [] -> true
  | (h::t) -> false

contract tail = {xs | not (null xs)} -> {r | true} 
let tail (xs: (int * int list * string) list list) = match xs with 
             | (h::t) -> t
	     | [] -> failwith "tail"

(* 


              31               E
                /                               \
      15        A                               F
       /               \               /               \
  7    X       15      B       15      G       15      I
   /       \       /       \       /       \       /       \
 3 L   7   L   7   L   7   C   7   L   7   H   7   J   7   K 
 /   \   /   \   /   \   /   \   /   \   /   \   /   \   /   \
 L   L   L   L   L   L   L   L   L   L   L   L   L   L   L   M
/ \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \ / \
L L L L L L L L L L L L L L L L L L L L L L L L L L L L L L L L

*)

let int_string i = match i with
  | 0 -> "X"
  | 1 -> "A"
  | 2 -> "B"
  | 3 -> "C"
  | 4 -> "E"
  | 7 -> "F"
  | 5 -> "G"
  | 6 -> "H"
  | 9 -> "I"
  | 8 -> "J"
  | 10 -> "K"
  | 11 -> "M"
  | others -> "Z"

let avl1 = N(4, N(1, N(0, L, L), N(2, L, N(3, L, L))),
                N(7, N(5, L, N(6, L, L)), N(9, N(8, L, L), N(10, L, N(11, L, L)))))


let rec print_space n = if n <= 0 then print_string ""
                    else begin print_string " "; print_space (n-1) end


let rec width t = match t with
   | L -> 2
   | N(v, t1, t2) -> 1 + width t1 + width t2

let rest_of_tree t = match t with
  | IL -> []
  | IN(v,t1, t2) -> [t1;t2]

let root_of_tree t = match t with
  | IL -> []
  | IN(v,t1,t2) -> [v]

let rec digit_to_num xs = match xs with
 | [] -> 0
 | x::l -> x + 2*digit_to_num l

(* let _ = print_int (digit_to_num [0;1;1;1;1]) *)

let rec idx_avl t db s = match t with
   | L -> IN ((db, s,"L"), IL, IL)
   | N(v,t1,t2) -> IN((db, s, int_string v), 
                       idx_avl t1 (db-1) (0::s),
                       idx_avl t2 (db-1) (1::s))

let rec avl_to_list ts = match ts with
   | [] -> []
   | x::l -> 
   let level_one = flatten (map root_of_tree ts) in
   level_one::(avl_to_list (flatten (map rest_of_tree ts)))

let rec power m n = if n <= 0 then 1
      else m*power m (n-1)

let rec print_branches ts b vb pre = match ts with
  | [] -> print_string ""
  | (d,idx,v)::l -> 
     let n = digit_to_num idx in 
     let gap = n - pre in
     let w = if gap = 1 then power 2 (d+1)  - 1
             else if pre = 0 
                    then (power 2 d) - 1 + gap*(power 2 (d+1)) 
		    else power 2 (d+1)  - 1 + (gap-1)*(power 2 (d+1)) in
     let br = if vb then v
              else if b then "/" else "\\" in
     print_space w; 
     (* print_int w; *)
     print_string br;
     print_branches l (not b) vb n

let rec print_int_list xs = match xs with
  | [] ->  print_string ""
  | x::l -> print_int x; print_int_list l
     
let rec print_avl_list tss = match tss with
   | [] -> print_string ""
   | ts::l -> 
              begin
       	      print_branches ts true false 0;
              print_string "\n";
      	      print_branches ts true true 0;
              print_string "\n";
              print_avl_list l
	      end
  
let print_avl t = 
  let d = depth t in
  let w = (power 2 d) - 1 in 
  let ts = avl_to_list [(idx_avl t d [])] in
  match ts with
  | [] -> print_string "\n"
  | x::l -> begin match l with
   | [] -> print_string "L"
   | y::z -> begin print_space w; 
     (* print_int w; *)
     (match t with | L -> print_string "L" 
                   | N (v, t1, t2) -> print_string (int_string v));
	     print_string "\n";
             print_avl_list l
       end
   end

let nothing = print_avl avl1; print_string "\n"
 
         
(* val btmax : tree -> int *)
contract btmax = {t | notL t} -> {y | true}
let rec btmax t = match t with
| N(x, t1, t2) -> begin match t2 with 
  | L -> x
  | N(x, t21, t22) -> btmax t2
  end
| L -> failwith "btmax"

(* val btmin :: tree -> int *)
contract btmin = {t | notL t} -> {y | true}
let rec btmin t = match t with
| N(x, t1, t2) -> begin match t1 with
  | L -> x
  | N(x, t11, t12) -> btmin t1
	end
| L -> failwith "btmin"


(* val balanced : tree -> bool *)
let rec balanced a = match a with 
| L -> true
| N(x, t, u) -> balanced t && balanced u &&
              abs (depth t - depth u) <= 1

(* val rrotate : tree -> tree *)
let pre_rrotate x = match x with
| N (v, t1, t2) -> depth t1 > depth t2
| L -> true

(* contract rrotate = {x | pre_rrotate x} -> 
	   	 {y | 0 <= depth x - depth y && depth x - depth y <= 1} *)
let rrotate w = match w with
| N (v, t1, t2) -> begin match t1 with
   | N (x, l, r) -> N (x, l, N (v, r, t2))
   | L -> w (* failwith "rrotate L1" *)
  end
| L -> L (* failwith "rrotate L" *)

(* val lrotate : tree -> tree *)
let pre_lrotate x = match x with
| N (v, t1, t2) -> depth t1 < depth t2
| L -> true

(* contract lrotate = {x | pre_lrotate x} -> 
	           {y | 0 <= depth x - depth y && depth x - depth y <= 1} *)
let lrotate w = match w with
| N (v, t1, t2) -> begin match t2 with
  | N (x, l, r) -> N (x, N (v, t1, l), r)
  | L -> w (* failwith "lrotate L2" *)
  end
| L -> L (* failwith "lrotate L" *)


(* val insert : tree -> int -> tree *)
contract insert = {w | balanced w} -> {y | true} ->
{v | notL v && balanced v && 0 <= depth v - depth w && depth v - depth w <= 1} 

let rec insert w i = match w with
| L -> N(i, L, L)
| N(v, t, u) -> 
  if i < v 
  then let t1 = insert t i in
       if depth t1 - depth u > 1 
       then match t1 with
            | L -> failwith "insert L"
            | N(x, l, r) -> if depth l > depth r 
                            then rrotate (N (v, t1, u))
                            else if depth l < depth r 
			         then rrotate (N (v, lrotate t1, u))
			         else failwith "insert: impossible1"
       else N(v, t1, u)
  else if i > v 
       then let u1 = insert u i in 
            if depth u1 - depth t > 1 
            then match u1 with
		 | L -> failwith "insert L"
                 | N(x, l, r) -> 
		     if depth r > depth l
                     then lrotate (N (v, t, u1))
                     else if depth r < depth l
			  then lrotate (N (v, t, rrotate u1))
		          else failwith "insert: impossible2"
            else N(v, t, u1)
       else N(v, t, u)

contract delete = {w | balanced w} -> {y | true} -> 
         {v | balanced v && 0 <= depth w - depth v && depth w - depth v <= 1} 
(* val delete : tree -> int -> tree *)
let rec delete v1 i = match v1 with
| L -> L
| N(v, t, u) -> begin match t with
   | L ->  if i = v then u
           else let u1 = delete u i in
	        N(v, L, u1)
   | N(y, l3, r3) -> 
          begin match u with
	  | L -> if i = v then t
                 else let t1 = delete t i in 
                      N(v, t1, L)
          | N(z, l4, r4) ->
    if i = v
    then begin 
         if depth t > depth u 
         then let tmax = btmax t in
	      let t1 = delete t tmax in 
              N (tmax, t1, u) 
         else begin 
              let umin = btmin u in
	      let u1 = delete u umin in 
              N (umin, t, u1)
              end
         end
    else if i < v 
         then begin 
	      let t1 = delete t i in
              let t2 = insert t1 v in
	      let umin = btmin u in
              let u1 = delete u umin in 
              if depth u - depth t1 > 1 
               then if depth u1 - depth t2 <= 1 
                    then N (umin, t2, u1)
                    else match u1 with
		         | L -> N (umin, t2, L)
                         | N(x, l5, r5) -> 
			     if depth r5 > depth l5 
                             then lrotate (N (umin, t2, u1))
                             else lrotate (N (umin, t2, rrotate u1)) 
               else N(v, t1, u)
               end
         else begin 
	      let u1 = delete u i in
              let u2 = insert u1 v in
	      let tmax = btmax t in
              let t1 = delete t tmax in
              if depth t - depth u1 > 1 
              then if depth t1 - depth u2 <= 1 
                   then N (tmax, t1, u2)
                   else match t1 with
		        | L -> N(tmax, L, u2)
                        | N(x, l6, r6) ->
                           if depth l6 > depth r6 
                            then rrotate (N (tmax, t1, u2))
                            else rrotate (N (tmax, lrotate t1, u2)) 
              else N(v, t, u1)
              end
          end
      end
                    
let _ =  print_avl (delete avl1 0); print_string "\n";
