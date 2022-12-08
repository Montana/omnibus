let fst (v : int list * bool) = match v with
          | (x, y) -> x
let snd (v : int list * bool) = match v with
          | (x, y) -> y

let rec sorted (xs:int list) = match xs with 
                 | [] -> true
                 | x::m -> match m with
                   | [] -> true
                   | y::n -> x <= y && sorted m

contract bsorthelper = {x | true} -> {y | (snd y) || sorted (fst y)} 
(* val bsorthelper : int list -> (int list, bool) *)
let rec bsorthelper (xs: int list) = match xs with
| [] -> ([], false)
| (a::l) -> begin match l with
  | [] -> ([a], false)
  | (x::m) -> begin 
      match bsorthelper l with
      | (ys, changed) -> begin match ys with
	        | [] -> ([], false)
                | (y::n) -> if a <= y then (a::(y::n), changed)
                 else (y::(a::n), true)
		  end
               end
            end

contract bubblesort = {x| true} -> {y | sorted y} 
let rec bubblesort (xs : int list) : int list = 
  match bsorthelper xs with
  | (result, changed) ->
      if changed then bubblesort result
      else result
