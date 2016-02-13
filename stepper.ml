(* This is a stepper implemented using shift and reset *)

(* terms and values *)

type value_t =
  Num of int
| Bool of bool
| Var of string
| Lam of string * term_t
| Fix of string * term_t  (* internal representation of recursive functions *) 
| Empty
| VCons of value_t * value_t

(* arithmetic operations *)
and aop_t =
  Plus | Minus | Times | Div

(* comparison operations *)
and cop_t =
  Eq | Less | Great | LessEq | GreatEq

and term_t =
  Value of value_t
| App of term_t * term_t
| AOp of term_t * aop_t * term_t 
| COp of term_t * cop_t * term_t 
| If of term_t * term_t * term_t
| Let of string * term_t * term_t
| LetRec of string * term_t * term_t
| Cons of term_t * term_t
| Match of term_t * (term_t * term_t) list
| Redex of term_t ;;  (* for highlighting redexes *)

(* a list of recursive functions defined so far *)
let rfun = ref [] ;;

(* for renaming functions *)
let counter = ref 0 ;;
let gensym () =
  counter := !counter + 1;
  "f" ^ string_of_int !counter ;;

(* check if there already exists a function whose name is f *)
(* not_contain : (string * term_t) list -> bool *)
let rec not_contain f rfuns = match rfuns with
  [] -> true
| (name, exp) :: rest -> if name = f then false
			   else not_contain f rest ;;

(* substitution *)
(* subst : term_t -> string -> term_t -> term_t *)
let rec subst e x e' = match e with
  Value (Num (n)) -> e
| Value (Bool (b)) -> e
| Value (Var (y)) -> if y = x then e' else e
| Value (Lam (x, e2)) -> 
   if (not (x = x)) 
   then Value (Lam (x, subst e2 x e'))
   else e
| Value (Fix (f, e2)) -> Value (Fix (f, subst e2 x e'))
| Value (Empty) -> e
| Value (VCons (first, rest)) ->
   (match (subst (Value (first)) x e', subst (Value (rest)) x e') with
      (Value (f), Value (r)) -> Value (VCons (f, r)))
| App (e1, e2) -> App (subst e1 x e', subst e2 x e')
| AOp (n1, op, n2) -> AOp (subst n1 x e', op, subst n2 x e')
| COp (x1, op, x2) -> COp (subst x1 x e', op, subst x2 x e')
| If (e1, e2, e3) -> If (subst e1 x e', subst e2 x e', subst e3 x e')
| Let (name, e1, e2) -> 
   if (not (name = x))
   then Let (name, subst e1 x e', subst e2 x e')
   else Let (name, e1, e2)
| LetRec (name, e1, e2) -> 
   if (not (name = x))
   then LetRec (name, subst e1 x e', subst e2 x e')
   else LetRec (name, e1, e2)
| Cons (first, rest) -> Cons (subst first x e', subst rest x e')
| Match (e, list) -> Match (subst e x e',
			    map (fun (a, b) -> 
				 (subst a x e', subst b x e')) list)
| Redex (e) -> Redex (subst e x e') ;;
  
(* evaluate arithmetic operations *)
(* eval_aop : aop -> int -> int -> int *)
let eval_aop op n1 n2 = match op with
  Plus -> n1 + n2
| Minus -> n1 - n2
| Times -> n1 * n2
| Div -> n1 / n2 ;;
  
(* evaluate comparison operations *)
(* eval_cop : cop -> term_t -> bool *)
let eval_cop op x y = match (x, y) with
  (Value (Num (n1)), Value (Num (n2))) -> 
   begin match op with
     Eq -> n1 = n2
   | Less -> n1 < n2
   | Great -> n1 > n2
   | LessEq -> n1 <= n2
   | GreatEq -> n1 >= n2
   end 
| (Value (Bool (b1)), Value (Bool (b2))) ->
   begin match op with
     Eq -> b1 = b2
   | Less -> b1 < b2
   | Great -> b1 > b2
   | LessEq -> b1 <= b2
   | GreatEq -> b1 >= b2
   end ;;
  
(* find a matching case of the given pattern *)
(* find_match : term_t -> term_t list -> term_t *)
let rec find_match v lst = match v with
  Value (Empty) ->
   begin match lst with
     (Value (Empty), expr) :: rest -> expr
   | _ :: rest -> find_match v rest
   end
| Value (VCons (f1, r1)) -> 
   begin match lst with
     (Value (VCons (Var (f), Var (r))), expr) :: rest -> 
      subst (subst expr f (Value (f1))) r (Value (r1))
   | _ :: rest -> find_match v rest
   end ;;

(* store each intermediate program *)
(* memo : 'a -> (unit => 'a) => 'a *)
let memo e f = 
  shift (fun k -> fun lst -> (reset (fun () -> k (f ()))) 
			     (k e lst)) ;;
(* to highlight redexes, replace (k e lst) by (k (Redex e) lst) *)

(* stepping interpreter *)
(* stepper : term_t => term_t *)
let rec stepper exp = match exp with
  Value (Num (n)) -> exp
| Value (Bool (b)) -> exp
| Value (Var (v)) -> exp
| Value (Lam (x, body)) -> exp
| Value (Fix (f, body)) -> exp
| Value (Empty) -> exp
| Value (VCons (first, rest)) -> exp
				   
| App (e1, e2) ->
   let a1 = stepper e1 in
   begin match a1 with
     Value (Lam (x, body)) -> 
     let a2 = stepper e2 in
     begin match a2 with
       Value (Var (x)) -> App (a1, a2)
     | Value (v) -> 
	memo (App (a1, a2)) (fun () ->
	stepper (subst body x a2))
     | _ -> App (a1, a2)
     end 
   | Value (Fix (f, Value (Lam (x, body)))) ->
      let a2 = stepper e2 in
      begin match a2 with
	Value (Var (x)) -> App (a1, a2)
      | Value (v) -> 
	 memo (App (a1, a2)) (fun () ->
         stepper (subst 
		    (subst body x a2)
		    f (Value (Fix (f, Value (Lam (x, body)))))))
      | _ -> App (a1, a2)
      end
   | _ -> App (a1, e2)
   end

  | AOp (n1, op, n2) -> 
     let a1 = stepper n1 in
     begin match a1 with
       Value (Num (v1)) ->
       let a2 = stepper n2 in
       begin match a2 with
         Value (Num (v2)) ->
	 memo (AOp (a1, op, a2)) (fun () ->
         Value (Num (eval_aop op v1 v2)))
       | _ -> AOp (a1, op, a2)
       end
     | _ -> AOp (a1, op, n2)
     end

  | COp (x1, op, x2) -> 
     let a1 = stepper x1 in
     begin match a1 with
       Value (Num (v1)) ->
       let a2 = stepper x2 in
       begin match a2 with
	 Value (Num (v2)) ->
	 memo (COp (a1, op, a2)) (fun () ->
         Value (Bool (eval_cop op a1 a2)))
       | _ -> COp (a1, op, a2)
       end
     | Value (Bool (v1)) -> 
        let a2 = stepper x2 in
        begin match a2 with
	  Value (Bool (v2)) ->
	  memo (COp (a1, op, a2)) (fun () ->
	  Value (Bool (eval_cop op a1 a2)))
        | _ -> COp (a1, op, a2)
	end 
     | _ -> COp (a1, op, x2)
     end 

  | If (e1, e2, e3) -> 
     let a1 = stepper e1 in
     begin match a1 with
       Value (Bool (v)) -> 
       memo (If (Value (Bool (v)), e2, e3)) (fun () ->
       if v then stepper e2 else stepper e3)
     | _ -> If (a1, e2, e3)
     end

  | Let (name, e1, e2) ->
     let a1 = stepper e1 in
     memo (Let (name, a1, e2)) (fun () ->
     stepper (subst e2 name a1))

  | LetRec (name, e1, e2) ->
     if (not_contain name !rfun)  (* if the name is fresh *)
     then (rfun := (name, e1) :: !rfun;  (* extend rfun with the new function *)
     stepper (subst e2 name (Value (Fix (name, e1)))))
     else (let f = gensym () in  (* creat a new name *)
	   rfun := (f, subst e1 name (Value (Var (f)))) :: !rfun; 
	   stepper (subst e2 name 
		        (Value (Fix (f, (subst e1 name (Value (Var (f)))))))))
             
  | Cons (first, rest) ->
     let f = stepper first in
     begin match f with
       Value (v) -> 
       let r = stepper rest in
       begin match r with
	 Value (Empty) ->
	  Value (VCons (v, Empty))
       | Value (VCons (f2, r2)) -> 
	  Value (VCons (v, (VCons (f2, r2))))
       | _ -> Cons (f, r)
       end
     | _ -> Cons (f, rest)
     end

  | Match (e, list) ->
     let a = stepper e in
     begin match a with
       Value (v) -> 
	memo (Match (a, list)) (fun () ->
        stepper (find_match a list))
     | _ -> Match (a, list)
     end ;;

(* to_string functions *)

(* convert arithmetic operators to a string *)
(* aop_to_string : aop_t -> string *)
let aop_to_string op = match op with
  Plus -> " + "
| Minus -> " - "
| Times -> " * "
| Div -> " / " ;;

(* convert comparison operators to a string *)
(* cop_to_string : cop_t -> string *)
let cop_to_string op = match op with
  Eq -> " = "
| Less -> " < "
| Great -> " > "
| LessEq -> " <= "
| GreatEq -> " >= " ;; 

(* convert terms into a string *)
(* to_string : term_t -> string *)
let rec to_string e = match e with
  Value (Num (n)) -> string_of_int n
| Value (Bool (b)) -> string_of_bool b
| Value (Var (x)) -> x
| Value (Lam (x, body)) -> "(fun " ^ x ^ " -> " ^ to_string body ^ ")"
| Value (Fix (f, body)) -> f
| Value (Empty) -> "[]"
| Value (VCons (first, rest)) ->
   "(" ^ to_string (Value (first)) ^ " :: " ^ to_string (Value (rest)) ^ ")"
| App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
| AOp (n1, op, n2) -> 
   "(" ^ to_string n1 ^ aop_to_string op ^ to_string n2 ^ ")"
| COp (x1, op, x2) -> 
   "(" ^ to_string x1 ^ cop_to_string op ^ to_string x2 ^ ")"
| If (e1, e2, e3) -> "(" ^ "if " ^ to_string e1 ^ 
		       " then " ^ to_string e2 ^
			 " else " ^ to_string e3 ^ ")"
| Let (name, e1, e2) -> "let " ^ name ^ " = " ^
			  to_string e1 ^ " in " ^ to_string e2
| LetRec (name, e1, e2) -> "let rec " ^ name ^ " = " ^
			     to_string e1 ^ " in " ^ to_string e2
| Cons (first, rest) -> "(" ^ to_string first ^ " :: " ^ to_string rest ^ ")"
| Match (e', list) -> "(match " ^ to_string e' ^ " with" ^ 
			match_to_string list ^ ")"
| Redex (e') -> "(" ^ to_string e' ^ "[@stepper.redex]" ^ ")" 
(* for highlighting the redex *)
							    
(* to_string for match expressions *)
(* match_to_string : (term_t * term_t) list -> string *)
and match_to_string list = match list with
  [] -> ""
| (a, b) :: rest -> " | " ^ to_string a ^ " -> " ^ to_string b ^ 
		      match_to_string rest ;;

(* to_string for recursive functions *)
(* necessary for avoiding free occurrences of the name of recursive functions *)
(* rec_to_string : (string * term_t) list -> string *)
let rec rec_to_string rfuns = match rfuns with
  [] -> ""
| (f, body) :: rest -> rec_to_string rest ^
			 "let rec " ^ f ^ " = " ^ 
			   to_string body ^
			     " in " ;;

(* same as List.map *)
(* map : ('a -> 'b) -> 'a list -> 'b list *)
let rec map f lst = match lst with
  [] -> []
| first :: rest -> f first :: map f rest ;;

(* start stepping execution *)
(* go : term_t -> string list *)
let go exp = 
  rfun := [];  (* initialize rfun *)
  map (fun x -> (rec_to_string !rfun) ^ x)  
      (* print the recursive functions defined so far *)
      (map to_string
	   (reset (fun () -> 
		   let res = stepper exp in
		   fun lst -> res :: lst) [])) ;;

(* factorial *)
let fac3 = 
  LetRec ("fac", 
	  Value (Lam ("n", 
		      If (COp (Value (Var ("n")), Eq, Value (Num (0))), 
			  Value (Num (1)), 
			  AOp (Value (Var ("n")), Times, 
			       App (Value (Var ("fac")), 
				    AOp (Value (Var ("n")), Minus, 
					 Value (Num (1)))))))), 
	  App (Value (Var ("fac")), Value (Num (3)))) ;;

go fac3 ;;
