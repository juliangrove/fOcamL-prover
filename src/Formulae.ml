open Bool
open List

(* Formulae *)

type var = Var of int

let var : int -> var = fun i -> Var i
let unvar : var -> int = fun v -> match v with Var i -> i

type name = Name of int

let name : int -> name = fun i -> Name i
let unname : name -> int = fun n -> match n with Name i -> i

type term = V of var | N of name

let v : var -> term = fun v0 -> V v0
let n : name -> term = fun n0 -> N n0

type formula =
  | Pred of int * term list
  | Top
  | Bot
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | Forall of var * formula
  | Exists of var * formula

let pred : int -> term list -> formula = fun i l -> Pred (i, l)
let ( &&& ) : formula -> formula -> formula = fun f0 f1 -> And (f0, f1)
let ( ||| ) : formula -> formula -> formula = fun f0 f1 -> Or (f0, f1)
let not' : formula -> formula = fun f0 -> Not f0
let forall : var -> formula -> formula = fun v0 f0 -> Forall (v0, f0)
let exists : var -> formula -> formula = fun v0 f0 -> Exists (v0, f0)

let fv_term : term -> var list =
 fun t -> match t with V v -> [ v ] | N n -> []

let rec fv_formula : formula -> var list =
 fun f ->
  match f with
  | Pred (_, l) -> concat (map fv_term l)
  | And (f0, f1) -> append (fv_formula f0) (fv_formula f1)
  | Or (f0, f1) -> append (fv_formula f0) (fv_formula f1)
  | Not f0 -> fv_formula f0
  | Forall (v, f0) -> filter (( != ) v) (fv_formula f0)
  | Exists (v, f0) -> filter (( != ) v) (fv_formula f0)
  | _ -> []

let names_term : term -> name list =
 fun t -> match t with V v -> [] | N n -> [ n ]

let rec names_formula : formula -> name list =
 fun f ->
  match f with
  | Pred (_, l) -> concat (map names_term l)
  | And (f0, f1) -> append (names_formula f0) (names_formula f1)
  | Or (f0, f1) -> append (names_formula f0) (names_formula f1)
  | Not f0 -> names_formula f0
  | Forall (v, f0) -> names_formula f0
  | Exists (v, f0) -> names_formula f0
  | _ -> []

let rec maximum : int list -> int =
 fun l -> match l with [] -> -1 | i :: l0 -> max i (maximum l0)

let fresh_v : var list -> var = fun vs -> var (maximum (map unvar vs) + 1)
let fresh_n : name list -> name = fun ns -> name (maximum (map unname ns) + 1)

let subst_term : var -> term -> term -> term =
 fun v0 t0 t1 -> match t1 with V v1 -> if v1 = v0 then t0 else t1 | N _ -> t1

let rec subst : var -> term -> formula -> formula =
 fun v0 t0 f0 ->
  match f0 with
  | Pred (i, l) -> pred i (map (subst_term v0 t0) l)
  | Top -> Top
  | Bot -> Bot
  | And (f1, f2) -> subst v0 t0 f1 &&& subst v0 t0 f2
  | Or (f1, f2) -> subst v0 t0 f1 ||| subst v0 t0 f2
  | Not f1 -> not' (subst v0 t0 f1)
  | Forall (v1, f1) -> (
      match v1 = v0 with
      | true -> forall v1 f1
      | false -> (
          match t0 with
          | V v2 -> (
              match v1 = v2 with
              | false -> forall v1 (subst v0 t0 f1)
              | true ->
                  let vnew = fresh_v (v1 :: fv_formula f1) in
                  let fnew = subst v1 (v vnew) f1 in
                  forall vnew (subst v0 t0 fnew))
          | N _ -> forall v1 (subst v0 t0 f1)))
  | Exists (v1, f1) -> (
      match v1 = v0 with
      | true -> exists v1 f1
      | false -> (
          match t0 with
          | V v2 -> (
              match v1 = v2 with
              | false -> exists v1 (subst v0 t0 f1)
              | true ->
                  let vnew = fresh_v (v1 :: fv_formula f1) in
                  let fnew = subst v1 (v vnew) f1 in
                  exists vnew (subst v0 t0 fnew))
          | N _ -> exists v1 (subst v0 t0 f1)))

let rec ( === ) : formula -> formula -> bool =
 fun f0 f1 ->
  match (f0, f1) with
  | Pred (i, l), Pred (j, m) -> i = j && l = m
  | Top, Top -> true
  | Bot, Bot -> true
  | And (f0, f1), And (f0', f1') -> f0 === f0' && f1 === f1'
  | Or (f0, f1), Or (f2, f3) -> f0 === f2 && f1 === f3
  | Not f0, Not f1 -> f0 === f1
  | Forall (v0, f0), Forall (v1, f1) ->
      let vnew = fresh_v (append (fv_formula f0) (fv_formula f1)) in
      let f0new = subst v0 (v vnew) f0 and f1new = subst v1 (v vnew) f1 in
      f0new === f1new
  | Exists (v0, f0), Exists (v1, f1) ->
      let vnew = fresh_v (append (fv_formula f0) (fv_formula f1)) in
      let f0new = subst v0 (v vnew) f0 and f1new = subst v1 (v vnew) f1 in
      f0new === f1new
  | _ -> false
