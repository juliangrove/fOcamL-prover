#use "Formulae.ml";;
#use "Tableaux.ml";;

let depth : int -> signed list -> bool = fun n sfs ->
  let rec times n f x = match n with
      0 -> x
    | n -> f (times (n - 1) f x) in
  for_all ((=) None) (times n loop [Some sfs])

let entails : int -> formula list -> formula -> bool = fun n fs f ->
  depth n ((f, false) :: map (fun f0 -> (f0, true)) fs)

(* Just for fun: *)

let imp f0 f1 = (not' f0) ||| f1

let transitivity = forall (var 0) (forall (var 1) (forall (var 2) (imp ((pred 0 [v (var 0); v (var 1)]) &&& (pred 0 [v (var 1); v (var 2)])) (pred 0 [v (var 0); v (var 2)]))))

let hyp1 = pred 0 [n (name 0); n (name 1)]
let hyp2 = pred 0 [n (name 1); n (name 2)]
let hyp3 = pred 0 [n (name 0); n (name 2)]

let animate a = pred 0 [a]
let see a b = pred 1 [a; b]
let see_animate = forall (var 1) (imp (exists (var 0) (see (v (var 0)) (v (var 1)))) (animate (v (var 1))))
