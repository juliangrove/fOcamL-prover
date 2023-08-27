#use "Formulae.ml";;
#use "Tableaux.ml";;

let depth : int -> signed list -> bool = fun n sfs ->
  let rec times n f x = match n with
      0 -> x
    | n -> f (times (n - 1) f x) in
  for_all ((=) None) (times n loop [Some sfs])

let entails : int -> formula list -> formula -> bool = fun n fs f ->
  depth n ((f, false) :: map (fun f0 -> (f0, true)) fs)

let imp f0 f1 = not' f0 ||| f1
let see a b = pred 0 [a; b]
let animate a = pred 1 [a]
let see_animate = forall (var 0) (forall (var 1) (imp (see (v (var 0)) (v (var 1))) (animate (v (var 1)))))
