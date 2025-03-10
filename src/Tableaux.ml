#use "Formulae.ml"

type signed = formula * bool
type tableau = signed list option list
type propositional_rule = signed -> signed list list
type quantifier_rule = signed list -> signed -> signed list

let and_rule : propositional_rule =
 fun sf ->
  match sf with
  | And (f0, f1), true -> [ [ (f0, true); (f1, true); sf ] ]
  | And (f0, f1), false -> [ [ (f0, false); sf ]; [ (f1, false); sf ] ]
  | _ -> [ [ sf ] ]

let or_rule : propositional_rule =
 fun sf ->
  match sf with
  | Or (f0, f1), true -> [ [ (f0, true); sf ]; [ (f1, true); sf ] ]
  | Or (f0, f1), false -> [ [ (f0, false); (f1, false); sf ] ]
  | _ -> [ [ sf ] ]

let not_rule : propositional_rule =
 fun sf ->
  match sf with
  | Not f0, true -> [ [ (f0, false); sf ] ]
  | Not f0, false -> [ [ (f0, true); sf ] ]
  | _ -> [ [ sf ] ]

let elem : signed -> signed list -> bool =
 fun sf l ->
  match find_opt (fun (f, b) -> f === fst sf && b = snd sf) l with
  | Some _ -> true
  | None -> false

let gamma_rule : quantifier_rule =
 fun sfs sf ->
  let name_t v f =
    let rec name0 i =
      if elem (subst v (n (name i)) f, true) sfs then name0 (i + 1) else name i
    in
    name0 0
  and name_f v f =
    let rec name0 i =
      if elem (subst v (n (name i)) f, false) sfs then name0 (i + 1) else name i
    in
    name0 0
  in
  match sf with
  | Forall (v0, f0), true -> [ (subst v0 (n (name_t v0 f0)) f0, true); sf ]
  | Exists (v0, f0), false -> [ (subst v0 (n (name_f v0 f0)) f0, false); sf ]
  | _ -> [ sf ]

let delta_rule : quantifier_rule =
 fun sfs sf ->
  let name_fresh = fresh_n (concat_map (fun (f, _) -> names_formula f) sfs) in
  match sf with
  | Exists (v0, f0), true -> [ (subst v0 (n name_fresh) f0, true) ]
  | Forall (v0, f0), false -> [ (subst v0 (n name_fresh) f0, false) ]
  | _ -> [ sf ]

let rec apply_rule : propositional_rule -> signed list -> signed list list =
 fun rule sfs ->
  match sfs with
  | [ (Top, true) ] -> [ [ (Top, true) ] ]
  | [] -> [ [ (Top, true) ] ]
  | sf0 :: sfs0 ->
      let just_the_first g = map (fun f -> f @ g) (rule sf0) in
      concat_map just_the_first (apply_rule rule sfs0)

let apply_quant_rule : quantifier_rule -> signed list -> signed list =
 fun rule sfs ->
  let rec apply_quant_rule0 rule0 (sfs0, sfs1) =
    match (sfs0, sfs1) with
    | [ (Top, true) ], _ -> sfs1
    | [], _ -> sfs1
    | sf2 :: sfs2, _ ->
        apply_quant_rule0 rule0
          (sfs2, append (rule0 (sf2 :: append sfs2 sfs1) sf2) sfs1)
  in
  apply_quant_rule0 rule (sfs, [ (Top, true) ])

let all_rules : signed list -> signed list list =
 fun sfs ->
  map
    (apply_quant_rule delta_rule)
    (map
       (apply_quant_rule gamma_rule)
       (concat_map (apply_rule not_rule)
          (concat_map (apply_rule and_rule) (apply_rule or_rule sfs))))

let rec contradictory : signed list -> bool =
 fun sfs ->
  match sfs with
  | [] -> false
  | (f, b) :: sfs -> elem (f, not b) sfs || contradictory sfs

let loop : tableau -> tableau =
  concat_map (fun maybesfs ->
      match maybesfs with
      | None -> [ None ]
      | Some sfs ->
          concat_map
            (fun newfs ->
              if contradictory newfs then [ None ] else [ Some newfs ])
            (all_rules sfs))
