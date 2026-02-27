
type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type 'a list =
| Nil
| Cons of 'a * 'a list

type form =
| F_Bot
| F_Imp of form * form

(** val form_eqb : form -> form -> bool **)

let rec form_eqb a b =
  match a with
  | F_Bot -> (match b with
              | F_Bot -> True
              | F_Imp (_, _) -> False)
  | F_Imp (a1, a2) ->
    (match b with
     | F_Bot -> False
     | F_Imp (b1, b2) ->
       (match form_eqb a1 b1 with
        | True -> form_eqb a2 b2
        | False -> False))

(** val is_K : form -> bool **)

let is_K = function
| F_Bot -> False
| F_Imp (a, f) ->
  (match f with
   | F_Bot -> False
   | F_Imp (_, a') -> form_eqb a a')

(** val is_EFQ : form -> bool **)

let is_EFQ = function
| F_Bot -> False
| F_Imp (f, _) -> (match f with
                   | F_Bot -> True
                   | F_Imp (_, _) -> False)

(** val is_S : form -> bool **)

let is_S = function
| F_Bot -> False
| F_Imp (f, f0) ->
  (match f with
   | F_Bot -> False
   | F_Imp (a, f1) ->
     (match f1 with
      | F_Bot -> False
      | F_Imp (b, c) ->
        (match f0 with
         | F_Bot -> False
         | F_Imp (f2, f3) ->
           (match f2 with
            | F_Bot -> False
            | F_Imp (a1, b1) ->
              (match f3 with
               | F_Bot -> False
               | F_Imp (a2, c2) ->
                 (match match form_eqb a a1 with
                        | True -> form_eqb a a2
                        | False -> False with
                  | True ->
                    (match form_eqb b b1 with
                     | True -> form_eqb c c2
                     | False -> False)
                  | False -> False))))))

(** val is_axiom : form -> bool **)

let is_axiom phi =
  match is_EFQ phi with
  | True -> True
  | False -> (match is_K phi with
              | True -> True
              | False -> is_S phi)

type proof = form list

(** val existsb_local : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb_local p = function
| Nil -> False
| Cons (x, xs') ->
  (match p x with
   | True -> True
   | False -> existsb_local p xs')

(** val mp_witness : form list -> form -> bool **)

let mp_witness ctx phi =
  existsb_local (fun psi ->
    existsb_local (fun chi ->
      match chi with
      | F_Bot -> False
      | F_Imp (x, y) ->
        (match form_eqb x psi with
         | True -> form_eqb y phi
         | False -> False)) ctx) ctx

(** val check_lines : form list -> proof -> bool **)

let rec check_lines ctx = function
| Nil -> True
| Cons (line, rest) ->
  let ok_line =
    match is_axiom line with
    | True -> True
    | False -> mp_witness ctx line
  in
  (match ok_line with
   | True -> check_lines (Cons (line, ctx)) rest
   | False -> False)

(** val last_opt : proof -> form option **)

let rec last_opt = function
| Nil -> None
| Cons (x, xs) -> (match xs with
                   | Nil -> Some x
                   | Cons (_, _) -> last_opt xs)

(** val check : proof -> form -> bool **)

let check pf goal =
  match last_opt pf with
  | Some last ->
    (match check_lines Nil pf with
     | True -> form_eqb last goal
     | False -> False)
  | None -> False

(** val checker : proof -> form -> bool **)

let checker =
  check

(** val cubic_accepts : proof -> form -> bool **)

let cubic_accepts =
  checker
