
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

val form_eqb : form -> form -> bool

val is_K : form -> bool

val is_EFQ : form -> bool

val is_S : form -> bool

val is_axiom : form -> bool

type proof = form list

val existsb_local : ('a1 -> bool) -> 'a1 list -> bool

val mp_witness : form list -> form -> bool

val check_lines : form list -> proof -> bool

val last_opt : proof -> form option

val check : proof -> form -> bool

val checker : proof -> form -> bool

val cubic_accepts : proof -> form -> bool
