From Coq Require Import ZArith List String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition var_count : nat := 18712.
Definition base : Z := 5.
Definition channel_count : nat := 6675.
Definition bound_n_lines : nat := 3.
Definition bound_digit_width : nat := 16.
Definition bound_max_repr_lane : nat := 7.
Definition bound_max_repr_full : nat := 2583.
Definition expected_max_degree : nat := 3.
Definition expected_has_degree_3 : bool := true.
Definition expected_count_degree_3_monomials : nat := 1175.
Definition encoding_scheme : string := "zeckendorf".
Definition pairing_layout : string := "gap4".
Definition successor_scheme : string := "nat_plus_one_eq".
Definition debug_nonadjacency_disabled : bool := false.
Definition max_coeff_digits : nat := 198.
Definition coeff_hash : string := "d9aa866a5b204698387592ee24d4bf011cd45fdc16c3be01a9faf855d7ba6d05".

Record monom := { coeff : Z; exps : list (nat * nat) }.
