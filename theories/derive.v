From elpi Require Import elpi.
From Coq Require Import Bool.

Elpi Init "./" "../elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

Elpi Accumulate File "coq-derive.elpi".

(* ------------------------------------------------------ *)

Elpi Run "coq-derive-eq-test {{bool}}".
Elpi Accumulate "eq-test {{bool}} {{bool_equal}}.".

Elpi Run "coq-derive-eq-test {{nat}}".
Elpi Accumulate "eq-test {{nat}} {{nat_equal}}.".

Elpi Run "coq-derive-eq-test {{prod}}".
Elpi Accumulate "
  eq-test (app [{{prod}}, A, B]) (app [{{prod_equal}}, A, F, B, G]) :-
    eq-test A F, eq-test B G.".

Inductive weird :=
  | W1 (w : nat * bool * nat).

(* Elpi Trace. *)

Elpi Run "coq-derive-eq-test {{weird}}".
Elpi Accumulate "eq-test {{weird}} {{weird_equal}}.".

Eval compute in
  weird_equal (W1 (3,true,2)) (W1 (3,true,2)).
Eval compute in
  weird_equal (W1 (3,true,2)) (W1 (3,true,22)).

Print weird_equal.

(* ------------------------------------------------------ *)

Elpi Trace.

Elpi Run "coq-derive-induction {{nat}}".
Print nat_induction.

Elpi Run "coq-derive-induction {{list}}".
Print list_induction.