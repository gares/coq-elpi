From elpi Require Export derive.projK.

(** A tactic pushing an equation under a constructor *)

Elpi Tactic injection.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate "
  solve [trm E] [goal Ctx _ _ _ as G] NG :- !,
    Ctx => (of E Eq ER, !, injection ER Eq _ P),
    if (P = []) (coq.error ""Could not generate new equations"")
       (refine (app[hole|P]) G NG).

  solve _ _ _ :- usage.

  usage :- coq.error ""Usage: injection <equation>"".
".
Elpi Typecheck.
