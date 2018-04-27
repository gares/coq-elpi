From elpi Require Import elpi.


Theorem fg_equal :
  forall (A B : Type) (f g : A -> B) (x y : A),
    x = y -> f = g -> f x = g y.
Proof.
  intros A B f g x y Hxy Hfg.
  rewrite <- Hxy. rewrite <- Hfg.
  reflexivity.
Qed.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).


Inductive LVar A :=
| VLow : A -> LVar A
| VHigh : A -> LVar A.

Inductive LamC (A : Type) :=
| App : LamC A -> LamC A -> LamC A
| Abs : LamC (LVar A) -> LamC A
| Var : A -> LamC A.

Inductive NList (A : Type) :=
| NCons : NList (A*A) -> NList A
| NNil.

Inductive MList (A B : Type) :=
| MCons : A -> B -> MList A B -> MList A B
| MNil : MList A B.

Inductive MTree (A : Type) :=
| MNode : MList A (MTree (A * A)) -> MTree A.

Inductive Tp (A B C D : Type) :=
| C : Tp A (B*B) C (list D) -> Tp A B C D
| C2 : A -> B -> C -> D -> Tp A B C D.

Elpi Command test.gen. 

Elpi Accumulate File "attic/derive-poly.elpi".

Elpi Accumulate File "attic/derive-poly-eq.elpi". 
Elpi Query "derive-eq ""prod"".".
Elpi Accumulate "eq-set ""prod"".".
Elpi Query "derive-eq ""list"".".
Elpi Accumulate "eq-set ""list"".".
Elpi Query "derive-eq ""Tp"".".
Elpi Accumulate "eq-set ""Tp"".".
Elpi Query "derive-eq ""MList"".".
Elpi Accumulate "eq-set ""MList"".".
Elpi Query "derive-eq ""MTree"".".
Elpi Accumulate "eq-set ""MTree"".".
Check MTree_equal.
Print MTree_equal.

Elpi Accumulate File "attic/derive-poly-map.elpi".
Elpi Query "derive-map ""prod"".".
Elpi Accumulate "map-set ""prod"".".
Elpi Query "derive-map ""list"".".
Elpi Accumulate "map-set ""list"".".
Elpi Query "derive-map ""Tp"".".
Elpi Accumulate "map-set ""Tp"".".
Elpi Query "derive-map ""MList"".".
Elpi Accumulate "map-set ""MList"".".
Elpi Query "derive-map ""MTree"".".
Elpi Accumulate "map-set ""MTree"".".
Check MTree_map.
Print MTree_map.
