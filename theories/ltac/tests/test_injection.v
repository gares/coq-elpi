From elpi Require Import elpi.
From elpi Require Import ltac.discriminate.
From elpi Require Import ltac.injection.

Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test_nat (a b :nat) : S a = S b -> a = b.
Proof.
intro H.
elpi injection (H).
intro I.
exact I.
Qed.

Require Vector.
Require Import ssreflect Arith.

Elpi derive.projK Vector.t.


Lemma test_vect A a b n (v1 v2 : Vector.t A n) :
  Vector.cons A a n v1 = Vector.cons A b n v2 -> a = b /\ v1 = v2.
Proof.
intro H.
elpi injection (H).
move=> /= Eab _ Esigv12.
split.
  exact Eab.
rewrite -[v2](projT2_eq Esigv12) /=.
by rewrite (UIP_nat _ _ (projT1_eq Esigv12) (eq_refl n)).
Qed.