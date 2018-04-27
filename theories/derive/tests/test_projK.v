From elpi Require Import derive.projK.

Set Implicit Arguments.

Elpi derive.projK nat.

Lemma test_proj1S x : projS1 33 (S x) = x.
Proof. split. Qed.

Require Vector.
Arguments Vector.nil {_}.
Inductive Box A : nat -> Type :=
 | mkB (T : Type) (a : A) i (t : Vector.t T i) : Box A (S i)
 | Oops : Box A 0.

Elpi derive.projK Box.

Lemma test_projmkB1 A (a : A) d1 d2 d3 d4 :
  @projmkB1 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = bool.
Proof. split. Qed.

Lemma test_projmkB2 A (a : A) d1 d2 d3 d4 :
  @projmkB2 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = a.
Proof. split. Qed.

Lemma test_projmkB3 A (a : A) d1 d2 d3 d4 :
  @projmkB3 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) = 0.
Proof. split. Qed.

Lemma test_projmkB4 A (a : A) d1 d2 d3 d4 :
  @projmkB4 A _ d1 d2 d3 d4 (@mkB A bool a 0 Vector.nil) =
      existT (fun T => { i : nat & Vector.t T i}) bool
        (existT (fun i => Vector.t bool i) 0 Vector.nil).
Proof. split. Qed.
