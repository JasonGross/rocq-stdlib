(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Bounded natural numbers [fin n], the new interface for [Fin.t].

    This file is the replacement for [Vectors.Fin]. The module [Fin] now
    defines its interface as deprecated notations for the definitions here
    when the two agree. Reasoning about [fin] goes through [to_nat] and
    small inversions ([inj_0], [inj_S]) instead of dependent elimination. *)

From Stdlib Require Import PeanoNat Peano_dec.
Local Open Scope nat_scope.

Inductive fin : nat -> Type :=
| finO {n}             : fin (S n)
| finS {n} (_ : fin n) : fin (S n).
Abbreviation t := fin (only parsing).
Abbreviation fin0 := finO (only parsing).

Fixpoint to_nat {n} (i : fin n) : nat :=
  match i with
  | finO => 0
  | finS i => S (to_nat i)
  end.
Coercion to_nat : fin >-> nat.

Definition cast {m} (v: t m) {n} : m = n -> t n :=
  match Nat.eq_dec m n with
  | left Heq => fun _ => eq_rect m _ v n Heq
  | right Hneq => fun Heq => False_rect _ (Hneq Heq)
  end.

Fixpoint add_nat (n : nat) [m] (i : fin m) {struct n} : fin (n + m) :=
  match n with
  | 0 => i
  | S n => finS (add_nat n i)
  end.

Section Relax.
Context (n : nat).
Fixpoint relax {m} (i : fin m) : fin (m + n) :=
  match i in fin m return fin (m + n) with
  | finO => finO
  | finS i => finS (relax i)
  end.
End Relax.

Lemma of_nat_subproof n i : i < n -> i + S (n - S i) = n.
Proof.
  intros H. rewrite Nat.add_succ_r, <-Nat.add_succ_l, Nat.add_comm.
  apply Nat.sub_add, H.
Qed.

Definition of_nat n (i : nat) (H : i < n) : fin n :=
  cast (add_nat i (@fin0 (n-S i))) (of_nat_subproof n i H).

Lemma inj_0 (i : fin 0) : False.
Proof. exact (match i with end). Qed.

Lemma inj_S {n} (i : t (S n)) : i = finO \/ exists j, i = finS j.
Proof.
  pattern i; refine ( (* destruct i, but using elaborator's small inversions *)
  match i in fin (S n) return forall P, P finO -> (forall i, P (finS i)) -> P i with
  | finO | _ => _ end _ _ _); eauto.
Qed.

Lemma to_nat_inj [n] (i j : fin n) : to_nat i = to_nat j -> i = j.
Proof.
  induction i; pose proof inj_S j; firstorder subst; try discriminate;
    cbn [to_nat] in *; eauto using f_equal.
Qed.

Lemma to_nat_inj_iff [n] (i j : fin n) : to_nat i = to_nat j <-> i = j.
Proof. split; try apply to_nat_inj; congruence. Qed.

Lemma to_nat_inj_dep [n] (i : fin n) [m] (j : fin m) : n = m -> to_nat i = to_nat j ->
  existT _ _ i = existT _ _ j.
Proof. destruct 1; auto using f_equal, to_nat_inj. Qed.

Lemma to_nat_0 n : to_nat (@finO n) = 0.
Proof. trivial. Qed.

Lemma to_nat_S [n] (i : fin n) : to_nat (finS i) = S (to_nat i).
Proof. trivial. Qed.

Lemma to_nat_bound [n] (i : fin n) : to_nat i < n.
Proof.
  induction i; cbn [to_nat]. { apply Nat.lt_0_succ. }
  rewrite <-Nat.succ_lt_mono. apply IHi.
Qed.

Lemma to_nat_eq_rect [m n] (p : m = n) i : to_nat (eq_rect m fin i n p) = to_nat i.
Proof. case p; trivial. Qed.

Lemma to_nat_cast [m n] (p : m = n) (i : fin m) : to_nat (cast i p) = to_nat i.
Proof. cbv[cast]. case Nat.eq_dec; intros; [apply to_nat_eq_rect|contradiction]. Qed.

Lemma cast_ext [m n] (p q : m = n) (i : fin m) : cast i p = cast i q.
Proof. apply to_nat_inj; rewrite 2 to_nat_cast; trivial. Qed.

Lemma to_nat_add_nat n [m] (i : fin m) : to_nat (add_nat n i) = n+i.
Proof. induction n; cbn [to_nat add_nat Nat.add]; auto. Qed.

Lemma to_nat_relax n [m] (i : fin m) : to_nat (relax n i) = i.
Proof. induction i; cbn [to_nat relax]; auto. Qed.

Lemma to_nat_of_nat i n p : to_nat (of_nat n i p) = i.
Proof.
  cbv [of_nat].
  rewrite to_nat_cast, to_nat_add_nat, to_nat_0, Nat.add_0_r; trivial.
Qed.

Lemma of_nat_to_nat [n] i p : of_nat n (to_nat i) p = i.
Proof. apply to_nat_inj, to_nat_of_nat. Qed.

Lemma of_nat_ext [n i] (p q : i < n) : of_nat n i p = of_nat n i q.
Proof. apply cast_ext. Qed.

Lemma finS_inj {n} (x y : fin n) : finS x = finS y -> x = y.
Proof. rewrite <-!to_nat_inj_iff; cbn [to_nat]; congruence. Qed.

Fixpoint of_nat' (i : nat) : fin (S i) :=
  match i with
  | O => finO
  | S i => finS (of_nat' i)
  end.

Lemma to_nat_of_nat' i : to_nat (of_nat' i) = i.
Proof. induction i; cbn [to_nat of_nat']; auto. Qed.
