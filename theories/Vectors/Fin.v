(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import PeanoNat Peano_dec.
#[local] Set Warnings "-deprecated".
From Stdlib Require Arith_base.

(** N.B.: This file defines a dependently-type programming view of
bounded integers. Another popular approach is to bundle integers with
a proof of boundedness, thus inheriting integer arithmetic rather than
redefining it on the bounded type. See
https://github.com/rocq-prover/stdlib/blob/master/theories/Vectors/Vector.v
for a similar discussion on bounded lists.

An alternative implementation can be found for instance in
https://github.com/math-comp/math-comp/blob/master/boot/fintype.v
One can read more about this type in section 7.4 of this book:
https://zenodo.org/record/4282710#.X_q4aGso-yU . *)

(** [fin n] is a way to represent \[1 .. n\]

[fin n] can be seen as a n-uplet of unit. [F1] is the first element of
the n-uplet. If [f] is the k-th element of the (n-1)-uplet, [FS f] is the
(k+1)-th element of  the n-uplet.

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010-01/2012-07/2012
*)

(** * The new interface: [fin n]

    Proofs about [fin] go through the injective conversion [val] to [nat]
    and the small inversions [inj_0] and [inj_S], not through dependent
    pattern matching. The historical interface ([t], [F1], [FS], [to_nat],
    [of_nat_lt], ...) follows below; it is deprecated. *)

Inductive fin : nat -> Type :=
| finO {n}             : fin (S n)
| finS {n} (_ : fin n) : fin (S n).
Notation fin0 := finO (only parsing).

(** [val i] is the natural number that [i] represents. *)
Fixpoint val {n} (i : fin n) : nat :=
  match i with
  | finO => 0
  | finS i => S (val i)
  end.
Coercion val : fin >-> nat.

Definition cast {m} (v: fin m) {n} : m = n -> fin n :=
  match Nat.eq_dec m n with
  | left Heq => fun _ => eq_rect m _ v n Heq
  | right Hneq => fun Heq => False_rect _ (Hneq Heq)
  end.

(** [add_nat n i] is the element [n + i] of [fin (n + m)]. *)
Fixpoint add_nat (n : nat) {m} (i : fin m) {struct n} : fin (n + m) :=
  match n with
  | 0 => i
  | S n => finS (add_nat n i)
  end.

(** [relax n i] is the element [i] of [fin (m + n)]. *)
Section Relax.
Context (n : nat).
Fixpoint relax {m} (i : fin m) : fin (m + n) :=
  match i in fin m return fin (m + n) with
  | finO => finO
  | finS i => finS (relax i)
  end.
End Relax.

Lemma mk_subproof n i : i < n -> i + S (n - S i) = n.
Proof.
  intros H. rewrite Nat.add_succ_r, <-Nat.add_succ_l, Nat.add_comm.
  apply Nat.sub_add, H.
Qed.

(** [mk n i H] is the element [i] of [fin n]. *)
Definition mk n (i : nat) (H : i < n) : fin n :=
  cast (add_nat i (@fin0 (n-S i))) (mk_subproof n i H).

(** [last n] is the last element of [fin (S n)]. *)
Fixpoint last (n : nat) : fin (S n) :=
  match n with
  | O => finO
  | S n => finS (last n)
  end.

Lemma inj_0 (i : fin 0) : False.
Proof. exact (match i with end). Qed.

Lemma inj_S {n} (i : fin (S n)) : i = finO \/ exists j, i = finS j.
Proof.
  pattern i; refine ( (* destruct i, but using elaborator's small inversions *)
  match i in fin (S n) return forall P, P finO -> (forall i, P (finS i)) -> P i with
  | finO | _ => _ end _ _ _); eauto.
Qed.

Lemma val_inj [n] (i j : fin n) : val i = val j -> i = j.
Proof.
  induction i; pose proof inj_S j; firstorder subst; try discriminate;
    cbn [val] in *; eauto using f_equal.
Qed.

Lemma val_inj_iff [n] (i j : fin n) : val i = val j <-> i = j.
Proof. split; try apply val_inj; congruence. Qed.

Lemma val_inj_dep [n] (i : fin n) [m] (j : fin m) : n = m -> val i = val j ->
  existT _ _ i = existT _ _ j.
Proof. destruct 1; auto using f_equal, val_inj. Qed.

Lemma val_0 n : val (@finO n) = 0.
Proof. trivial. Qed.

Lemma val_S [n] (i : fin n) : val (finS i) = S (val i).
Proof. trivial. Qed.

Lemma val_bound [n] (i : fin n) : val i < n.
Proof.
  induction i; cbn [val]. { apply Nat.lt_0_succ. }
  rewrite <-Nat.succ_lt_mono. apply IHi.
Qed.

Lemma val_eq_rect [m n] (p : m = n) i : val (eq_rect m fin i n p) = val i.
Proof. case p; trivial. Qed.

Lemma val_cast [m n] (p : m = n) (i : fin m) : val (cast i p) = val i.
Proof. cbv[cast]. case Nat.eq_dec; intros; [apply val_eq_rect|contradiction]. Qed.

Lemma cast_ext [m n] (p q : m = n) (i : fin m) : cast i p = cast i q.
Proof. apply val_inj; rewrite 2 val_cast; trivial. Qed.

Lemma val_add_nat n [m] (i : fin m) : val (add_nat n i) = n+i.
Proof. induction n; cbn [val add_nat Nat.add]; auto. Qed.

Lemma val_relax n [m] (i : fin m) : val (relax n i) = i.
Proof. induction i; cbn [val relax]; auto. Qed.

Lemma val_mk i n p : val (mk n i p) = i.
Proof.
  cbv [mk].
  rewrite val_cast, val_add_nat, val_0, Nat.add_0_r; trivial.
Qed.

Lemma mk_val [n] i p : mk n (val i) p = i.
Proof. apply val_inj, val_mk. Qed.

Lemma mk_ext [n i] (p q : i < n) : mk n i p = mk n i q.
Proof. apply cast_ext. Qed.

Lemma finS_inj {n} (x y : fin n) : finS x = finS y -> x = y.
Proof. rewrite <-!val_inj_iff; cbn [val]; congruence. Qed.

Lemma val_last n : val (last n) = n.
Proof. induction n; cbn [val last]; auto. Qed.

(** * The historical interface, deprecated *)

#[deprecated(since="9.3", use=fin)]
Abbreviation t := fin (only parsing).
#[deprecated(since="9.3", use=finO)]
Abbreviation F1 := finO (only parsing).
#[deprecated(since="9.3", use=finS)]
Abbreviation FS := finS (only parsing).
#[deprecated(since="9.3", use=fin_ind)]
Abbreviation t_ind := fin_ind (only parsing).
#[deprecated(since="9.3", use=fin_rect)]
Abbreviation t_rect := fin_rect (only parsing).
#[deprecated(since="9.3", use=fin_rec)]
Abbreviation t_rec := fin_rec (only parsing).
#[deprecated(since="9.3", use=fin_sind)]
Abbreviation t_sind := fin_sind (only parsing).

Section SCHEMES.
#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition case0 P (p: t 0): P p :=
  match p with | F1 | FS  _ => fun devil => False_rect (@ID) devil (* subterm !!! *) end.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition caseS' {n : nat} (p : t (S n)) : forall (P : t (S n) -> Type)
  (P1 : P F1) (PS : forall (p : t n), P (FS p)), P p :=
  match p with
  | @F1 k => fun P P1 PS => P1
  | FS pp => fun P P1 PS => PS pp
  end.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition caseS (P: forall {n}, t (S n) -> Type)
  (P1: forall n, @P n F1) (PS : forall {n} (p: t n), P (FS p))
  {n} (p: t (S n)) : P p := caseS' p P (P1 n) PS.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition rectS (P: forall {n}, t (S n) -> Type)
  (P1: forall n, @P n F1) (PS : forall {n} (p: t (S n)), P p -> P (FS p)):
  forall {n} (p: t (S n)), P p :=
fix rectS_fix {n} (p: t (S n)): P p:=
  match p with
  | @F1 k => P1 k
  | @FS 0 pp => case0 (fun f => P (FS f)) pp
  | @FS (S k) pp => PS pp (rectS_fix pp)
  end.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition rect2 (P : forall {n} (a b : t n), Type)
  (H0 : forall n, @P (S n) F1 F1)
  (H1 : forall {n} (f : t n), P F1 (FS f))
  (H2 : forall {n} (f : t n), P (FS f) F1)
  (HS : forall {n} (f g : t n), P f g -> P (FS f) (FS g)) :
    forall {n} (a b : t n), P a b :=
  fix rect2_fix {n} (a : t n) {struct a} : forall (b : t n), P a b :=
    match a with
    | @F1 m => fun (b : t (S m)) => caseS' b (P F1) (H0 _) H1
    | @FS m a' => fun (b : t (S m)) =>
      caseS' b (fun b => P (@FS m a') b) (H2 a') (fun b' => HS _ _ (rect2_fix a' b'))
    end.

End SCHEMES.

#[deprecated(since="9.3", use=finS_inj)]
Definition FS_inj {n} (x y: t n) (eq: FS x = FS y): x = y :=
match eq in _ = a return
  match a as a' in t m return match m with |0 => Prop |S n' => t n' -> Prop end
  with F1 =>  fun _ => True |FS y => fun x' => x' = y end x with
  eq_refl => eq_refl
end.

(** [to_nat f] = p iff [f] is the p{^ th} element of [fin m]. *)
#[deprecated(since="9.3", use=val)]
Fixpoint to_nat {m} (n : t m) : {i | i < m} :=
  match n with
    |@F1 j => exist _ 0 (Nat.lt_0_succ j)
    |FS p => match to_nat p with |exist _ i P => exist _ (S i) (proj1 (Nat.succ_lt_mono _ _) P) end
  end.

(** [of_nat p n] answers the p{^ th} element of [fin n] if p < n or a proof of
p >= n else *)
#[deprecated(since="9.3", use=mk)]
Fixpoint of_nat (p n : nat) : (t n) + { exists m, p = n + m } :=
  match n with
   |0 => inright _ (ex_intro _ p eq_refl)
   |S n' => match p with
      |0 => inleft _ (F1)
      |S p' => match of_nat p' n' with
        |inleft f => inleft _ (FS f)
        |inright arg => inright _ (match arg with |ex_intro _ m e =>
          ex_intro (fun x => S p' = S n' + x) m (f_equal S e) end)
      end
    end
  end.

(** [of_nat_lt p n H] answers the p{^ th} element of [fin n]
it behaves much better than [of_nat p n] on open term *)
#[deprecated(since="9.3", use=mk)]
Fixpoint of_nat_lt {p n : nat} : p < n -> t n :=
  match n with
    |0 => fun H : p < 0 => False_rect _ (PeanoNat.Nat.nlt_0_r p H)
    |S n' => match p with
      |0 => fun _ => @F1 n'
      |S p' => fun H => FS (of_nat_lt (proj2 (Nat.succ_lt_mono _ _) H))
    end
  end.

#[deprecated(since="9.3", use=mk_ext)]
Lemma of_nat_ext {p}{n} (h h' : p < n) : of_nat_lt h = of_nat_lt h'.
Proof.
 now rewrite (Peano_dec.le_unique _ _ h h').
Qed.

#[deprecated(since="9.3", use=mk_val)]
Lemma of_nat_to_nat_inv {m} (p : t m) : of_nat_lt (proj2_sig (to_nat p)) = p.
Proof.
induction p as [|? p]; simpl.
- reflexivity.
- destruct (to_nat p); simpl in *. f_equal. subst p. apply of_nat_ext.
Qed.

#[deprecated(since="9.3", use=val_mk)]
Lemma to_nat_of_nat {p}{n} (h : p < n) : to_nat (of_nat_lt h) = exist _ p h.
Proof.
revert p h. induction n as [|n IHn].
- intros p h. destruct (Nat.nlt_0_r p h).
- intros [|p] h; cbn; [|rewrite IHn]; f_equal; apply Peano_dec.le_unique.
Qed.

#[deprecated(since="9.3", use=val_inj)]
Lemma to_nat_inj {n} (p q : t n) :
 proj1_sig (to_nat p) = proj1_sig (to_nat q) -> p = q.
Proof.
 intro H.
 rewrite <- (of_nat_to_nat_inv p), <- (of_nat_to_nat_inv q).
 destruct (to_nat p) as (np,hp), (to_nat q) as (nq,hq); simpl in *.
 revert hp hq. rewrite H. apply of_nat_ext.
Qed.

#[deprecated(since="9.3", use=val)]
Lemma to_nat_val {n} (p : t n) : proj1_sig (to_nat p) = val p.
Proof.
 induction p as [|? p IHp]; cbn [to_nat val]; trivial.
 destruct (to_nat p); cbn in *; congruence.
Qed.

#[deprecated(since="9.3", use=mk)]
Lemma of_nat_lt_mk {p n} (h : p < n) : of_nat_lt h = mk n p h.
Proof.
 apply val_inj. rewrite val_mk, <-to_nat_val, to_nat_of_nat; trivial.
Qed.


(** [weak p f] answers a function witch is the identity for the p{^  th} first
element of [fin (p + m)] and [FS (FS .. (FS (f k)))] for [FS (FS .. (FS k))]
with p FSs *)
#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Fixpoint weak {m}{n} p (f : t m -> t n) :
  t (p + m) -> t (p + n) :=
match p as p' return t (p' + m) -> t (p' + n) with
  |0 => f
  |S p' => fun x => match x with
     |@F1 n' => fun eq : n' = p' + m => F1
     |@FS n' y => fun eq : n' = p' + m => FS (weak p' f (eq_rect _ t y _ eq))
  end (eq_refl _)
end.

(** The p{^ th} element of [fin m] viewed as the p{^ th} element of
[fin (m + n)] *)
#[deprecated(since="9.3", use=relax)]
Abbreviation L n := (relax n) (only parsing).

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma L_sanity {m} n (p : t m) : proj1_sig (to_nat (L n p)) = proj1_sig (to_nat p).
Proof.
induction p as [|? p IHp].
- reflexivity.
- simpl; destruct (to_nat (L n p)); simpl in *; rewrite IHp. now destruct (to_nat p).
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma L_inj {m} n (p q : t m) : L n p = L n q -> p = q.
Proof.
induction p as [m|m p IH]; apply (caseS' q); [easy..|].
intros ??. f_equal. now apply IH, FS_inj.
Qed.

(** The p{^ th} element of [fin m] viewed as the p{^ th} element of
[fin (n + m)]
Really really inefficient !!! *)
#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition L_R {m} n (p : t m) : t (n + m).
Proof.
induction n as [|n IHn].
- exact p.
- exact ((fix LS k (p: t k) :=
    match p with
      |@F1 k' => @F1 (S k')
      |FS p' => FS (LS _ p')
    end) _ IHn).
Defined.

(** The p{^ th} element of [fin m] viewed as the (n + p){^ th} element of
[fin (n + m)] *)
#[deprecated(since="9.3", use=add_nat)]
Abbreviation R n := (add_nat n) (only parsing).

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma R_sanity {m} n (p : t m) : proj1_sig (to_nat (R n p)) = n + proj1_sig (to_nat p).
Proof.
induction n as [|n IHn].
- reflexivity.
- simpl; destruct (to_nat (R n p)); simpl in *; rewrite IHn. now destruct (to_nat p).
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma R_inj {m} n (p q : t m) : R n p = R n q -> p = q.
Proof.
induction n as [|n IH].
- easy.
- intros ?. now apply IH, FS_inj.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma L_R_neq n m (p : t n) (q : t m) : L m p <> R n q.
Proof.
induction p as [n|n p IH].
- discriminate.
- intros ?. now apply IH, FS_inj.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Fixpoint case_L_R' {n m} : forall (P : t (n + m) -> Type) (p : t (n + m)),
  (forall q, P (L m q)) -> (forall q, P (R n q)) -> P p :=
match n with
| 0 => fun P p HL HR => HR p
| S n' => fun P p HL HR => Fin.caseS' p P
    (HL Fin.F1)
    (fun p' => case_L_R' (fun q => P (Fin.FS q)) p' (fun q => HL (Fin.FS q)) HR)
end.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Definition case_L_R (P : forall n m, t (n + m) -> Type) {n m} (p : t (n + m)) :
  (forall n m (q : t n), P n m (L m q)) -> (forall n m (q : t m), P n m (R n q)) -> P n m p :=
fun HL HR => case_L_R' _ p (HL _ _) (HR _ _).

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma case_L_R'_L {n m : nat} (P : Fin.t (n + m) -> Type) (p : Fin.t n) HL HR :
  case_L_R' P (Fin.L m p) HL HR = HL p.
Proof.
  induction p as [|? ? IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma case_L_R'_R {n m : nat} (P : Fin.t (n + m) -> Type) (p : Fin.t m) HL HR :
  case_L_R' P (Fin.R n p) HL HR = HR p.
Proof.
  induction n as [|? IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma case_L_R_L (P : forall n m, t (n + m) -> Type) {n m} (p : Fin.t n) HL HR :
  case_L_R P (Fin.L m p) HL HR = HL _ _ p.
Proof.
  apply case_L_R'_L.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma case_L_R_R (P : forall n m, t (n + m) -> Type) {n m} (p : Fin.t m) HL HR :
  case_L_R P (Fin.R n p) HL HR = HR _ _ p.
Proof.
  apply case_L_R'_R.
Qed.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Fixpoint depair {m n} (o : t m) (p : t n) : t (m * n) :=
match o with
  |@F1 m' => L (m' * n) p
  |FS o' => R n (depair o' p)
end.

#[deprecated(since="9.3", note="Please open an issue if you would like stdlib to keep this definition.")]
Lemma depair_sanity {m n} (o : t m) (p : t n) :
  proj1_sig (to_nat (depair o p)) = n * (proj1_sig (to_nat o)) + (proj1_sig (to_nat p)).
Proof.
induction o as [|? o IHo] ; simpl.
- rewrite L_sanity. now rewrite Nat.mul_0_r.
- rewrite R_sanity. rewrite IHo.
  rewrite Nat.add_assoc. destruct (to_nat o); simpl; rewrite Nat.mul_succ_r.
    now rewrite (Nat.add_comm n).
Qed.

Fixpoint eqb {m n} (p : t m) (q : t n) :=
match p, q with
| @F1 m', @F1 n' => Nat.eqb m' n'
| FS _, F1 => false
| F1, FS _ => false
| FS p', FS q' => eqb p' q'
end.

Lemma eqb_nat_eq : forall m n (p : t m) (q : t n), eqb p q = true -> m = n.
Proof.
intros m n p; revert n; induction p as [|? p IHp];
 intros ? q; destruct q; simpl; intros; f_equal.
- now apply Nat.eqb_eq.
- easy.
- easy.
- eapply IHp. eassumption.
Qed.

Lemma eqb_eq : forall n (p q : t n), eqb p q = true <-> p = q.
Proof.
apply rect2; simpl; intros.
- split; intros ; [ reflexivity | now apply Nat.eqb_eq ].
- now split.
- now split.
- eapply iff_trans.
 + eassumption.
 + split.
  * intros; now f_equal.
  * apply FS_inj.
Qed.

Lemma eq_dec {n} (x y : t n): {x = y} + {x <> y}.
Proof.
case_eq (eqb x y); intros.
- left; now apply eqb_eq.
- right. intros Heq. apply <- eqb_eq in Heq. congruence.
Defined.
