(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definitions of Vectors and functions to use them

   Initial Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

(** Length-indexed lists [vec A n]. Proofs about [vec] go through the
    injective conversion [to_list] (see [VectorSpec]) and the small
    inversions [inj_0] and [inj_S], not through dependent pattern matching.
    The historical interface ([t], [nil A], [cons A h n v], [nth],
    [append], ...) follows the new one below; it is deprecated. *)

#[local] Set Warnings "+deprecated".
From Stdlib Require Import PeanoNat List Arith_base.
From Stdlib Require Fin.
Import EqNotations.
#[local] Open Scope nat_scope.

#[universes(template)]
Inductive vec A : nat -> Type :=
| nil : vec _ 0
| cons (h : A) (n : nat) (tl : vec _ n) : vec _ (S n).
Arguments nil {_}.
Arguments cons {_} _ {_} _.

Section UniformElementType.
Context {A : Type}.

Fixpoint to_list {n} (v : vec A n) {struct v} : list A :=
  match v with
  | nil => List.nil
  | cons a v => List.cons a (to_list v)
  end.

Fixpoint of_list (l : list A) {struct l} : vec A (length l) :=
  match l with
  | List.nil => nil
  | List.cons h tail => cons h (of_list tail)
  end.

Definition cast {m} (v: vec A m) {n} : m = n -> vec A n :=
  match Nat.eq_dec m n with
  | left Heq => fun _ => eq_rect m _ v n Heq
  | right Hneq => fun Heq => False_rect _ (Hneq Heq)
  end.

Definition tl {n} (v : vec A (S n)) : vec A n := let 'cons _ v := v in v.

Definition hd {n} (v : vec A (S n)) : A := let 'cons a _ := v in a.

Definition hd_error {n} (v : vec A n) : option A :=
  match v with
  | nil => None
  | cons a v => Some a
  end.

Fixpoint snoc {n} (v:vec A n) (a : A) {struct v} : vec A (S n) :=
  match v with
  | nil => cons a nil
  | cons h t => cons h (snoc t a)
  end.

Fixpoint last {n} (v : vec A (S n)) {struct v} : A :=
  let '@cons _ a n v := v in
  match n return vec _ n -> _ with
  | O => fun _ => a
  | S _ => last
  end v.

Fixpoint app {n p} (v : vec A n) (w : vec A p) {struct v} : vec A (n+p) :=
  match v with
  | nil => w
  | cons a v => cons a (app v w)
  end.

Section WithA.
Context (a : A).
Fixpoint repeat n {struct n} : vec A n :=
  match n with
  | O => nil
  | S n => cons a (repeat n)
  end.
End WithA.

Fixpoint firstn {n} (v : vec A n) {struct v} : forall i, vec A (Nat.min n i) :=
  match v with
  | nil => fun _ => nil
  | cons a v => fun i =>
      match i with
      | O => nil
      | S i => cons a (firstn v i)
      end
  end.

Fixpoint skipn {n} (v : vec A n) i {struct v} : vec A (Nat.sub n i) :=
  match v with
  | nil => match i with (O|_) => nil end
  | (cons a v') as v =>
      match i with
      | O => v
      | S i => skipn v' i
      end
  end.

Definition get {n} (v : vec A n) i := hd_error (skipn v i).

Fixpoint put {n : nat} (v : vec A n) (i : nat) (a : A) {struct v} :=
  match v with
  | nil => nil
  | cons b v =>
    match i with
    | O => cons a v
    | S i => cons b (put v i a)
    end
  end.

Lemma lastn_subproof n i : n - (n - i) = Nat.min n i.
Proof.
  destruct (Nat.le_ge_cases n i) as [H|H].
  { rewrite Nat.min_l, (proj2 (Nat.sub_0_le _ _) H), Nat.sub_0_r; trivial. }
  { rewrite Nat.min_r, Nat.sub_sub_distr, Nat.sub_diag; trivial. }
Qed.

Definition lastn {n} (v : vec A n) i : vec A (Nat.min n i) :=
  cast (skipn v (n-i)) (lastn_subproof n i).

Fixpoint unappl {i n} {struct i} : forall (v : vec A (i+n)), vec A i :=
  match i with
  | O => fun v => nil
  | S i => fun v => cons (hd v) (unappl (tl v))
  end.

Fixpoint unappr {i n} {struct i} : forall (v : vec A (i+n)), vec A n :=
  match i with
  | O => fun v => v
  | S i => fun v => unappr (tl v)
  end.

Fixpoint unapp (l : nat) {r : nat} : vec A (l + r) -> vec A l * vec A r :=
  match l with
  | 0 => fun v => (nil, v)
  | S l' => fun v =>
    let (v1, v2) := unapp l' (tl v) in
    (cons (hd v) v1, v2)
  end.

Lemma length_to_list n (v : vec A n) : length (to_list v) = n.
Proof. induction v; cbn [length to_list]; auto. Qed.

Definition rev_append {n p} (v : vec A n) (w : vec A p) : vec A (n + p).
Proof.
  refine (cast (of_list (List.rev_append (to_list v) (to_list w))) _).
  abstract (rewrite rev_append_rev, length_app, length_rev, 2 length_to_list; trivial).
Defined.

Definition rev {n} (v : vec A n) : vec A n.
Proof.
  refine (cast (of_list (List.rev (to_list v))) _).
  abstract (rewrite length_rev, length_to_list; trivial).
Defined.
End UniformElementType.
Coercion to_list : vec >-> list.
Arguments length_to_list : clear implicits.

Section Map.
Context {A} {B} (f : A -> B).
Fixpoint map {n} (v:vec A n) : vec B n :=
  match v with
  | nil => nil
  | cons a v' => cons (f a) (map v')
  end.
End Map.

Section Map2.
Context {A B C} (f : A -> B -> C).
Fixpoint map2 {n} (v : vec A n) {struct v} : vec B n -> vec C n :=
  match v with
  | nil => fun _ => nil
  | cons a v => fun w => cons (f a (hd w)) (map2 v (tl w))
  end.
End Map2.

Section FoldLeft.
Context {A B : Type} (f:B->A->B).
Fixpoint fold_left (b : B) {n} (v : vec A n) : B :=
  match v with
  | nil => b
  | cons a v => fold_left (f b a) v
  end.
End FoldLeft.

Section FoldRight.
Context {A B : Type} (f : A->B->B).
Fixpoint fold_right {n} (v : vec A n) (b:B) {struct v} : B :=
  match v with
  | nil => b
  | cons a v => f a (fold_right v b)
  end.
End FoldRight.



(** The predicates are declared outside of sections so that their induction
principles take the element types as explicit arguments, as [Vector] did. *)

Inductive Forall {A} (P : A -> Prop) : forall {n}, vec A n -> Prop :=
| Forall_nil : Forall P nil
| Forall_cons {n} x (v : vec A n) (_ : P x) (_ : Forall P v) : Forall P (cons x v).

Inductive Exists {A} (P : A -> Prop) : forall {n}, vec A n -> Prop :=
| Exists_cons_hd {n} x (v : vec A n) (_ : P x) : Exists P (cons x v)
| Exists_cons_tl {n} x (v : vec A n) (_ : Exists P v) : Exists P (cons x v).

Inductive In {A} (a : A) : forall {n}, vec A n -> Prop :=
| In_cons_hd {n} (v : vec A n) : In a (cons a v)
| In_cons_tl {n} x (v : vec A n) (_ : In a v) : In a (cons x v).

Inductive Forall2 {A B} (P : A -> B -> Prop) : forall {n}, vec A n -> vec B n -> Prop :=
| Forall2_nil : Forall2 P nil nil
| Forall2_cons {n} x1 x2 (v1 : vec A n) (v2 : vec B n) (_ : P x1 x2) (_ : Forall2 P v1 v2)
  : Forall2 P (cons x1 v1) (cons x2 v2).

Inductive Exists2 {A B} (P : A -> B -> Prop) : forall {n}, vec A n -> vec B n -> Prop :=
| Exists2_cons_hd {n} x1 x2 (v1 : vec A n) (v2 : vec B n) (_ : P x1 x2)
  : Exists2 P (cons x1 v1) (cons x2 v2)
| Exists2_cons_tl {n} x1 x2 (v1 : vec A n) (v2 : vec B n) (_ : Exists2 P v1 v2)
  : Exists2 P (cons x1 v1) (cons x2 v2).


Lemma inj_0 [A] (v : vec A 0) : v = nil.
Proof. exact (let 'nil := v in eq_refl). Qed.

Lemma inj_S [A n] (v : vec A (S n)) : v = cons (hd v) (tl v).
Proof. exact (let 'cons _ _ := v in eq_refl). Qed.

(** * Indexing by a bounded natural number *)

Section UniformElementType.
Context {A : Type}.

Fixpoint getFin {n : nat} (v : vec A n) {struct v} : Fin.fin n -> A :=
  match v with
  | nil => fun i => False_rect _ (Fin.inj_0 i)
  | cons a v => fun i =>
    match i in Fin.fin n return vec _ (pred n) -> A with
    | Fin.finO => fun _ => a
    | Fin.finS i => fun v => getFin v i
    end v
  end.

Fixpoint putFin {n} (v : vec A n) {struct v} : Fin.fin n -> A -> vec A n :=
  match v with
  | nil => fun _ _ => nil
  | cons b v => fun i =>
    match i in Fin.fin n return vec _ (pred n) -> _ -> vec _ n with
    | Fin.finO => fun v a => cons a v
    | Fin.finS i => fun v a => cons b (putFin v i a)
    end v
  end.

Definition getLt {n} (v: vec A n) {p} (H: p < n) := getFin v (Fin.mk _ _ H).
Definition putLt {n} (v: vec A n) {p} (H: p < n) := putFin v (Fin.mk _ _ H).
End UniformElementType.

(** * Boolean equality *)

Section BEQ.

 Variables (A: Type) (A_beq: A -> A -> bool).
 Hypothesis A_eqb_eq: forall x y, A_beq x y = true <-> x = y.

 Fixpoint eqb {m n} (v1: vec A m) (v2: vec A n) : bool :=
   match v1, v2 with
   | nil, nil => true
   | cons h1 t1, cons h2 t2 => A_beq h1 h2 && eqb t1 t2
   | _, _ => false
   end.

 Lemma eqb_nat_eq: forall m n (v1: vec A m) (v2: vec A n)
  (Hbeq: eqb v1 v2 = true), m = n.
 Proof.
   intros m n v1; revert n.
   induction v1; intros ? v2; destruct v2;
     [now constructor | discriminate | discriminate | simpl].
   intros Hbeq; apply andb_prop in Hbeq; destruct Hbeq.
   f_equal; eauto.
 Qed.

 Lemma eqb_eq: forall n (v1: vec A n) (v2: vec A n),
  eqb v1 v2 = true <-> v1 = v2.
 Proof.
   induction v1 as [|h1 n t1 IH]; intros v2.
   - rewrite (inj_0 v2). split; reflexivity.
   - rewrite (inj_S v2); cbn. split.
     + intros Hbeq. apply andb_prop in Hbeq as [Hh Ht].
       apply A_eqb_eq in Hh. apply IH in Ht. now f_equal.
     + intros Heq. apply andb_true_intro. split.
       * apply A_eqb_eq, (f_equal (@hd _ _) Heq).
       * apply IH, (f_equal (@tl _ _) Heq).
 Qed.

 Definition eq_dec n (v1 v2: vec A n): {v1 = v2} + {v1 <> v2}.
 Proof.
 case_eq (eqb v1 v2); intros.
  + left; now apply eqb_eq.
  + right. intros Heq. apply <- eqb_eq in Heq. congruence.
 Defined.

 Lemma eqb_spec n (v1 v2 : vec A n) : BoolSpec (v1 = v2) (v1 <> v2) (eqb v1 v2).
 Proof.
 case_eq (eqb v1 v2); intros E; constructor.
  + now apply eqb_eq.
  + intros Heq. apply <- eqb_eq in Heq. congruence.
 Qed.

End BEQ.

(** * The historical interface, deprecated *)

#[local] Set Warnings "-deprecated".

(** The constructors get back the argument structure of the old [Vector.t],
in which the element type and the length are explicit arguments: this
[Arguments] command keeps working the commands [Arguments Vector.nil {A}]
and [Arguments Vector.cons {A} _ {n}] that users wrote for them. *)
#[deprecated(since="9.4", use=vec)]
Abbreviation t := vec (only parsing).
Arguments nil : clear implicits.
Arguments cons : clear implicits.
#[deprecated(since="9.4", use=vec_ind)]
Abbreviation t_ind := vec_ind (only parsing).
#[deprecated(since="9.4", use=vec_rect)]
Abbreviation t_rect := vec_rect (only parsing).
#[deprecated(since="9.4", use=vec_rec)]
Abbreviation t_rec := vec_rec (only parsing).
#[deprecated(since="9.4", use=vec_sind)]
Abbreviation t_sind := vec_sind (only parsing).

#[local] Notation "[ ]" := (nil _) (format "[ ]").
#[local] Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).


(** An induction scheme for non-empty vectors *)

#[deprecated(since="9.4", note="Use small inversions. Elaborator input: let '@cons _ a n' v' := v in ...")]
Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match v with
 |@cons _ a 0 v =>
   match v with
     |nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
   end
 |@cons _ a (S nn') v => rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
 end.

(** A vector of length [0] is [nil] *)
#[deprecated(since="9.4", use=inj_0)]
Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(** A vector of length [S _] is [cons] *)
#[deprecated(since="9.4", use=inj_S)]
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

#[deprecated(since="9.4", use=inj_S)]
Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

#[deprecated(since="9.4", use=inj_S)]
(** An induction scheme for 2 vectors of same length *)
Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match v1 with
  | [] => fun v2 => case0 _ bas v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
  end.


(** Build a vector of n{^ th} [a] *)
#[deprecated(since="9.4", use=repeat)]
Abbreviation const := repeat (only parsing).

(** The [p]{^ th} element of a vector of length [m].

Computational behavior of this function should be the same as
ocaml function. *)
#[deprecated(since="9.4", use=getFin)]
Definition nth {A} :=
  fix nth_fix {n : nat} (v : t A n) {struct v} : Fin.t n -> A :=
    match v with
    | nil _ => fun p => False_rect A (Fin.case0 _ p)
    | cons _ x m v' => fun p =>
      match p in (Fin.t m') return t A (pred m') -> A with
      | Fin.F1 => fun _ => x
      | Fin.FS p' => fun v' => nth_fix v' p'
      end v'
    end.

(** An equivalent definition of [nth]. *)
#[deprecated(since="9.4", use=getLt)]
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

(** Put [a] at the p{^ th} place of [v] *)
#[deprecated(since="9.4", use=putFin)]
Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace t p' a)))
  end v.

(** Version of replace with [lt] *)
#[deprecated(since="9.4", use=putLt)]
Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

(** Remove the first element of a non empty vector *)
(** Destruct a non empty vector *)
#[deprecated(since="9.4", note="Use small inversions. Elaborator input: let '@cons _ a n' v' := v in ...")]
Definition uncons {A} {n : nat} (v : t A (S n)) : A * t A n := (hd v, tl v).

(** Remove last element of a non-empty vector *)
#[deprecated(since="9.4", note="If you would like stdlib to keep this definition, please open an issue.")]
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
#[global] Arguments shiftout {A} {n} v.

#[deprecated(since="9.4", use=snoc)]
(** Add an element at the end of a vector *)
Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match v with
  |[] => a :: []
  |h :: t => h :: (shiftin a t)
end.

(** Copy last element of a vector *)
#[deprecated(since="9.4", note="If you would like stdlib to keep this definition, please open an issue.")]
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
#[global] Arguments shiftrepeat {A} {n} v.

(** Take first [p] elements of a vector *)
#[deprecated(since="9.4", use=firstn)]
Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p :=
  match p as p return p <= n -> t A p with
  | 0 => fun _ => []
  | S p' => match v in t _ n return S p' <= n -> t A (S p') with
    | []=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
    | x::xs => fun le => x::take p' (le_S_n p' _ le) xs
    end
  end le.

(** Remove [p] last elements of a vector *)
#[deprecated(since="9.4", use=firstn, note="If you would like stdlib to keep this definition, please open an issue.")]
Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
  -> t A (n - p).
Proof.
  intros A n p; induction p as [| p f]; intros H v.
  - rewrite Nat.sub_0_r.
    exact v.

  - apply shiftout.

    rewrite <- Nat.sub_succ_l.
    + exact (f (Nat.lt_le_incl _ _ H) v).
    + exact (Nat.lt_le_incl _ _ H).
Defined.

(** Concatenation of two vectors *)
#[deprecated(since="9.4", use=app)]
Abbreviation append := app (only parsing).

(** Split a vector into two parts *)
#[deprecated(since="9.4", use=unapp)]
Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

(** Two definitions of the tail recursive function that appends two lists but
reverses the first one *)

#[deprecated(since="9.4", note="If you would like stdlib to keep this definition, please open an issue.")]
(** This one has the exact expected computational behavior *)
Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (Nat.tail_add n p) :=
  match v with
  | [] => w
  | a :: v' => rev_append_tail v' (a :: w)
  end.


#[local] Notation "v [@ p ]" := (nth v p) (at level 1).

(** fold_right2 g c [x1 .. xn] [y1 .. yn] = g x1 y1 (g x2 y2 .. (g xn yn c) .. )
    c is before the vectors to be compliant with "refolding". *)
#[deprecated(since="9.4", note="Use fold_right and map2. Please open an issue if you would like stdlib to keep this definition.")]
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).


(** fold_left2 f b [x1 .. xn] [y1 .. yn] = g .. (g (g a x1 y1) x2 y2) .. xn yn *)
#[deprecated(since="9.4", note="Use fold_left and map2. Please open an issue if you would like stdlib to keep this definition.")]
Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
match v in t _ n0 return t C n0 -> A with
  |[] => fun w => case0 (fun _ => A) a w
  |@cons _ vh vn vt => fun w =>
    caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a vh wh) vt wt)
end.


Module VectorNotations.
Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "[ ]" := (@nil _) (format "[ ]") : vector_scope.
Notation "h :: t" := (@cons _ h _ t) (at level 60, right associativity)
  : vector_scope.
Notation "[ x ]" := (@cons _ x _ (@nil _)) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (@cons _ x _ (@cons _ y _ .. (@cons _ z _ (@nil _)) ..)) : vector_scope.
Infix "++" := app : vector_scope.
#[deprecated(since="9.4", note="Use getFin v p.")]
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
Open Scope vector_scope.
End VectorNotations.
