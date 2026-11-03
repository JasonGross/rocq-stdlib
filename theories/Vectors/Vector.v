(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** N.B.: Lists inductively defined with a dependency on their length,
here called vectors, are popular in dependent type programming:
programs embed their specification and only programs are
manipulated. However, this currently requires mastering advanced
dependent type programming to simultaneously handle the list
manipulation and the specification of its length.

We recommend using lists bundled with, when needed, a proof about
their length rather than vectors. (Thanks to the proof irrelevance of
equality on [nat], any two bundlings of a same list are provably
equal.) This decouples the two aspects above, making it easy to write
code in Gallina and develop proofs with tactics.

Such an implementation can be found for instance in
https://github.com/math-comp/math-comp/blob/master/boot/tuple.v
One can read more about this tuple type in section 7.1 of this book:
https://doi.org/10.5281/zenodo.4282710 .
In particular, this implementation comes with coercion and canonical
structures so that lists and tuples can be transparently mixed most of
the time. For instance, after [From mathcomp Require Import seq tuple.],
in [Context n1 n2 T (v1 : n1.-tuple T) (v2 : n2.-tuple T) (foo : (n1 + n2).-tuple T -> bool).]
one can write [Check foo (v1 ++ v2).], where [++] is the list concatenation,
and Coq will automatically elaborate it, as [Set Printing All.] would show,
to [foo (cat_tuple v1 v2)] where [cat_tuple] is the lifting of [++] on tuples.

Another representation can be found in
https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Datatypes/HList.v
where tuples can be manipulated through the [of_list] and [to_list] functions.
This has to be done manually though as the library doesn't automate it.

To give an example of the difficulties faced with [Vector.t],
writing [VectorDef.rev] constitutes a good exercise. This proves
fairly tricky and requires reimplementing dependent type versions
of functions already written on lists (typing [Vector.rev] even
relies on a tail-recursive version of the addition on natural
numbers whose computational content structurally follows the one
of the auxiliary function [Vector.rev_append] from which
[Vector.rev] is defined; additionally, the computational content
is intertwined with some rewriting steps). In contrast, the
dependent pair encoding reuses functions and lemmas already
written on lists and the definition (called [rev_tuple] in
mathcomp's [tuple.v]) only needs the property that [rev]
preserves the length:

[[
From Stdlib Require Import List.

Record tuple_of (n : nat) T := Tuple
  { tval :> list T; tsize : length tval = n }.

Lemma rev_tupleP [T n] (t : tuple_of n T) : length (rev t) = n.
Proof. now rewrite length_rev, tsize. Qed.
Canonical rev_tuple T n (t : tuple_of n T) := Tuple n T (rev t) (rev_tupleP t).

(* The canonical instance allows to automatically elaborate tuples: *)
Section TestRevTuple.
Variables (T : Type) (n : nat) (t : tuple_of n T).
Check rev t : tuple_of n T.
]]

Thus lemmas about lists are enough in most cases. *)

(** Vectors.

   Initial Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010

Originally from the contribution bit vector by Jean Duprat (ENS Lyon).

Based on contents from Util/VecUtil of the CoLoR contribution *)

From Stdlib Require Import PeanoNat Eqdep_dec List.
From Stdlib Require Fin.
From Stdlib Require VectorDef.
Include VectorDef.
Import VectorNotations EqNotations.

(** Deprecation warnings are errors in the non-deprecated part of this file:
    the new interface must not depend on the deprecated one. *)
#[local] Set Warnings "+deprecated".

(** * Properties of the new interface *)

(** [to_list] is injective: most proofs about [vec] go through it. *)

Lemma to_list_inj [A n] (v w : vec A n) : to_list v = to_list w -> v = w.
Proof.
  induction n; cbn [to_list].
  { rewrite (inj_0 v), (inj_0 w); trivial. }
  { rewrite (inj_S v), (inj_S w); inversion 1; f_equal; eauto. }
Qed.


Lemma to_list_inj_iff [A n] (v w : vec A n) : to_list v = to_list w <-> v = w.
Proof. split; try apply to_list_inj; congruence. Qed.

Lemma to_list_inj_dep [A m] (v : vec A m) [n] (w : vec A n) :
  to_list v = to_list w -> existT _ _ v = existT _ _ w.
Proof.
  intros H; specialize (f_equal (@length _) H); rewrite 2 length_to_list.
  destruct 1; auto using f_equal, to_list_inj.
Qed.

Lemma to_list_eq_rect [A m n] (p : m = n) v : to_list (eq_rect m (vec A) v n p) = to_list v.
Proof. case p; trivial. Qed.

Lemma to_list_cast [A m n] (p : m = n) (v : vec A m) : to_list (cast v p) = to_list v.
Proof. cbv[cast]. case Nat.eq_dec; intros; [apply to_list_eq_rect|contradiction]. Qed.


Lemma to_list_nil A : to_list (@nil A) = List.nil.
Proof. trivial. Qed.

Lemma to_list_cons [A n] a (v : vec A n) : to_list ((a :: v)) = List.cons a v.
Proof. trivial. Qed.

Lemma to_list_of_list [A] (l : list A) : to_list (of_list l) = l.
Proof. induction l; cbn [to_list of_list]; congruence. Qed.

Lemma hd_to_list [A n] (d : A) (v : vec A (S n)) : List.hd d v = hd v.
Proof. rewrite (inj_S v); trivial. Qed.

Lemma to_list_tl [A n] (v : vec A (S n)) : to_list (tl v) = List.tl v.
Proof. rewrite (inj_S v); trivial. Qed.

Lemma last_to_list [A n] (d : A) (v : vec A (S n)) : List.last v d = last v.
Proof.
  rewrite (inj_S v) in *.
  generalize (hd v); generalize (tl v); clear v; intros v; induction v; trivial.
  set (h::v) as hv; cbn [List.last to_list last]; subst hv. rewrite IHv. auto.
Qed.

Lemma to_list_repeat [A n] (a : A) : to_list (repeat a n) = List.repeat a n.
Proof. induction n; cbn [to_list repeat List.repeat]; auto using f_equal2. Qed.

Lemma to_list_app [A n p] (v : vec A n) (w : vec A p) : to_list (app v w) = List.app v w.
Proof. induction v; cbn [to_list app List.app]; rewrite ?IHv; trivial. Qed.

Lemma to_list_firstn [A n] (v : vec A n) i : to_list (firstn v i) = List.firstn i v.
Proof. revert i; induction v, i; cbn [to_list firstn List.firstn]; congruence. Qed.


Lemma to_list_rev [A n] (v : vec A n) : to_list (rev v) = List.rev v.
Proof. cbv [rev]. rewrite to_list_cast, to_list_of_list; trivial. Qed.

Lemma to_list_In A a n (v : vec A n): In a v <-> List.In a (to_list v).
Proof.
  split.
  { induction 1; [left|right]; auto. }
  { induction v; inversion 1; subst; auto using In_cons_tl, In_cons_hd. }
Qed.

Lemma to_list_map [A B n] (f : A -> B) (v : vec A n) : to_list (map f v) = List.map f v.
Proof. induction v; cbn [to_list map List.map]; auto using f_equal. Qed.

Lemma to_list_map2 [A B C n] (f : A -> B -> C) (v : vec A n) (w : vec B n) :
  to_list (map2 f v w) = List.map (uncurry f) (List.combine v w).
Proof.
  induction v; [|rewrite (inj_S w)];
    cbn [to_list map2 List.map List.combine]; auto using f_equal.
Qed.

Lemma to_list_snoc [A n] (v : vec A n) a : to_list (snoc v a) = List.app v (List.cons a List.nil).
Proof. induction v; cbn; auto using f_equal. Qed.


(** * [app] *)

Lemma app_assoc_dep [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  existT _ _ (app a (app b c)) = existT _ _ (app (app a b) c).
Proof.
  apply to_list_inj_dep.
  induction a; cbn [app to_list]; auto using f_equal2.
Qed.

Lemma app_assoc_vec [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  app a (app b c) = cast (app (app a b) c) (eq_sym (Nat.add_assoc _ _ _)).
Proof.
  pose proof app_assoc_dep a b c as E; symmetry in E; inversion_sigma.
  apply to_list_inj; rewrite <-E2, to_list_eq_rect, to_list_cast; trivial.
Qed.

Lemma sym_app_assoc [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  app (app a b) c = cast (app a (app b c)) (Nat.add_assoc _ _ _).
Proof.
  pose proof app_assoc_dep a b c as E; inversion_sigma.
  apply to_list_inj; rewrite <-E2, to_list_eq_rect, to_list_cast; trivial.
Qed.

Lemma app_repeat_repeat [A] (a : A) n m : app (repeat a n) (repeat a m) = repeat a (n + m).
Proof. induction n; cbn [app repeat Nat.add]; auto using f_equal. Qed.

(** * [rev] *)

Lemma rev_nil A : rev [] = [] :> vec A _.
Proof. trivial. Qed.

Lemma rev_cons_snoc [A n] a (v : vec A n) : rev ((a :: v)) = snoc (rev v) a.
Proof. erewrite <-to_list_inj_iff, to_list_snoc, 2 to_list_rev, to_list_cons, List.rev_cons; trivial. Qed.

Lemma rev_snoc [A n] (v : vec A n) a : rev (snoc v a) = (a :: (rev v)).
Proof. erewrite <-to_list_inj_iff, to_list_cons, 2 to_list_rev, to_list_snoc, List.rev_unit; trivial. Qed.

Lemma rev_rev [A n] (v : vec A n) : rev (rev v) = v.
Proof. apply to_list_inj; rewrite 2 to_list_rev, List.rev_involutive; trivial. Qed.

Lemma rev_map [A B] (f : A -> B) [n] (v : vec A n) : rev (map f v) = map f (rev v).
Proof. apply to_list_inj; rewrite to_list_map, 2 to_list_rev, List.map_rev, to_list_map. trivial. Qed.

Lemma map_rev [A B] (f : A -> B) [n] (v : vec A n) : map f (rev v) = rev (map f v).
Proof. apply to_list_inj; rewrite to_list_map, 2 to_list_rev, List.map_rev, to_list_map. trivial. Qed.


(** * [map] *)

Lemma map_id [A n] (v : vec A n) : map (fun x => x) v = v.
Proof. apply to_list_inj; rewrite to_list_map, List.map_id; trivial. Qed.

Lemma map_nil [A B] (f : A -> B) : map f [] = [].
Proof. trivial. Qed.

Lemma map_cons_vec [A B] (f : A -> B) (a : A) [n] (v : vec A n) :
  map f ((a :: v)) = ((f a) :: (map f v)).
Proof. trivial. Qed.

Lemma map_map [A B C] (f : A -> B) (g : B -> C) [n] (v : vec A n) :
  map g (map f v) = map (fun x => g (f x)) v.
Proof. apply to_list_inj; rewrite 3 to_list_map, List.map_map; trivial. Qed.

Lemma map_ext_in [A B] (f g:A->B) [n] (v : vec A n)
  (H : forall a, In a v -> f a = g a) : map f v = map g v.
Proof.  setoid_rewrite to_list_In in H; erewrite <-to_list_inj_iff, !to_list_map, List.map_ext_in; trivial. Qed.

Lemma map_ext [A B] (f g:A->B) [n] (v : vec A n)
  (H : forall a, f a = g a) : map f v = map g v.
Proof. erewrite <-to_list_inj_iff, !to_list_map, List.map_ext; trivial. Qed.

Lemma map_app_vec [A B] (f : A -> B) [n m] (v: vec A n) (w: vec A m) :
  map f (v ++ w) = map f v ++ map f w.
Proof. erewrite <-to_list_inj_iff, to_list_app, 3 to_list_map, to_list_app, List.map_app; trivial. Qed.

Lemma map_snoc [A B] (f : A -> B) [n] (v : vec A n) a :
  map f (snoc v a) = snoc (map f v) (f a).
Proof. induction v; cbn [map snoc]; auto using f_equal. Qed.


(** * [fold_right] *)

Lemma fold_right_snoc [A B] f (a : A) (b : B) n (v : vec A n) :
  fold_right f (snoc v a) b = fold_right f v (f a b).
Proof. induction v; cbn [snoc fold_right]; rewrite ?IHv; trivial. Qed.

Lemma fold_right_rev [A B] (f : A -> B -> B) [n] (v : vec A n) b :
  fold_right f (rev v) b = fold_left (fun x y => f y x) b v.
Proof.
  revert b; induction v; intros; rewrite ?rev_nil, ?rev_cons_snoc, ?fold_right_snoc; trivial.
Qed.


(** * [cast] *)

Lemma cast_nil [A] p : cast [] p = [] :> vec A 0.
Proof. trivial. Qed.

Lemma cast_cons [A m] a (v : vec A m) [n] p :
  cast ((a :: v)) p = (a :: (cast v (Nat.succ_inj _ _ p))) :> vec A (S n).
Proof. apply to_list_inj; repeat rewrite ?to_list_cast, ?to_list_cons; trivial. Qed.

Lemma cast_refl [A n] (v : vec A n) p : cast v p = v.
Proof. apply to_list_inj; repeat rewrite ?to_list_cast; trivial. Qed.

Lemma cast_ext [A m] (v : vec A m) [n] p q : cast v p = cast v q :> vec A n.
Proof. apply to_list_inj; repeat rewrite ?to_list_cast; trivial. Qed.


(** * [put] *)

Lemma put_alt_subproof : forall x x0 : nat, Nat.min x x0 + (x - x0) = x.
Proof.
  intros n i; destruct (Nat.le_ge_cases n i) as [H|H].
  { rewrite Nat.min_l, (proj2 (Nat.sub_0_le _ _) H), Nat.add_0_r; trivial. }
  { rewrite Nat.min_r, Nat.add_comm; auto using Nat.sub_add. }
Qed.

Lemma put_alt [A n] (v : vec A n) (i : nat) (a : A) :
  put v i a = cast (app (firstn v i) (match skipn v i with [] => [] | (_ :: v) => (a :: v) end)) (put_alt_subproof n i).
Proof.
  revert i; induction v, i; cbn [put firstn app skipn Nat.min Nat.sub Nat.add];
    rewrite ?cast_refl, ?cast_cons, ?IHv; auto using f_equal, cast_ext.
Qed.

Lemma nth_error_to_list [A n] (v : vec A n) i : List.nth_error v (Fin.toNat i) = Some (getFin v i).
Proof. induction v; [case Fin.inj_0 | case (Fin.inj_S i) as [->|[? ->] ] ]; cbn; eauto. Qed.

Lemma getFin_inj [A n] (v w : vec A n)
  (H : forall i, getFin v i = getFin w i) : v = w.
Proof.
  apply to_list_inj, List.nth_error_ext; intros i.
  case (Nat.ltb_spec i n) as [Hi|].
  { rewrite <-(Fin.toNat_mk i n Hi), !nth_error_to_list; auto using f_equal. }
  { rewrite 2 (proj2 (List.nth_error_None _ _)); rewrite ?length_to_list; auto. }
Qed.

Lemma getFin_inj_iff [A n] (v w : vec A n) :
  (forall i, getFin v i = getFin w i) <-> v = w.
Proof. split; [apply getFin_inj | intros ->; auto]. Qed.


(** * Properties of the predicates and of [to_list], continued *)

Lemma map2_ext [A B C] (f g : A -> B -> C) (Hfg : forall a b, f a b = g a b)
  [n] (v : vec A n) (w : vec B n) : map2 f v w = map2 g v w.
Proof.
  revert w; induction v as [|a n v IH]; intros w.
  - rewrite (inj_0 w); reflexivity.
  - rewrite (inj_S w); cbn; f_equal; auto.
Qed.

Lemma fold_left_right_assoc_eq {A B} {f: A -> B -> A}
  (assoc: forall a b c, f (f a b) c = f (f a c) b)
  {n} (v: vec B n): forall a, fold_left f a v = fold_right (fun x y => f y x) v a.
Proof.
assert (forall n h (v: vec B n) a, fold_left f (f a h) v = f (fold_left f a v) h).
- intros n0 h v0; induction v0 as [|? ? v0 IHv0].
  + now simpl.
  + intros; simpl. rewrite<- IHv0, assoc. now f_equal.
- induction v as [|? ? v IHv].
  + reflexivity.
  + simpl. intros; now rewrite<- (IHv).
Qed.

Lemma app_comm_cons {A} : forall {n m : nat} (v : vec A n) (w : vec A m) (a : A),
  a :: (v ++ w) = (a :: v) ++ w.
Proof. reflexivity. Qed.

Lemma app_inj {A} : forall {n m : nat} (v v' : vec A n) (w w' : vec A m),
  v ++ w = v' ++ w' -> v = v' /\ w = w'.
Proof.
intros n m v; induction v as [|a n v IH]; intros v' w w' E.
- rewrite (inj_0 v') in *. auto.
- rewrite (inj_S v') in *. cbn in E.
  specialize (IH (tl v') w w' (f_equal (@tl _ _) E)) as [-> ->].
  split; [f_equal; exact (f_equal (@hd _ _) E)|reflexivity].
Qed.

Lemma In_cons_iff A: forall n a b (v : vec A n),
  In a (b :: v) <-> (b = a \/ In a v).
Proof.
intros n a b v. split.
- enough (H : forall n (v : vec A n), In a v ->
    match v with
    | nil _ => False
    | cons _ b _ v => b = a \/ In a v
    end) by apply H.
  now intros ?? []; [left|right].
- intros [<-|?].
  + apply In_cons_hd.
  + now apply In_cons_tl.
Qed.

Lemma Forall_impl A: forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall n (v : vec A n), Forall P v -> Forall Q v.
Proof.
intros P Q H n v HPv. now induction HPv; constructor; [apply H|].
Qed.

Lemma Forall_forall A: forall P n (v : vec A n),
  Forall P v <-> forall a, In a v -> P a.
Proof.
intros P n v. split.
- intros H. induction H.
  + easy.
  + intros a [<-|?]%In_cons_iff; auto.
- induction v as [|? ? v IHv]; intros Hin; constructor.
  + apply Hin; constructor.
  + apply IHv; intros a Ha.
    apply Hin; now constructor.
Qed.

Lemma Forall_cons_iff A: forall (P : A -> Prop) a n (v : vec A n),
  Forall P (a :: v) <-> P a /\ Forall P v.
Proof.
intros P a n v. split.
- rewrite !Forall_forall. intros H. split.
  + apply H, In_cons_hd.
  + intros b Hb. apply H, In_cons_tl, Hb.
- intros [??]. now constructor.
Qed.

Lemma Forall_map A B: forall (P : B -> Prop) (f : A -> B) n (v : vec A n),
  Forall P (map f v) <-> Forall (fun x => P (f x)) v.
Proof.
intros P f n v. induction v as [|a n v IH].
- split; constructor.
- cbn. now rewrite !Forall_cons_iff, IH.
Qed.

Lemma Forall_app A: forall P n m (v : vec A n) (w : vec A m),
  Forall P v -> Forall P w -> Forall P (v ++ w).
Proof.
intros ????? H ?. induction H.
- easy.
- now constructor.
Qed.

Lemma Forall2_cons_iff A B: forall P n h1 h2 (v1 : vec A n) (v2 : vec B n),
  Forall2 P (h1 :: v1) (h2 :: v2) <-> P h1 h2 /\ Forall2 P v1 v2.
Proof.
  intros P n h1 h2 v1 v2; split.
  2: { intros [H1 H2]; right; [exact H1 | exact H2]. }
  intros H; inversion H as [| m x1 x2 v0 v3 ph f2p mn [x1h1 H1] [x2h2 H2]].
  split; [exact ph |].
  apply inj_pair2_eq_dec in H1 as ->; [| exact Nat.eq_dec].
  apply inj_pair2_eq_dec in H2 as ->; [| exact Nat.eq_dec].
  exact f2p.
Qed.

Lemma Forall2_app A B: forall P n m (v : vec A n) (v' : vec B n) (w : vec A m) (w' : vec B m),
  Forall2 P v v' -> Forall2 P w w' -> Forall2 P (v ++ w) (v' ++ w').
Proof.
intros ??????? H ?. induction H.
- easy.
- now constructor.
Qed.

Lemma In_snoc A: forall a b n (v : vec A n),
  In a (snoc v b) <-> (b = a \/ In a v).
Proof.
intros a b n v. induction v as [|c n v IH].
- apply In_cons_iff.
- cbn. rewrite !In_cons_iff. tauto.
Qed.

Lemma Forall_snoc A: forall (P : A -> Prop) a n (v : vec A n),
  Forall P (snoc v a) <-> (P a /\ Forall P v).
Proof.
intros P a n v. induction v as [|b n v IH].
- apply Forall_cons_iff.
- cbn. rewrite !Forall_cons_iff. tauto.
Qed.

Lemma In_rev A: forall a n (v : vec A n),
  In a (rev v) <-> In a v.
Proof.
intros a n v. induction v as [|b n v IH].
- now rewrite rev_nil.
- now rewrite rev_cons_snoc, In_snoc, In_cons_iff, IH.
Qed.

Lemma Forall_rev A: forall (P : A -> Prop) n (v : vec A n),
  Forall P (rev v) <-> Forall P v.
Proof.
intros P n v. induction v as [|a n v IH].
- now rewrite rev_nil.
- now rewrite rev_cons_snoc, Forall_snoc, Forall_cons_iff, IH.
Qed.

Lemma of_list_to_list_opp A n (v: vec A n):
  rew length_to_list _ _ _ in of_list (to_list v) = v.
Proof.
induction v as [ | h n v IHv ].
- apply inj_0.
- replace (length_to_list _ _ (cons _ h _ v)) with (f_equal S (length_to_list _ _ v))
    by apply (UIP_dec Nat.eq_dec).
  cbn; rewrite map_subst_map.
  f_equal.
  now etransitivity; [ | apply IHv].
Qed.

Lemma to_list_nil_iff A v:
  to_list v = List.nil <-> v = nil A.
Proof.
split; intro H.
- now rewrite (inj_0 v).
- subst. apply to_list_nil.
Qed.

Lemma to_list_rev_append A n m (v1 : vec A n) (v2 : vec A m):
  to_list (rev_append v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. cbv [rev_append]. rewrite to_list_cast, to_list_of_list; trivial. Qed.

Lemma to_list_fold_left A B f (b : B) n (v : vec A n):
  fold_left f b v = List.fold_left f (to_list v) b.
Proof. now revert b; induction v; cbn. Qed.

Lemma to_list_fold_right A B f (b : B) n (v : vec A n):
  fold_right f v b = List.fold_right f b (to_list v).
Proof. now revert b; induction v; cbn; intros; f_equal. Qed.

Lemma to_list_Forall A P n (v : vec A n):
  Forall P v <-> List.Forall P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; constructor; auto.
Qed.

Lemma to_list_Exists A P n (v : vec A n):
  Exists P v <-> List.Exists P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; now constructor; auto.
Qed.

Lemma to_list_Forall2 A B P n (v1 : vec A n) (v2 : vec B n) :
  Forall2 P v1 v2 <-> List.Forall2 P (to_list v1) (to_list v2).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v1) as l1.
  remember (to_list v2) as l2.
  revert n v1 v2 Heql1 Heql2; induction HF; intros n v1 v2 Heql1 Heql2.
  + destruct v1; [ | inversion Heql1 ].
    rewrite (inj_0 v2); constructor.
  + destruct v1; inversion Heql1; subst.
    rewrite (inj_S v2) in Heql2; inversion Heql2; subst.
    rewrite (inj_S v2); constructor; auto.
Qed.

(** * The historical interface, deprecated *)

#[local] Set Warnings "-deprecated".


(** The historical lemmas live in the deprecated file [VectorSpec]; they are
    reachable here under their old names, deprecated. *)
From Stdlib Require VectorSpec.
From Stdlib Require VectorEq.

#[deprecated(since="9.4", use=getFin)]
Abbreviation nth_getFin := VectorSpec.nth_getFin (only parsing).
#[deprecated(since="9.4", use=getLt)]
Abbreviation nth_order_getLt := VectorSpec.nth_order_getLt (only parsing).
#[deprecated(since="9.4", use=putFin)]
Abbreviation replace_putFin := VectorSpec.replace_putFin (only parsing).
#[deprecated(since="9.4", use=putLt)]
Abbreviation replace_order_putLt := VectorSpec.replace_order_putLt (only parsing).
#[deprecated(since="9.4", use=snoc)]
Abbreviation shiftin_snoc := VectorSpec.shiftin_snoc (only parsing).
#[deprecated(since="9.4", use=firstn)]
Abbreviation take_firstn_dep := VectorSpec.take_firstn_dep (only parsing).
#[deprecated(since="9.4", use=firstn)]
Abbreviation take_firstn := VectorSpec.take_firstn (only parsing).
#[deprecated(since="9.4", use=unapp)]
Abbreviation splitat_unapp := VectorSpec.splitat_unapp (only parsing).
#[deprecated(since="9.4", use=rev_append)]
Abbreviation rev_append_tail_rev_append := VectorSpec.rev_append_tail_rev_append (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this definition, please open an issue.")]
Abbreviation cons_inj := VectorSpec.cons_inj (only parsing).
#[deprecated(since="9.4", use=inj_0)]
Abbreviation nil_spec := VectorSpec.nil_spec (only parsing).
#[deprecated(since="9.4", use=inj_S)]
Abbreviation eta := VectorSpec.eta (only parsing).
#[deprecated(since="9.4", use=getFin_inj_iff)]
Abbreviation eq_nth_iff := VectorSpec.eq_nth_iff (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_order_hd := VectorSpec.nth_order_hd (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_order_tl := VectorSpec.nth_order_tl (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_order_last := VectorSpec.nth_order_last (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_order_ext := VectorSpec.nth_order_ext (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_append_L := VectorSpec.nth_append_L (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation nth_append_R := VectorSpec.nth_append_R (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation In_nth := VectorSpec.In_nth (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_replace_eq := VectorSpec.nth_replace_eq (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_replace_neq := VectorSpec.nth_replace_neq (only parsing).
#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_order_replace_eq := VectorSpec.nth_order_replace_eq (only parsing).
#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_order_replace_neq := VectorSpec.nth_order_replace_neq (only parsing).
#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation replace_id := VectorSpec.replace_id (only parsing).
#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation replace_replace_eq := VectorSpec.replace_replace_eq (only parsing).
#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation replace_replace_neq := VectorSpec.replace_replace_neq (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation replace_append_L := VectorSpec.replace_append_L (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation replace_append_R := VectorSpec.replace_append_R (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation const_nth := VectorSpec.const_nth (only parsing).
#[deprecated(since="9.4", use=app_repeat_repeat)]
Abbreviation append_const := app_repeat_repeat (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_map := VectorSpec.nth_map (only parsing).
#[deprecated(since="9.4", use=map_app_vec)]
Abbreviation map_append := map_app_vec (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation nth_map2 := VectorSpec.nth_map2 (only parsing).
#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation take_O := VectorSpec.take_O (only parsing).
#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation take_idem := VectorSpec.take_idem (only parsing).
#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation take_app := VectorSpec.take_app (only parsing).
#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation take_prf_irr := VectorSpec.take_prf_irr (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation uncons_cons := VectorSpec.uncons_cons (only parsing).
#[deprecated(since="9.4", use=unapp, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation splitat_append := VectorSpec.splitat_append (only parsing).
#[deprecated(since="9.4", use=unapp, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation append_splitat := VectorSpec.append_splitat (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation Forall_nth := VectorSpec.Forall_nth (only parsing).
#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation Forall_nth_order := VectorSpec.Forall_nth_order (only parsing).
#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation Forall2_nth := VectorSpec.Forall2_nth (only parsing).
#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation Forall2_nth_order := VectorSpec.Forall2_nth_order (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation shiftin_nth := VectorSpec.shiftin_nth (only parsing).
#[deprecated(since="9.4", use=snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation shiftin_last := VectorSpec.shiftin_last (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation shiftrepeat_nth := VectorSpec.shiftrepeat_nth (only parsing).
#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Abbreviation shiftrepeat_last := VectorSpec.shiftrepeat_last (only parsing).
#[deprecated(since="9.4", use=map_snoc)]
Abbreviation map_shiftin := VectorSpec.map_shiftin (only parsing).
#[deprecated(since="9.4", use=fold_right_snoc)]
Abbreviation fold_right_shiftin := VectorSpec.fold_right_shiftin (only parsing).
#[deprecated(since="9.4", use=In_snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation In_shiftin := VectorSpec.In_shiftin (only parsing).
#[deprecated(since="9.4", use=Forall_snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation Forall_shiftin := VectorSpec.Forall_shiftin (only parsing).
#[deprecated(since="9.4", use=rev_cons_snoc)]
Abbreviation rev_cons := VectorSpec.rev_cons (only parsing).
#[deprecated(since="9.4", use=rev_snoc)]
Abbreviation rev_shiftin := VectorSpec.rev_shiftin (only parsing).
#[deprecated(since="9.4", use=fold_right_rev)]
Abbreviation fold_left_rev_right := fold_right_rev (only parsing).
#[deprecated(since="9.4", use=to_list_of_list)]
Abbreviation to_list_of_list_opp := to_list_of_list (only parsing).
#[deprecated(since="9.4", use=hd_to_list)]
Abbreviation to_list_hd := hd_to_list (only parsing).
#[deprecated(since="9.4", use=last_to_list)]
Abbreviation to_list_last := last_to_list (only parsing).
#[deprecated(since="9.4", use=to_list_repeat)]
Abbreviation to_list_const := to_list_repeat (only parsing).
#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation to_list_nth_order := VectorSpec.to_list_nth_order (only parsing).
#[deprecated(since="9.4", use=to_list_app)]
Abbreviation to_list_append := to_list_app (only parsing).
#[deprecated(since="9.4", use=rev_append, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Abbreviation to_list_rev_append_tail := VectorSpec.to_list_rev_append_tail (only parsing).
#[deprecated(since="9.4", use=app_comm_cons)]
Abbreviation append_comm_cons := app_comm_cons (only parsing).
#[deprecated(since="9.4", use=app_inj)]
Abbreviation append_inj := app_inj (only parsing).
#[deprecated(since="9.4", use=Forall_app)]
Abbreviation Forall_append := Forall_app (only parsing).
#[deprecated(since="9.4", use=Forall2_app)]
Abbreviation Forall2_append := Forall2_app (only parsing).
