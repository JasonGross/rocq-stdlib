(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the historical Vector interface.

    Every lemma of this file is deprecated: the new interface and its lemmas
    are in [Vector], which requires this file. The deprecated lemmas stay here
    so that [Require VectorSpec] and the names [VectorSpec.x] keep working. The
    file itself carries no deprecation attribute, because [Vector] requires it
    and a deprecated library would warn on every [Require Vector]. *)
#[local] Set Warnings "-deprecated".
From Stdlib Require Fin List.
From Stdlib Require Import VectorDef PeanoNat Eqdep_dec.
Import VectorNotations EqNotations.

(** Copies of the lemmas of [Vector] that the proofs below use. They are
    private to this file; use the ones of [Vector]. *)
Module Private.
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

End Private.
Import Private.

(** ** The deprecated operations in terms of the new ones *)

#[deprecated(since="9.4", use=getFin)]
Lemma nth_getFin A n v i : @nth A n v i = @getFin A n v i.
Proof. induction i; trivial; try rewrite (inj_S v); cbn; trivial. Qed.

#[deprecated(since="9.4", use=getLt)]
Lemma nth_order_getLt [A n] v p H : @nth_order A n v p H = @getLt A n v p H.
Proof. cbv [nth_order getLt]. rewrite nth_getFin, Fin.of_nat_lt_mk; trivial. Qed.

#[deprecated(since="9.4", use=putFin)]
Lemma replace_putFin A n v i x : @replace A n v i x = @putFin A n v i x.
Proof. induction i; trivial; try rewrite (inj_S v); cbn; congruence. Qed.

#[deprecated(since="9.4", use=putLt)]
Lemma replace_order_putLt [A n] v p H x : @replace_order A n v p H x = @putLt A n v p H x.
Proof. cbv [replace_order putLt]. rewrite replace_putFin, Fin.of_nat_lt_mk; trivial. Qed.

#[deprecated(since="9.4", use=snoc)]
Lemma shiftin_snoc [A n] x v : @shiftin A n x v = @snoc A n v x.
Proof. induction v; cbn; congruence. Qed.

#[deprecated(since="9.4", use=firstn)]
Lemma take_firstn_dep [A n] p le v : existT _ _ (@take A n p le v) = existT _ _ (@firstn A n v p).
Proof.
  revert dependent p; induction v, p; cbn [Nat.min take firstn]; auto;
    [pose proof Nat.nle_succ_0 p; contradiction|intros].
  specialize (IHv _ (le_S_n p n le)); symmetry in IHv; inversion_sigma.
  rewrite <-IHv2; clear IHv2.
  apply to_list_inj_dep.
  rewrite 2 to_list_cons, to_list_eq_rect; trivial.
Qed.

#[deprecated(since="9.4", use=firstn)]
Lemma take_firstn [A n] p le v : @take A n p le v = cast (@firstn A n v p) (Nat.min_r _ _ le).
Proof.
  pose proof eq_sym (take_firstn_dep p le v) as Hr; inversion_sigma.
  rewrite <-Hr2; clear Hr2.
  apply to_list_inj; rewrite to_list_eq_rect, to_list_cast; trivial.
Qed.

#[deprecated(since="9.4", use=unapp)]
Lemma splitat_unapp {A} l r v : @splitat A l r v = @unapp A l r v.
Proof. induction l; cbn; rewrite <-?IHl; trivial. Qed.

#[deprecated(since="9.4", use=rev_append)]
Lemma rev_append_tail_rev_append [A n p] v w : existT _ _ (@rev_append_tail A n p v w) = existT _ _ (@rev_append A n p v w).
Proof.
  revert dependent p; induction v; intros.
  { cbv [rev_append];
    apply to_list_inj_dep;
    rewrite ?to_list_cast, ?to_list_of_list; cbn; rewrite ?IHv; trivial. }
  { cbn; rewrite IHv.
    apply to_list_inj_dep; cbv [rev_append].
    rewrite ?to_list_cast, ?to_list_cons, ?to_list_of_list.
    rewrite !List.rev_append_rev; cbn; rewrite <-!List.app_assoc; trivial. }
Qed.


(** * Properties of the historical interface *)

#[deprecated(since="9.4", note="If you would like stdlib to keep this definition, please open an issue.")]
Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.

#[deprecated(since="9.4", use=inj_0)]
Lemma nil_spec {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.

#[deprecated(since="9.4", use=inj_S)]
Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.

(** Lemmas are done for functions that use [Fin.t] but thanks to [Peano_dec.le_unique], all
is true for the one that use [lt] *)

(** ** Properties of [nth] and [nth_order] *)

#[deprecated(since="9.4", use=getFin_inj_iff)]
Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
  rewrite <-getFin_inj_iff; repeat setoid_rewrite nth_getFin.
  split; intros; subst; eauto.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_order_hd A: forall n (v : t A (S n)) (H : 0 < S n),
  nth_order v H = hd v.
Proof. intros n v H; now rewrite (eta v). Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_order_tl A: forall n k (v : t A (S n)) (H : k < n) (HS : S k < S n),
  nth_order (tl v) H = nth_order v HS.
Proof.
intros n; induction n; intros k v H HS.
- inversion H.
- rewrite (eta v).
  unfold nth_order; simpl.
  now rewrite (Fin.of_nat_ext H (proj2 (Nat.succ_lt_mono _ _) HS)).
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
  nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now simpl.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_order_ext A: forall n k (v : t A n) (H1 H2 : k < n),
  nth_order v H1 = nth_order v H2.
Proof.
intros n k v H1 H2; unfold nth_order.
now rewrite (Fin.of_nat_ext H1 H2).
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_append_L A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.L m p] = v [@ p].
Proof.
intros n m v w. induction v as [|a n v IH].
- apply Fin.case0.
- intros p. now apply (Fin.caseS' p).
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma nth_append_R A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.R n p] = w [@ p].
Proof.
intros n m v w. now induction v.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma In_nth A: forall n (v : t A n) p,
  In (nth v p) v.
Proof.
intros n v. induction v as [|a n v IH].
- apply Fin.case0.
- intros p. apply (Fin.caseS' p).
  + apply In_cons_hd.
  + intros q. apply In_cons_tl, IH.
Qed.

(** ** Properties of [replace] *)

#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma nth_replace_eq A: forall n p (v : t A n) a,
  nth (replace v p a) p = a.
Proof.
intros n p v a. induction v.
- now apply Fin.case0.
- now apply (Fin.caseS' p).
Qed.

#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma nth_replace_neq A: forall n p q, p <> q -> forall (v : t A n) a,
  nth (replace v q a) p = nth v p.
Proof.
intros n p q Hpq v a.
induction v as [|b n v IH]; revert Hpq.
- now apply Fin.case0.
- apply (Fin.caseS' p); apply (Fin.caseS' q); [easy..|].
  intros ???. apply IH. contradict Hpq. now f_equal.
Qed.

#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma nth_order_replace_eq A: forall n k (v : t A n) a (H1 : k < n) (H2 : k < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros n k v a H1 H2.
rewrite (Fin.of_nat_ext H2 H1).
apply nth_replace_eq.
Qed.

#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma nth_order_replace_neq A: forall n k1 k2, k1 <> k2 ->
  forall (v : t A n) a (H1 : k1 < n) (H2 : k2 < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = nth_order v H1.
Proof.
intros n k1 k2 H v a H1 H2.
unfold nth_order. rewrite nth_replace_neq; [reflexivity|].
intros E. apply H.
apply (f_equal (fun p => proj1_sig (Fin.to_nat p))) in E.
now rewrite !Fin.to_nat_of_nat in E.
Qed.

#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma replace_id A: forall n p (v : t A n),
  replace v p (nth v p) = v.
Proof.
intros n p; induction p as [|? p IHp]; intros v; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma replace_replace_eq A: forall n p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros n p v a b.
induction p as [|? p IHp]; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

#[deprecated(since="9.4", use=putFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma replace_replace_neq A: forall n p1 p2 (v : t A n) a b, p1 <> p2 ->
  replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a.
Proof.
apply (Fin.rect2 (fun n p1 p2 => forall v a b,
  p1 <> p2 -> replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a)).
- intros n v a b Hneq.
  now contradiction Hneq.
- intros n p2 v; revert n v p2.
  refine (@rectS _ _ _ _); auto.
- intros n p1 v; revert n v p1.
  refine (@rectS _ _ _ _); auto.
- intros n p1 p2 IH v; revert n v p1 p2 IH.
  refine (@rectS _ _ _ _); simpl; intro n; [| do 3 intro]; intros ? ? IH p1 p2; intro Hneq;
    f_equal; apply IH; intros Heq; apply Hneq; now subst.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma replace_append_L A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.L m p) a = (replace v p a) ++ w.
Proof.
intros n m v w p a. induction v as [|b n v IH].
- now apply Fin.case0.
- apply (Fin.caseS' p).
  + reflexivity.
  + intros p'. cbn. apply f_equal, IH.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma replace_append_R A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.R n p) a = v ++ (replace w p a).
Proof.
intros n m v w p a. induction v as [|b n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

(** ** Properties of [const] *)

#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.


(** ** Properties of [map] *)





#[deprecated(since="9.4", use=app_repeat_repeat)]
Abbreviation append_const := Private.app_repeat_repeat (only parsing).

#[deprecated(since="9.4", use=getFin_map)]
Lemma nth_map {A B} (f: A -> B) {n} v (p1 p2: Fin.t n) (eq: p1 = p2):
  (map f v) [@ p1] = f (v [@ p2]).
Proof.
subst p2; induction p1 as [n|n p1 IHp1].
- revert n v; refine (@caseS _ _ _); reflexivity.
- revert n v p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.


#[deprecated(since="9.4", use=map_app_vec)]
Abbreviation map_append := Private.map_app_vec (only parsing).

#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma nth_map2 {A B C} (f: A -> B -> C) {n} v w (p1 p2 p3: Fin.t n):
  p1 = p2 -> p2 = p3 -> (map2 f v w) [@p1] = f (v[@p2]) (w[@p3]).
Proof.
intros; subst p2; subst p3; revert n v w p1.
refine (@rect2 _ _ _ _ _); simpl.
- exact (Fin.case0 _).
- intros n v1 v2 H a b p; revert n p v1 v2 H; refine (@Fin.caseS _ _ _);
    now simpl.
Qed.


(** ** Properties of [fold_left] *)


(** ** Properties of [take] *)

#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof.
  reflexivity.
Qed.

#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma take_idem : forall {A} p n (v:t A n) le le',
  take p le' (take p le v) = take p le v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - reflexivity.
  - destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.

#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma take_app : forall {A} {n} (v:t A n) {m} (w:t A m) le, take n le (append v w) = v.
Proof.
  intros a n v; induction v as [|? ? v IHv]; intros m w le.
  - reflexivity.
  - simpl. apply f_equal, IHv.
Qed.

(* Proof is irrelevant for [take] *)
#[deprecated(since="9.4", use=firstn, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma take_prf_irr : forall {A} p {n} (v:t A n) le le', take p le v = take p le' v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - reflexivity.
  - destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.

(** ** Properties of [uncons] and [splitat] *)

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma uncons_cons {A} : forall {n : nat} (a : A) (v : t A n),
  uncons (a::v) = (a,v).
Proof. reflexivity. Qed.

(* [append] *)


#[deprecated(since="9.4", use=unapp_app)]
Lemma splitat_append {A} : forall {n m : nat} (v : t A n) (w : t A m),
  splitat n (v ++ w) = (v, w).
Proof.
  intros n m v w. induction v as [|a n v IH].
  - reflexivity.
  - cbn. now rewrite IH.
Qed.

#[deprecated(since="9.4", use=app_unapp)]
Lemma append_splitat {A} : forall {n m : nat} (v : t A n) (w : t A m) (vw : t A (n+m)),
  splitat n vw = (v, w) -> vw = v ++ w.
Proof.
intros n m v w vw E.
assert (v = fst (splitat n vw)) as -> by now rewrite E.
assert (w = snd (splitat n vw)) as -> by now rewrite E.
clear E. induction n as [|n IH].
- reflexivity.
- cbn. specialize (IH (tl vw)).
  destruct (splitat n (tl vw)) as [??].
  rewrite (eta vw). cbn. apply f_equal, IH.
Qed.


(** ** Properties of [In] *)


(** ** Properties of [Forall] and [Forall2] *)






#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma Forall_nth A: forall P n (v : t A n),
  Forall P v <-> forall p, P (nth v p).
Proof.
intros P n v. split.
- intros H. induction H.
  + apply Fin.case0.
  + intros p. now apply (Fin.caseS' p).
- induction v as [|a v n IH].
  + intros ?. constructor.
  + intros H. constructor.
    * apply (H Fin.F1).
    * apply IH. intros p. apply (H (Fin.FS p)).
Qed.

#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma Forall_nth_order A: forall P n (v : t A n),
  Forall P v <-> forall i (Hi : i < n), P (nth_order v Hi).
Proof.
intros P n v. rewrite Forall_nth. split.
- intros H i Hi. apply H.
- intros H p.
  rewrite <- (Fin.of_nat_to_nat_inv p).
  apply H.
Qed.


#[deprecated(since="9.4", use=getFin, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma Forall2_nth A: forall P n (v1 v2 : t A n),
  Forall2 P v1 v2 <-> forall p, P (nth v1 p) (nth v2 p).
Proof.
intros P n v1 v2. split.
- intros H. induction H.
  + apply Fin.case0.
  + intros p. now apply (Fin.caseS' p).
- apply (fun P H1 H2 => rect2 P H1 H2 v1 v2).
  + constructor.
  + intros ??? IH ?? H. constructor.
    * apply (H Fin.F1).
    * apply IH. intros p. apply (H (Fin.FS p)).
Qed.

#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma Forall2_nth_order A: forall P n (v1 v2 : t A n),
     Forall2 P v1 v2
 <-> forall i (Hi1 : i < n) (Hi2 : i < n), P (nth_order v1 Hi1) (nth_order v2 Hi2).
Proof.
intros P n v1 v2. rewrite Forall2_nth. split.
- intros H i Hi1 Hi2.
  rewrite (nth_order_ext _ _ _ _ Hi1 Hi2).
  apply H.
- intros H p.
  rewrite <- (Fin.of_nat_to_nat_inv p).
  apply H.
Qed.


(** ** Properties of [shiftin] and [shiftrepeat] *)

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma shiftin_nth A a n (v: t A n) k1 k2 (eq: k1 = k2):
  nth (shiftin a v) (Fin.L_R 1 k1) = nth v k2.
Proof.
subst k2; induction k1 as [n|n k1 IH].
- revert n v. now apply caseS.
- revert k1 IH. apply (fun P IS => caseS P IS v). now simpl.
Qed.

#[deprecated(since="9.4", use=snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma shiftin_last A a n (v: t A n): last (shiftin a v) = a.
Proof.
induction v; now simpl.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma shiftrepeat_nth A: forall n k (v: t A (S n)),
  nth (shiftrepeat v) (Fin.L_R 1 k) = nth v k.
Proof.
intros n k.
apply (fun P P0 PS => Fin.rectS P P0 PS k); clear n k.
- intros [|n] v; rewrite (eta v); [|reflexivity].
  now rewrite (nil_spec (tl v)).
- intros n k IH v. rewrite (eta v). apply IH.
Qed.

#[deprecated(since="9.4", note="If you would like stdlib to keep this lemma, please open an issue.")]
Lemma shiftrepeat_last A: forall n (v: t A (S n)), last (shiftrepeat v) = last v.
Proof.
refine (@rectS _ _ _ _); now simpl.
Qed.

#[deprecated(since="9.4", use=map_snoc)]
Lemma map_shiftin A B: forall (f : A -> B) a n (v : t A n),
  map f (shiftin a v) = shiftin (f a) (map f v).
Proof.
intros f a n v. induction v as [|b n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

#[deprecated(since="9.4", use=fold_right_snoc)]
Lemma fold_right_shiftin A B: forall (f : A -> B -> B) a b n (v : t A n),
  fold_right f (shiftin b v) a = fold_right f v (f b a).
Proof.
intros f a b n v. induction v as [|c n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

#[deprecated(since="9.4", use=In_snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma In_shiftin A: forall a b n (v : t A n),
  In a (shiftin b v) <-> (b = a \/ In a v).
Proof.
intros a b n v. induction v as [|c n v IH].
- apply In_cons_iff.
- cbn. rewrite !In_cons_iff. tauto.
Qed.

#[deprecated(since="9.4", use=Forall_snoc, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma Forall_shiftin A: forall (P : A -> Prop) a n (v : t A n),
  Forall P (shiftin a v) <-> (P a /\ Forall P v).
Proof.
intros P a n v. induction v as [|b n v IH].
- apply Forall_cons_iff.
- cbn. rewrite !Forall_cons_iff. tauto.
Qed.

(** ** Properties of [rev] *)


#[deprecated(since="9.4", use=rev_cons_snoc)]
Lemma rev_cons A: forall a n (v : t A n), rev (a :: v) = shiftin a (rev v).
Proof. intros; rewrite shiftin_snoc; apply rev_cons_snoc. Qed.

#[deprecated(since="9.4", use=rev_snoc)]
Lemma rev_shiftin A: forall a n (v : t A n),
  rev (shiftin a v) = a :: rev v.
Proof. intros; rewrite shiftin_snoc; apply rev_snoc. Qed.






(** ** Properties of [to_list] *)











#[deprecated(since="9.4", use=fold_right_rev)]
Abbreviation fold_left_rev_right := Private.fold_right_rev (only parsing).

#[deprecated(since="9.4", use=to_list_of_list)]
Abbreviation to_list_of_list_opp := Private.to_list_of_list (only parsing).

#[deprecated(since="9.4", use=hd_to_list)]
Abbreviation to_list_hd := Private.hd_to_list (only parsing).

#[deprecated(since="9.4", use=last_to_list)]
Abbreviation to_list_last := Private.last_to_list (only parsing).

#[deprecated(since="9.4", use=to_list_repeat)]
Abbreviation to_list_const := Private.to_list_repeat (only parsing).

#[deprecated(since="9.4", use=getLt, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma to_list_nth_order A n (v : t A n) p (H : p < n) d:
  nth_order v H = List.nth p (to_list v) d.
Proof.
unfold nth_order. revert p H.
induction v as [|a n v IH].
- intros p H. destruct (Nat.nlt_0_r p H).
- intros [|p] ?; [ reflexivity | apply IH ].
Qed.



#[deprecated(since="9.4", use=to_list_app)]
Abbreviation to_list_append := Private.to_list_app (only parsing).

#[deprecated(since="9.4", use=rev_append, note="Stated for a deprecated operation; see the lemmas about vec in Vector.")]
Lemma to_list_rev_append_tail A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append_tail v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. now revert m v2; induction v1 as [ | ? ? ? IHv1 ]; intros; [ | simpl; rewrite IHv1 ]. Qed.










