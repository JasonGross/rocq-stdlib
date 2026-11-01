(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The data structure is [Stdlib.EMaps.Trie]; this file only adds the
    [FMapInterface] specifications. Authors of the trie: Andrew W. Appel,
    Xavier Leroy, Andres Erbsen. *)

From Stdlib Require Import Bool PeanoNat PArith List SetoidList.
From Stdlib Require Import OrderedType OrderedTypeEx FMapInterface EMaps.Trie.

(** * FMapTrie : the extensional tries of [EMaps.Trie] as an instance of [FMapInterface.S] *)

(** The functions below that need the key of each binding ([elements],
    [fold], [mapi]) carry the current path in the trie as an extra
    [positive] argument, in reverse order, as in [FMapPositive]. The proofs
    follow [FMapPositive]: [trie_ind] replaces the structural induction on
    trees, and one [_Node] equation per operation replaces [simpl]. *)

#[local] Set Implicit Arguments.
#[local] Unset Strict Implicit.

Module TrieMap <: S with Module E := PositiveOrderedTypeBits.

  Module E := PositiveOrderedTypeBits.
  Module ME := KeyOrderedType E.

  Definition key := positive : Type.

  (** Reverses the positive [y] and concatenate it with [x] *)

  Fixpoint rev_append (y x : positive) : positive :=
    match y with
    | xH => x
    | xI y => rev_append y (xI x)
    | xO y => rev_append y (xO x)
    end.
  Local Infix "@" := rev_append (at level 60).
  Definition rev x := x@xH.

  Definition t := trie.

  Section A.
  Variable A:Type.

  Definition empty : t A := empty A.

  Definition is_empty (m : t A) := match m with None => true | _ => false end.

  Definition find (i : key) (m : t A) : option A := get i m.

  Definition mem (i : key) (m : t A) : bool :=
    match get i m with Some _ => true | _ => false end.

  Definition add (i : key) (v : A) (m : t A) : t A := set i v m.

  Definition remove (i : key) (m : t A) : t A := remove i m.

  (** [elements] *)

  Definition elements (m : t A) : list (key*A) := to_list m.

  (** [cardinal] *)

  Definition cardinal : t A -> nat :=
    trie_ind (fun _ => nat) O (fun _ x o _ y _ => x+(match o with Some a => 1|_=> O end)+y).

  (** Specification predicates, as in [FMapInterface] *)

  Definition MapsTo (i:key)(v:A)(m:t A) := find i m = Some v.

  Definition In (i:key)(m:t A) := exists e:A, MapsTo i e m.

  Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').

  Definition eq_key_elt (p p':key*A) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

  (** Specifications in terms of [find] *)

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof. reflexivity. Qed.

  Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
  Proof.
  unfold Empty, MapsTo.
  intuition.
  - generalize (H a).
    destruct (find a m); intuition.
    elim (H0 a0); auto.
  - rewrite H in H0; discriminate.
  Qed.

  Lemma Empty_None : forall m, Empty m <-> m = None.
  Proof.
  intros m. rewrite Empty_alt. split.
  - apply extensionality_empty.
  - intros ->. reflexivity.
  Qed.

  Lemma is_empty_None : forall m, is_empty m = true <-> m = None.
  Proof. destruct m; simpl; intuition discriminate. Qed.

  Theorem gempty: forall (i: key), find i empty = None.
  Proof. reflexivity. Qed.

  Theorem gss: forall (i: key) (x: A) (m: t A), find i (add i x m) = Some x.
  Proof. intros; apply get_set_same. Qed.

  Theorem gso: forall (i j: key) (x: A) (m: t A),
    i <> j -> find i (add j x m) = find i m.
  Proof. intros; apply get_set_diff; auto. Qed.

  Theorem grs: forall (i: key) (m: t A), find i (remove i m) = None.
  Proof. intros; apply get_remove_same. Qed.

  Theorem gro: forall (i j: key) (m: t A),
    i <> j -> find i (remove j m) = find i m.
  Proof. intros; apply get_remove_diff; auto. Qed.

  (** Specification of [elements] *)

  Definition fstmap (f:key->key) '(k, e) : key*A := (f k, e).

  Lemma elements_node r l o :
   elements (Node l o r) =
   (List.map (fstmap xO) (elements l)) ++
   (match o with Some e => (xH,e)::nil | None => nil end) ++
   (List.map (fstmap xI) (elements r)).
  Proof. case l, o, r; reflexivity. Qed.

  Local Abbreviation InL := (InA eq_key_elt).

  Lemma InL_fstmap f k e l :
    InL (k,e) (List.map (fstmap f) l) <-> exists k', k = f k' /\ InL (k',e) l.
  Proof.
    induction l as [|(k0,e0) l IH]; simpl.
    - rewrite InA_nil. split; [intros []|intros (k' & _ & H); inversion H].
    - split.
      + intros H. apply InA_cons in H. destruct H as [(Hk,He)|H]; simpl in *.
        * exists k0. split; [exact Hk|]. left. split; simpl; [reflexivity|exact He].
        * apply IH in H. destruct H as (k' & -> & H). exists k'. split; trivial. now right.
      + intros (k' & -> & H). apply InA_cons in H. destruct H as [(Hk,He)|H]; simpl in *.
        * unfold E.eq in Hk. subst. left. split; reflexivity.
        * right. apply IH. exists k'. auto.
  Qed.

  Lemma InL_opt k e (o : option A) :
    InL (k,e) (match o with Some v => (xH,v)::nil | None => nil end)
    <-> k = xH /\ o = Some e.
  Proof.
    destruct o as [v|]; rewrite ?InA_cons, InA_nil; split.
    - intros [(Hk,He)|[]]. simpl in *. subst. auto.
    - intros (-> & [= ->]). left. split; reflexivity.
    - intros [].
    - intros (_ & [=]).
  Qed.

  Lemma elements_spec m k e :
    InA eq_key_elt (k,e) (elements m) <-> MapsTo k e m.
  Proof.
    unfold MapsTo, find. revert k.
    induction m as [|l IHl o r IHr _] using trie_ind; intros k.
    - split; [inversion 1 | discriminate].
    - rewrite elements_node, !InA_app_iff, !InL_fstmap, InL_opt, get_Node.
      setoid_rewrite IHl. setoid_rewrite IHr.
      destruct k as [k|k|]; split.
      + intros [(k0 & H & _)|[(H & _)|(k0 & H & H')]]; try discriminate.
        injection H as <-. exact H'.
      + intros H. right. right. exists k. auto.
      + intros [(k0 & H & H')|[(H & _)|(k0 & H & _)]]; try discriminate.
        injection H as <-. exact H'.
      + intros H. left. exists k. auto.
      + intros [(k0 & H & _)|[(_ & H)|(k0 & H & _)]]; try discriminate. exact H.
      + intros H. right. left. auto.
  Qed.

  Lemma sort_app (l1 l2 : list (key*A)) :
    sort lt_key l1 -> sort lt_key l2 ->
    (forall x y, List.In x l1 -> List.In y l2 -> lt_key x y) ->
    sort lt_key (l1 ++ l2).
  Proof.
    induction 1 as [|x l1 Hs IH Hinf]; simpl; intros Hs2 Hlt; trivial.
    constructor; [apply IH; trivial; intros; apply Hlt; simpl; auto|].
    destruct Hinf as [|y l1' H]; simpl.
    - destruct l2; constructor. apply Hlt; simpl; auto.
    - constructor; trivial.
  Qed.

  Lemma sort_fstmap f l :
    (forall x y, E.lt x y -> E.lt (f x) (f y)) ->
    sort lt_key l -> sort lt_key (List.map (fstmap f) l).
  Proof.
    intros Hf. induction 1 as [|(k,e) l Hs IH Hinf]; simpl; constructor; trivial.
    destruct Hinf as [|(k',e') l' H]; simpl; constructor.
    unfold lt_key in *; simpl in *; auto.
  Qed.

  Lemma elements_sort m : sort lt_key (elements m).
  Proof.
    induction m as [|l IHl o r IHr _] using trie_ind; [constructor|].
    rewrite elements_node.
    apply sort_app; [apply sort_fstmap; trivial| apply sort_app |].
    - destruct o; repeat constructor.
    - apply sort_fstmap; trivial.
    - intros (x,d) (y,d') Hx Hy.
      destruct o; simpl in Hx; [destruct Hx as [[= <- <-]|[]]|destruct Hx].
      rewrite in_map_iff in Hy. destruct Hy as ((k,e) & [= <- <-] & _).
      red; simpl; exact I.
    - intros (x,d) (y,d') Hx Hy.
      rewrite in_map_iff in Hx. destruct Hx as ((k,e) & [= <- <-] & _).
      rewrite in_app_iff, in_map_iff in Hy.
      destruct Hy as [Hy|((k',e') & [= <- <-] & _)];
        [destruct o; simpl in Hy; [destruct Hy as [[= <- <-]|[]]|destruct Hy]|];
        red; simpl; exact I.
  Qed.

  (** [cardinal] *)

  Lemma cardinal_Node l o r :
    cardinal (Node l o r) =
    (cardinal l + (match o with Some _ => 1 | None => 0 end) + cardinal r)%nat.
  Proof. case l, o, r; reflexivity. Qed.

  Lemma cardinal_elements m : cardinal m = length (elements m).
  Proof.
    induction m as [|l IHl o r IHr _] using trie_ind; trivial.
    rewrite elements_node, cardinal_Node, !length_app, !length_map, IHl, IHr.
    destruct o; simpl; now rewrite ?Nat.add_0_r, ?Nat.add_1_r, ?Nat.add_succ_r.
  Qed.

  (** Specifications in the form of [FMapInterface] *)

  Section FMapSpec.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct (find x m).
  - exists a; auto.
  - intros; discriminate.
  Qed.

  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  rewrite Empty_alt; apply gempty.
  Qed.

  Lemma is_empty_1 : Empty m -> is_empty m = true.
  Proof.
  rewrite Empty_None. intros ->. reflexivity.
  Qed.

  Lemma is_empty_2 : is_empty m = true -> Empty m.
  Proof.
  rewrite Empty_None. destruct m; [discriminate|reflexivity].
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
  unfold MapsTo.
  intro H; rewrite H; clear H.
  apply gss.
  Qed.

  Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
  unfold MapsTo.
  intros; rewrite gso; auto.
  Qed.

  Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  intro H; rewrite gso; auto.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof.
  intros; intro.
  generalize (mem_1 H0).
  rewrite mem_find.
  red in H.
  rewrite H.
  rewrite grs.
  intros; discriminate.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
  unfold MapsTo.
  intro H; rewrite gro; auto.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
  unfold MapsTo.
  destruct (E.eq_dec x y).
  - subst.
    rewrite grs; intros; discriminate.
  - rewrite gro; auto.
  Qed.

  Lemma elements_1 :
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof. apply elements_spec. Qed.

  Lemma elements_2 :
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof. apply elements_spec. Qed.

  Lemma elements_3 : sort lt_key (elements m).
  Proof. apply elements_sort. Qed.

  Lemma elements_3w : NoDupA eq_key (elements m).
  Proof.
    apply ME.Sort_NoDupA.
    apply elements_3.
  Qed.

  Lemma cardinal_1 : cardinal m = length (elements m).
  Proof. apply cardinal_elements. Qed.

  End FMapSpec.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> A -> B.

    Fixpoint xmapi' (m : branch A) (i : positive) {struct m} : t B :=
      branch_map (fun l o r =>
        Node (option_bind (fun l => xmapi' l (xO i)) l)
             (option_map (f (rev i)) o)
             (option_bind (fun r => xmapi' r (xI i)) r)) m.

    Definition xmapi (m : t A) (i : positive) : t B :=
      match m with Some m => xmapi' m i | None => None end.

    Lemma xmapi_Node l o r i :
      xmapi (Node l o r) i =
      Node (xmapi l (xO i)) (option_map (f (rev i)) o) (xmapi r (xI i)).
    Proof. case l, o, r; reflexivity. Qed.

    Definition mapi m := xmapi m xH.

  End Mapi.

  Definition map (f : A -> B) : t A -> t B := map_filter (fun a => Some (f a)).

  End A.

  Lemma xgmapi:
    forall (A B: Type) (f: key -> A -> B) (i j : key) (m: t A),
      find i (xmapi f m j) = option_map (f (j@i)) (find i m).
  Proof.
  unfold find.
  induction i; intros; induction m using trie_ind;
   rewrite ?xmapi_Node, ?get_Node, ?IHi; simpl; auto.
  Qed.

  Theorem gmapi:
    forall (A B: Type) (f: key -> A -> B) (i: key) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof. intros. apply xgmapi. Qed.

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: key) (m: t A),
    find i (map f m) = option_map f (find i m).
  Proof.
  intros. unfold map, find. rewrite get_map_filter. now destruct get.
  Qed.

  Lemma map_as_mapi A B (f:A -> B)(m : t A) : map f m = mapi (fun _ => f) m.
  Proof.
  apply extensionality. intros i.
  change (find i (map f m) = find i (mapi (fun _ => f) m)).
  now rewrite gmap, gmapi.
  Qed.

  Lemma mapi_1 :
    forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
    MapsTo x e m ->
    exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
  intros.
  exists x.
  split; [red; auto|].
  apply find_2.
  generalize (find_1 H); clear H; intros.
  rewrite gmapi.
  rewrite H.
  simpl; auto.
  Qed.

  Lemma mapi_2 :
    forall (elt elt':Type)(m: t elt)(x:key)(f:key->elt->elt'),
    In x (mapi f m) -> In x m.
  Proof.
  intros.
  apply mem_2.
  rewrite mem_find.
  destruct H as (v,H).
  generalize (find_1 H); clear H; intros.
  rewrite gmapi in H.
  destruct (find x m); auto.
  simpl in *; discriminate.
  Qed.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
  intros; rewrite map_as_mapi.
  destruct (mapi_1 (fun _ => f) H); intuition.
  Qed.

  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
    In x (map f m) -> In x m.
  Proof.
  intros; rewrite map_as_mapi in *; eapply mapi_2; eauto.
  Qed.

  (** [map2] *)

  Definition map2 (elt elt' elt'':Type)(f:option elt->option elt'->option elt'') :=
   combine (fun o1 o2 => match o1,o2 with None,None => None | _, _ => f o1 o2 end).

  Lemma gmap2: forall (elt elt' elt'':Type)(f:option elt->option elt'->option elt'')
    (i: key)(m1:t elt)(m2: t elt'),
    find i (map2 f m1 m2) =
    match find i m1, find i m2 with None,None => None | o1, o2 => f o1 o2 end.
  Proof.
  intros. unfold map2, find. rewrite get_combine by reflexivity.
  destruct (get i m1), (get i m2); reflexivity.
  Qed.

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m').
  Proof.
  intros.
  rewrite gmap2.
  generalize (@mem_1 _ m x) (@mem_1 _ m' x).
  do 2 rewrite mem_find.
  destruct (find x m); simpl; auto.
  destruct (find x m'); simpl; auto.
  intros.
  destruct H; intuition; try discriminate.
  Qed.

  Lemma  map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  generalize (mem_1 H); clear H; intros.
  rewrite mem_find in H.
  rewrite gmap2 in H.
  generalize (@mem_2 _ m x) (@mem_2 _ m' x).
  do 2 rewrite mem_find.
  destruct (find x m); simpl in *; auto.
  destruct (find x m'); simpl in *; auto.
  Qed.

  (** [fold] *)

  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Fixpoint xfold' (m : branch A) (v : B) (i : key) {struct m} : B :=
      branch_map (fun l o r =>
        let v := match l with Some l => xfold' l v (xO i) | None => v end in
        let v := match o with Some x => f (rev i) x v | None => v end in
        match r with Some r => xfold' r v (xI i) | None => v end) m.

    Definition xfold (m : t A) (v : B) (i : key) : B :=
      match m with Some m => xfold' m v i | None => v end.

    Definition fold m i := xfold m i xH.

    Lemma xfold_Node l o r v i :
      xfold (Node l o r) v i =
      match o with
      | Some x => xfold r (f (rev i) x (xfold l v (xO i))) (xI i)
      | None => xfold r (xfold l v (xO i)) (xI i)
      end.
    Proof. case l, o, r; reflexivity. Qed.

  End Fold.

  Lemma xfold_elements :
    forall (A B : Type) (f : key -> A -> B -> B) m v j,
    xfold f m v j =
    fold_left (fun a p => f (fst p) (snd p) a) (List.map (fstmap (rev_append j)) (elements m)) v.
  Proof.
    intros A B f.
    induction m as [|l IHl o r IHr _] using trie_ind; intros; trivial.
    rewrite xfold_Node, elements_node, !map_app, !fold_left_app, !map_map.
    destruct o; simpl; rewrite IHr, IHl;
      repeat (f_equal; try (apply map_ext; now intros (?,?))).
  Qed.

  Lemma fold_1 :
    forall (A:Type)(m:t A)(B:Type)(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros. unfold fold. rewrite xfold_elements.
    erewrite map_ext with (g := fun p => p); [now rewrite map_id | now intros (k,e)].
  Qed.

  (** [equal]: thanks to extensionality, two tries are [equal] when the trie
      of their differences is empty. *)

  Definition equal_opt (A:Type)(cmp : A -> A -> bool) o1 o2 : option unit :=
    match o1, o2 with
    | None, None => None
    | Some v1, Some v2 => if cmp v1 v2 then None else Some tt
    | _, _ => Some tt
    end.

  Definition equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    is_empty (combine (equal_opt cmp) m1 m2).

  Definition Equal (A:Type)(m m':t A) :=
    forall y, find y m = find y m'.
  Definition Equiv (A:Type)(eq_elt:A->A->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_spec : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true <-> Equivb cmp m m'.
  Proof.
  intros A m m' cmp. unfold equal, Equivb, Equiv, In, MapsTo, Cmp, find.
  rewrite is_empty_None, <- Empty_None, Empty_alt. unfold find.
  setoid_rewrite get_combine; [|reflexivity].
  split.
  - intros H. split.
    + intros k. specialize (H k). unfold equal_opt in H.
      destruct (get k m), (get k m'); split; try discriminate;
        intros (v,Hv); try discriminate; eauto.
    + intros k e e' He He'. specialize (H k). rewrite He, He' in H.
      simpl in H. now destruct cmp.
  - intros (H1,H2) k. specialize (H1 k). specialize (H2 k).
    unfold equal_opt.
    destruct (get k m) as [v|], (get k m') as [v'|]; trivial.
    + now rewrite (H2 v v').
    + exfalso. destruct H1 as (H1,_). destruct H1 as (?,H1); eauto. discriminate.
    + exfalso. destruct H1 as (_,H1). destruct H1 as (?,H1); eauto. discriminate.
  Qed.

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof. intros; now apply equal_spec. Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof. intros; now apply equal_spec. Qed.

End TrieMap.

(** Here come some additional facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)

Module TrieMapAdditionalFacts.
  Import TrieMap.

  (** The main point of this implementation: [Equal] maps are
      Leibniz-equal. *)

  Lemma Equal_eq {A} (m m' : t A) : Equal m m' <-> m = m'.
  Proof.
  split.
  - apply extensionality.
  - intros <- k. reflexivity.
  Qed.

  Lemma Equiv_eq {A} (m m' : t A) :
    Equiv Logic.eq m m' <-> m = m'.
  Proof.
  rewrite <- Equal_eq. unfold Equiv, In, MapsTo, Equal, find.
  split.
  - intros (H1,H2) k. specialize (H1 k). specialize (H2 k).
    destruct (get k m) as [v|], (get k m') as [v'|]; trivial.
    + f_equal. now apply H2.
    + exfalso. destruct H1 as (H1,_). destruct H1 as (?,H1); eauto. discriminate.
    + exfalso. destruct H1 as (_,H1). destruct H1 as (?,H1); eauto. discriminate.
  - intros H. split.
    + intros k. now rewrite H.
    + intros k e e' He He'. rewrite H in He. congruence.
  Qed.

  (* Derivable from the Map interface *)
  Theorem gsspec {A} i j x (m: t A) :
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    destruct (E.eq_dec i j) as [->|];
    [ apply gss | apply gso; auto ].
  Qed.

  (* Not derivable from the Map interface, but easy from extensionality *)
  Theorem gsident {A} i (m:t A) v :
    find i m = Some v -> add i v m = m.
  Proof.
    intros H. apply extensionality. intros k.
    change (find k (add i v m) = find k m).
    rewrite gsspec. destruct E.eq_dec; congruence.
  Qed.

  Theorem remove_absent {A} i (m:t A) :
    find i m = None -> remove i m = m.
  Proof.
    intros H. apply extensionality. intros k.
    change (find k (remove i m) = find k m).
    destruct (E.eq_dec k i) as [->|].
    - now rewrite grs.
    - apply gro; auto.
  Qed.

  Theorem map2_commut{A B C}
    (f: option A -> option B -> option C)
    (g: option B -> option A -> option C) :
    (forall o1 o2, f o1 o2 = g o2 o1) ->
    forall m1 m2, map2 f m1 m2 = map2 g m2 m1.
  Proof.
    intros E m1 m2. apply extensionality. intros k.
    change (find k (map2 f m1 m2) = find k (map2 g m2 m1)).
    rewrite !gmap2.
    destruct (find k m1), (find k m2); simpl; auto.
  Qed.

End TrieMapAdditionalFacts.
