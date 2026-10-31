(* The deprecated Vector and Fin interfaces still work on top of
   Compat.Vector92 and Compat.Fin92: the same type, the historical names, and
   the historical argument structure of the constructors. *)

Set Warnings "-deprecated".
From Stdlib Require Import Vector Fin Bvector List.
Import VectorNotations.

(* Constructors with explicit type and length arguments, as before. *)
Check (Vector.cons nat 1 _ (Vector.nil nat)) : Vector.t nat 1.
Check [1; 2; 3] : Vector.t nat 3.
Check @Vector.cons : forall A, A -> forall n, Vector.t A n -> Vector.t A (S n).
Check @Vector.nil : forall A, Vector.t A 0.
Check Fin.F1 : Fin.t 3.
Check Fin.FS Fin.F1 : Fin.t 3.

(* Pattern matching with the historical constructor names. *)
Definition my_hd {A n} (v : Vector.t A (S n)) : A :=
  match v with
  | Vector.cons _ a _ _ => a
  end.

Definition my_length {A n} (v : Vector.t A n) : nat :=
  match v with
  | Vector.nil _ => 0
  | Vector.cons _ _ n _ => S n
  end.

Definition fin_is_zero {n} (i : Fin.t n) : bool :=
  match i with Fin.F1 => true | Fin.FS _ => false end.

(* Induction with the historical scheme names and tactics. *)
Lemma my_length_ok A n (v : Vector.t A n) : my_length v = n.
Proof. induction v; reflexivity. Qed.

Lemma map_id' A n (v : Vector.t A n) : Vector.map (fun x => x) v = v.
Proof. induction v as [|a n v IH] using Vector.t_ind; cbn; congruence. Qed.

Definition double_by_rect {A n} : Vector.t A n -> Vector.t (A * A) n :=
  Vector.t_rect A (fun n _ => Vector.t (A * A) n) [] (fun a n _ r => (a, a) :: r) n.

Lemma fin_zero_or_succ n (i : Fin.t (S n)) : i = Fin.F1 \/ exists j, i = Fin.FS j.
Proof. apply (Fin.caseS' i); eauto. Qed.

(* The eliminators for empty and non-empty vectors. *)
Lemma v0_nil A (v : Vector.t A 0) : v = [].
Proof. apply (Vector.case0 (fun v => v = [])); reflexivity. Qed.

Lemma vS_eta A n (v : Vector.t A (S n)) : v = Vector.hd v :: Vector.tl v.
Proof. apply (Vector.caseS' v); reflexivity. Qed.

Lemma map2_fst A B n (v : Vector.t A n) (w : Vector.t B n) :
  Vector.map2 (fun a _ => a) v w = v.
Proof.
  apply (Vector.rect2 (fun n v w => Vector.map2 (fun a _ => a) v w = v)); cbn;
    congruence.
Qed.

(* The predicates, with their constructors and induction principles. *)
Lemma In_hd A a n (v : Vector.t A n) : Vector.In a (a :: v).
Proof. apply Vector.In_cons_hd. Qed.

Lemma Forall_hd A (P : A -> Prop) a n (v : Vector.t A n) :
  Vector.Forall P (a :: v) -> P a.
Proof. intros H; inversion H; subst; assumption. Qed.

Lemma Forall_impl' A (P Q : A -> Prop) (HPQ : forall a, P a -> Q a) n (v : Vector.t A n) :
  Vector.Forall P v -> Vector.Forall Q v.
Proof.
  induction 1 using Vector.Forall_ind; constructor; auto.
Qed.

Lemma Forall2_refl A n (v : Vector.t A n) : Vector.Forall2 eq v v.
Proof. induction v; constructor; auto. Qed.

Lemma Exists_cons_hd' A (P : A -> Prop) a n (v : Vector.t A n) : P a -> Vector.Exists P (a :: v).
Proof. apply Vector.Exists_cons_hd. Qed.

(* Operations and notations. *)
Check fun (v : Vector.t nat 3) => v[@Fin.F1].
Goal Vector.nth [1; 2; 3] (Fin.FS Fin.F1) = 2. Proof. reflexivity. Qed.
Goal Vector.to_list [1; 2; 3] = (1 :: 2 :: 3 :: Datatypes.nil)%list. Proof. reflexivity. Qed.
Goal Vector.of_list (1 :: 2 :: Datatypes.nil)%list = [1; 2]. Proof. reflexivity. Qed.
Goal Vector.rev [1; 2; 3] = [3; 2; 1].
Proof. rewrite 3 Vector.rev_cons, Vector.rev_nil; reflexivity. Qed.
Goal ([1; 2] ++ [3]) = [1; 2; 3]. Proof. reflexivity. Qed.
Goal Vector.append [1; 2] [3] = [1; 2; 3]. Proof. reflexivity. Qed.
Goal Vector.const 0 2 = [0; 0]. Proof. reflexivity. Qed.
Goal Vector.shiftin 3 [1; 2] = [1; 2; 3]. Proof. reflexivity. Qed.
Goal Vector.replace [1; 2; 3] Fin.F1 7 = [7; 2; 3]. Proof. reflexivity. Qed.
Goal Vector.fold_left Nat.add 0 [1; 2; 3] = 6. Proof. reflexivity. Qed.
Goal Vector.fold_right Nat.add [1; 2; 3] 0 = 6. Proof. reflexivity. Qed.
Goal proj1_sig (Fin.to_nat (Fin.FS (Fin.FS Fin.F1) : Fin.t 5)) = 2. Proof. reflexivity. Qed.
Goal Fin.of_nat_lt (ltac:(repeat constructor) : 0 < 3) = Fin.F1. Proof. reflexivity. Qed.
Goal Fin.L 2 (Fin.F1 : Fin.t 1) = (Fin.F1 : Fin.t 3). Proof. reflexivity. Qed.
Goal Fin.R 2 (Fin.F1 : Fin.t 1) = Fin.FS (Fin.FS Fin.F1). Proof. reflexivity. Qed.
Goal Vector.eqb nat Nat.eqb [1; 2] [1; 2] = true. Proof. reflexivity. Qed.
Goal Vector.cast [1; 2] (eq_refl 2) = [1; 2]. Proof. reflexivity. Qed.

Goal forall (v : Vector.t nat 2), Vector.nth_order v (ltac:(repeat constructor) : 0 < 2) = Vector.hd v.
Proof. intros; apply Vector.nth_order_hd. Qed.

(* Lemmas stated with the old names. *)
Goal forall A n (v : Vector.t A n), Vector.rev (Vector.rev v) = v.
Proof. intros; apply Vector.rev_rev. Qed.

Goal forall A n (v : Vector.t A n), Vector.length_to_list _ _ v = Vector.length_to_list _ _ v.
Proof. reflexivity. Qed.

Goal forall A n (v : Vector.t A n) p a, Vector.nth (Vector.replace v p a) p = a.
Proof. intros; apply Vector.nth_replace_eq. Qed.

(* Bvector still works. *)
Check Bnil : Bvector 0.
Check Bcons true 0 Bnil : Bvector 1.

(* Extraction still works. *)
From Stdlib Require Extraction.
Recursive Extraction Vector.map Vector.nth.
