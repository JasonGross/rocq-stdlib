(* The new interface Compat.Vector92 / Compat.Fin92 next to the deprecated
   Vector interface. While VectorDef is loaded, the constructors nil and cons
   take their type and length arguments explicitly (as Vector.nil and
   Vector.cons did); the notations do not care. *)

From Stdlib Require Import Vector.
From Stdlib Require Import Compat.Vector92 Compat.Fin92 VectorFin.
Import Vector92.VectorNotations.

Check cons _ 1 _ (cons _ 2 _ (nil _)) : vec nat 2.
Check [1; 2; 3] : vec nat 3.
Check @cons : forall A, A -> forall n, vec A n -> vec A (S n).
Check finS finO : fin 3.

(* The old and the new names denote the same terms. *)
Check eq_refl : Vector.t = vec.
Check eq_refl : @Vector.cons = @cons.
Check eq_refl : @Vector.nil = @nil.
Check eq_refl : @Fin.F1 = @finO.
Check eq_refl : @Fin.FS = @finS.

(* Old code can use the small inversions on the shared type. *)
Lemma eta A n (v : Vector.t A (S n)) : v = Vector.hd v :: Vector.tl v.
Proof. rewrite (Vector92.inj_S v); reflexivity. Qed.

Lemma old_map_is_new A B (f : A -> B) n (v : Vector.t A n) : Vector.map f v = map f v.
Proof. rewrite Vector.map_92; reflexivity. Qed.

(* Computation and lemmas of the new interface. *)
Goal rev [1; 2; 3] = [3; 2; 1]. Proof. rewrite 3 rev_cons; reflexivity. Qed.
Goal to_list (firstn [1; 2; 3] 2) = (1 :: 2 :: Datatypes.nil)%list. Proof. reflexivity. Qed.
Goal to_list (skipn [1; 2; 3] 2) = (3 :: Datatypes.nil)%list. Proof. reflexivity. Qed.
Goal to_list (lastn [1; 2; 3] 2) = (2 :: 3 :: Datatypes.nil)%list.
Proof. cbv [lastn]; rewrite to_list_cast; reflexivity. Qed.
Goal get [1; 2; 3] 1 = Some 2. Proof. reflexivity. Qed.
Goal put [1; 2; 3] 1 7 = [1; 7; 3]. Proof. reflexivity. Qed.
Goal getFin [1; 2; 3] (finS finO) = 2. Proof. reflexivity. Qed.
Goal putFin [1; 2; 3] finO 7 = [7; 2; 3]. Proof. reflexivity. Qed.
Goal to_nat (of_nat 5 2 ltac:(repeat constructor)) = 2.
Proof. apply to_nat_of_nat. Qed.
Goal unapp 2 [1; 2; 3] = ([1; 2], [3]). Proof. reflexivity. Qed.

Lemma rev_rev' A n (v : vec A n) : rev (rev v) = v.
Proof. apply to_list_inj; rewrite 2 to_list_rev, List.rev_involutive; reflexivity. Qed.

Lemma getFin_map A B (f : A -> B) n (v : vec A n) i : getFin (map f v) i = f (getFin v i).
Proof.
  induction v; [case (Fin92.inj_0 i)|case (Fin92.inj_S i) as [->|[? ->]]]; cbn; auto.
Qed.
