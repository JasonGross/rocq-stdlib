(* The new interface of Vector and Fin (vec, fin, getFin, Fin.val, ...) next
   to the deprecated one. The constructors nil and cons take their type and
   length arguments explicitly, as Vector.nil and Vector.cons did; the
   notations do not care. *)

From Stdlib Require Import Vector Fin.
Import VectorNotations.

Check cons _ 1 _ (cons _ 2 _ (nil _)) : vec nat 2.
Check [1; 2; 3] : vec nat 3.
Check @cons : forall A, A -> forall n, vec A n -> vec A (S n).
Check Fin.finS Fin.finO : fin 3.

(* The old and the new names denote the same terms. *)
Check eq_refl : Vector.t = vec.
Check eq_refl : @Vector.t_rect = @vec_rect.
Check eq_refl : @Fin.F1 = @Fin.finO.
Check eq_refl : @Fin.FS = @Fin.finS.
Check eq_refl : @Fin.t_rect = @Fin.fin_rect.
Check eq_refl : @Vector.append = @Vector.app.
Check eq_refl : @Vector.const = @Vector.repeat.

(* Old code can use the small inversions on the shared type. *)
Lemma eta A n (v : Vector.t A (S n)) : v = Vector.hd v :: Vector.tl v.
Proof. rewrite (Vector.inj_S v); reflexivity. Qed.

Lemma old_nth_is_new A n (v : Vector.t A n) i : Vector.nth v i = getFin v i.
Proof. rewrite Vector.nth_getFin; reflexivity. Qed.

(* Computation and lemmas of the new interface. *)
Goal rev [1; 2; 3] = [3; 2; 1]. Proof. rewrite 3 rev_cons_snoc; reflexivity. Qed.
Goal to_list (firstn [1; 2; 3] 2) = (1 :: 2 :: Datatypes.nil)%list. Proof. reflexivity. Qed.
Goal to_list (skipn [1; 2; 3] 2) = (3 :: Datatypes.nil)%list. Proof. reflexivity. Qed.
Goal to_list (lastn [1; 2; 3] 2) = (2 :: 3 :: Datatypes.nil)%list.
Proof. cbv [lastn]; rewrite to_list_cast; reflexivity. Qed.
Goal get [1; 2; 3] 1 = Some 2. Proof. reflexivity. Qed.
Goal put [1; 2; 3] 1 7 = [1; 7; 3]. Proof. reflexivity. Qed.
Goal getFin [1; 2; 3] (Fin.finS Fin.finO) = 2. Proof. reflexivity. Qed.
Goal putFin [1; 2; 3] Fin.finO 7 = [7; 2; 3]. Proof. reflexivity. Qed.
Goal Fin.val (Fin.mk 5 2 ltac:(repeat constructor)) = 2.
Proof. apply Fin.val_mk. Qed.
Goal Fin.val (Fin.last 4) = 4. Proof. reflexivity. Qed.
Goal unapp 2 [1; 2; 3] = ([1; 2], [3]). Proof. reflexivity. Qed.
Goal ([1; 2] ++ [3]) = [1; 2; 3]. Proof. reflexivity. Qed.

Lemma rev_rev' A n (v : vec A n) : rev (rev v) = v.
Proof. apply to_list_inj; rewrite 2 to_list_rev, List.rev_involutive; reflexivity. Qed.

Lemma getFin_map A B (f : A -> B) n (v : vec A n) i : getFin (map f v) i = f (getFin v i).
Proof.
  induction v; [case (Fin.inj_0 i)|case (Fin.inj_S i) as [->|[? ->]]]; cbn; auto.
Qed.
