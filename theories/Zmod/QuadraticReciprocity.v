From Stdlib Require Import ZArith ZModOffset Zdiv Zdivisibility Lia.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.
From Stdlib Require Import Zmod.ZmodDef Zmod.ZstarDef Zmod.Zmod Zmod.Zstar.

#[local] Lemma andb_implied_r a b : (a = true -> b = true) -> a && b = a.
Proof. case a, b; trivial. intros H. case H; trivial. Qed.

#[local] Open Scope Z_scope.
#[local] Coercion Z.pos : positive >-> Z.
#[local] Coercion N.pos : positive >-> N.
#[local] Coercion Z.of_N : N >-> Z.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

#[local] Lemma Private_odd_prime (p : Z) : Z.prime p -> 3 <= p -> p mod 2 = 1.
Proof.
  case (Z.mod_pos_bound p 2 eq_refl) as [[]%Zle_lt_or_eq ?]; trivial.
  { intros _ _; eapply Z.le_antisymm;
    solve [ eapply Z.lt_pred_le + eapply Zlt_succ_le; trivial ]. }
  intros [? A] B.
  case (A 2). { split. exact eq_refl. eapply Z.le_succ_l; trivial. }
  apply Z.mod_divide. inversion 1. congruence.
Qed.
#[local] Abbreviation odd_prime := Private_odd_prime (only parsing).

Module CRT.
Module Zmod.
Import ZmodDef.Zmod ZmodBase.Zmod.
Lemma elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  Permutation (elements (a * b))
    (map (fun xy : Zmod _ * Zmod _ => Zmod.of_Z (a*b) (Z.combinecong a b (fst xy) (snd xy)))
      (list_prod (elements a) (elements b))).
Proof.
  eapply NoDup_Permutation_bis; try apply NoDup_elements; rewrite ?length_map, ?length_prod, ?length_elements; try lia.
  intros xy G; rewrite in_map_iff; exists (of_Z _ xy, of_Z _ xy); cbn [fst snd].
  split; cycle 1. { apply List.in_prod; apply in_elements; lia. }
  apply to_Z_inj; rewrite !to_Z_of_Z, Z.combinecong_mod_l, Z.combinecong_mod_r.
  symmetry; rewrite <-2mod_to_Z at 1; f_equal.
  apply Z.combinecong_complete_coprime_nonneg_nonneg; trivial; lia.
Qed.
End Zmod.

Module Zstar.
Import ZstarDef.Zstar ZstarBase.Zstar.

Lemma elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  Permutation (elements (a * b))
    (map (fun xy : Zstar _ * Zstar _ => of_Zmod (Zmod.of_Z (a*b) (Z.combinecong a b (fst xy) (snd xy))))
      (list_prod (elements a) (elements b))).
Proof.
  pose proof Zmod.elements_mul_coprime a b H as P.
  eapply (Permutation_filter (fun x : Zmod (a*b) => Z.gcd x (a*b) =? 1)) in P.
  eapply (Permutation_map (@of_Zmod (a*b))) in P.
  rewrite <-Pos2Z.inj_mul in P; rewrite P; clear P.
  symmetry; rewrite <-map_map with (g:=of_Zmod), filter_map_swap; Morphisms.f_equiv.
  erewrite <-map_ext, <-map_map with (f := fun xy : Zstar _ * Zstar _ => (fst xy : Zmod _, snd xy : Zmod _)); [ eapply f_equal | intros; exact eq_refl ].
  cbv [elements].
  do 2 (case Z.eqb_spec; try lia); intros.
  erewrite list_prod_map_map, map_map, list_prod_filter_filter;
  erewrite map_ext_in, map_id, filter_ext; trivial; intros [x y]; cbn [fst snd].
  { case (Z.combinecong_sound_coprime a b x y ltac:(trivial)) as [Hx Hy].
    apply eq_true_iff_eq; rewrite andb_true_iff, !Z.eqb_eq.
    rewrite Zmod.to_Z_of_Z, Pos2Z.inj_mul.
    setoid_rewrite Z.coprime_mul_r_iff.
    rewrite <-(Z.coprime_mod_l_iff _ a), <-(Z.coprime_mod_l_iff _ b).
    rewrite Z.mod_prod_mod_factor_l, Z.mod_prod_mod_factor_r, Hx, Hy.
    rewrite Z.coprime_mod_l_iff, Z.coprime_mod_l_iff. reflexivity. }
  { intros [?[?%Z.eqb_eq ?%Z.eqb_eq]%andb_true_iff]%filter_In.
    rewrite !to_Zmod_of_Zmod; trivial. }
Qed.

Lemma length_elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  length (elements (a*b)) = (length (elements a) * length (elements b))%nat.
Proof. erewrite elements_mul_coprime, ?length_map, ?length_prod; trivial; lia. Qed.

Lemma length_elements_semiprime (p q : positive)
  (Hp : Z.prime p) (Hq : Z.prime q) (H : p <> q) :
  length (elements (p*q)) = Z.to_nat ((p-1)*(q-1)).
Proof.
  rewrite length_elements_mul_coprime, 2length_elements_prime;
    try apply Z.coprime_prime_prime; trivial; nia.
Qed.
End Zstar.
End CRT.

Module Zstar.
Import ZstarDef.Zstar ZstarBase.Zstar.

Lemma square_roots_opp_prime {p : positive} (Hp : Z.prime p) (x y : Zstar p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite <-3 to_Zmod_inj_iff, 2to_Zmod_pow, to_Zmod_opp.
  rewrite (Zmod.square_roots_opp_prime Hp); reflexivity.
Qed.

Lemma square_roots_1_prime (p : positive) (Hp : Z.prime p) (x : Zstar p) :
  pow x 2 = one <-> (x = one \/ x = opp one).
Proof.
  rewrite <-3to_Zmod_inj_iff, to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite (Zmod.square_roots_1_prime Hp); reflexivity.
Qed.

#[local] Notation "∏ xs" := (prod xs) (at level 40).

Local Infix "*" := mul.
Local Infix "/" := div.

(* TODO: move? Local? *)
Definition of_bool m (b : bool) : Zstar m := if b then one else opp one.
Lemma of_bool_negb m b : of_bool m (negb b) = opp (of_bool m b).
Proof. case b; cbn [of_bool negb]; rewrite ?opp_opp; trivial. Qed.
Lemma of_bool_1_iff (m : positive) b : of_bool m b = one <-> b = true \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3_pos m one (opp one) ltac:(lia).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_m1_iff (m : positive) b : of_bool m b = (opp one) <-> b = false \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3_pos m one (opp one) ltac:(lia).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = one <-> b = true.
Proof. rewrite of_bool_1_iff; intuition (congruence || lia). Qed.
Lemma of_bool_m1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = opp one <-> b = false.
Proof. rewrite of_bool_m1_iff; intuition (congruence || lia). Qed.

Lemma abs_of_bool m b : abs (of_bool m b) = one.
Proof. cbv [of_bool]; case b; rewrite ?abs_opp, ?abs_1; trivial. Qed.
Lemma inv_of_bool m b : inv (of_bool m b) = of_bool m b.
Proof. cbv [of_bool]; case b; rewrite ?inv_opp, ?inv_1; trivial. Qed.

Lemma to_Z_true {m : positive} (H : 2 <= m) : Zmod.to_Z (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.to_Z_1, Z.mod_small; lia. Qed.

Lemma to_Z_false {m : positive} : Zmod.to_Z (of_bool m false) = m-1.
Proof.
  case (Pos.eq_dec m 1) as [->|]; trivial.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.to_Z_opp, to_Zmod_1, Zmod.to_Z_1, (Z.mod_diveq (-1));
    rewrite ?(Z.mod_small 1); try lia.
Qed.

Lemma signed_true {m : positive} (H : 3 <= m) : Zmod.signed (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.signed_1; trivial. Qed.

Lemma signed_false {m : positive} (H : 2 <= m) : Zmod.signed (of_bool m false) = -1.
Proof.
  case (Pos.eq_dec m 2) as [->|]; trivial. cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.signed_opp, to_Zmod_1, Zmod.signed_1 by lia.
  rewrite Z.smod_small; trivial. zify; Z.to_euclidean_division_equations; nia.
Qed.

#[local] Lemma euler_criterion_subproof  {p : positive} (Hp : Z.prime p) (a : Zstar p) :
  ∏ elements p =
  of_bool _ (negb (existsb (fun x => eqb (pow x 2) a) (elements p))) * pow a ((p-1)/2).
Proof.
  apply wlog_eq_Zstar_3_pos; try lia; intro Hp'.

  (* Tripartite categorization *)
  rewrite existsb_as_filter, negb_involutive.
  set (roots := filter (fun x : Zstar p => eqb (pow x 2) a) (elements p)).
  set (smalls := filter (fun x : Zstar p => x <? div a x) (elements p)).
  set (larges := filter (fun x : Zstar p => div a x <? x) (elements p)).
  assert (HP : Permutation (elements p) (roots ++ (smalls ++ larges))). {
   erewrite (Permutation_partition (fun x : Zstar _ => pow x 2 =? a)).
   erewrite (Permutation_partition (fun x : Zstar _ => x <? div a x) (snd _)).
   rewrite !partition_as_filter; cbn [fst snd]; rewrite !filter_filter.
   assert (Hiff : forall x, x*x = a :> Z <-> a/x = x :> Z).
   { intros x; rewrite !Zmod.to_Z_inj_iff, !to_Zmod_inj_iff.
     erewrite <-(mul_cancel_l_iff x _ x), mul_div_r_same_r. split; congruence. }
   erewrite (filter_ext (fun _ => _ && _) (fun x : Zstar _ => x <? div a x)); cycle 1.
   { intros x; eapply andb_implied_r; rewrite pow_2_r, negb_true_iff, Z.eqb_neq, Hiff; lia. }
   erewrite (filter_ext (fun _ => _ && _) (fun x => div a x <? x)); cycle 1.
   { intros x; apply eq_true_iff_eq. rewrite pow_2_r, !andb_true_iff, !negb_true_iff, Z.eqb_neq, Hiff; lia. }
   trivial. }

  pose proof @NoDup_elements p. (* TODO @ *)
  assert (NoDup roots) as NDroots by eauto using NoDup_filter.
  assert (NoDup smalls) by eauto using NoDup_filter.
  assert (NoDup larges) by eauto using NoDup_filter.

  (* Pairing inverses *)
  assert (HPP : Permutation larges (map (fun x : Zstar p => div a x) smalls));
    [|rewrite HPP in HP; clear HPP].
  { apply Permutation.NoDup_Permutation; intros; trivial.
    { eapply Injective_map_NoDup; trivial.
      (* TODO: div_inj, inv_inj *)
      intros ? ? E.
      rewrite <-2mul_inv_r in E.
      eapply mul_cancel_l, (f_equal inv) in E.
      rewrite 2 inv_inv in E.
      trivial. }
    cbv [smalls larges].
    rewrite in_map_iff; repeat setoid_rewrite filter_In.
    repeat setoid_rewrite N.ltb_lt.
    assert (Hdiv : forall x y z : Zstar p, div z y = x <-> z = mul x y); [|setoid_rewrite Hdiv].
    { split; intros; subst.
      { rewrite <-mul_inv_r, <-!mul_assoc, mul_inv_same_l, mul_1_r; auto. }
      { rewrite div_mul_l, div_same, mul_1_r; trivial. } }
    split.
    { intros []. exists (div a x). rewrite mul_div_r_same_r, div_div_r_same. intuition apply in_elements. }
    { intros (y&A&?&?). rewrite A in *. rewrite mul_comm.
      rewrite div_mul_l, div_same, mul_1_r in *. intuition apply in_elements. } }
  erewrite prod_Permutation, prod_app by eapply HP.
  erewrite (prod_Permutation (smalls++_) (flat_map (fun x => [x;a/x]) smalls)); cycle 1.
  { generalize (div a) as f; generalize smalls as xs; generalize (Zstar p) as A; clear.
    induction xs; cbn [map flat_map app]; intros; econstructor.
    erewrite <-Permutation_middle; eauto. }
  erewrite prod_flat_map, map_ext, map_const, (prod_repeat a); cycle 1.
  { intros x. cbn [prod fold_right]. rewrite mul_1_r, mul_div_r_same_r; trivial. }

  (* Counting elements *)
  assert (length (elements p) = length roots + 2*length smalls)%nat as HL.
  { erewrite Permutation.Permutation_length, !length_app, !length_map by eauto; lia. }
  assert (Z.of_nat (length smalls) = (p-1-Z.of_nat (length roots))/2)%Z as ->.
  { pose proof length_elements_prime p Hp.
    zify; Z.to_euclidean_division_equations; lia. }

  (* Casework on [length roots] using [NoDup roots] *)
  destruct roots as [|x roots'] eqn:A. (* no roots *)
  { cbn [prod fold_right length Nat.eqb of_bool]; rewrite ?mul_1_l, Z.sub_0_r; trivial. }
  assert (Hx: In x roots). { rewrite A. left. split. } apply filter_In, proj2 in Hx.
  destruct roots' as [|y roots''] eqn:B. (* 1 *)
  { unshelve ecase (opp_distinct_odd _ _ x); try lia; auto using odd_prime.
    assert (In (opp x) roots) as AA.
    { apply filter_In, conj; try apply in_elements. rewrite pow_opp_2; trivial. }
    rewrite A in AA; inversion AA as [|AAA]; trivial; inversion AAA. }
  (* 2 <= *)
  assert (Hy: In y roots). { rewrite A. right. left. split. } apply filter_In, proj2 in Hy.
  rewrite eqb_eq in *.
  assert (y = opp x) as ->.
  { case (proj1 (square_roots_opp_prime Hp y x)); trivial.
    { congruence. }
    { intros ->. inversion_clear NDroots as [|? ? X]; case X; left; trivial. } }
  destruct roots'' as [|z roots''']; cycle 1. (* 3 <= *)
  { assert (Hz: In z roots). { rewrite A. right. right. left. split. } apply filter_In, proj2 in Hz.
    rewrite ?eqb_eq in *.
    { case (proj1 (square_roots_opp_prime Hp z x)) as [->| ->].
      { congruence. }
      { inversion_clear NDroots as [|? ? X]; case X; right; left; split. }
      { inversion_clear NDroots as [|? ? ? X].
        inversion_clear X as [|? ? Y]; case Y; left; split. } } }
  (* 2 roots *)
  cbn [prod fold_right length Nat.eqb of_bool];
  repeat rewrite ?mul_1_r, ?mul_1_l, ?mul_opp_l, ?mul_opp_r.
  rewrite <-pow_2_r, Hx, <-pow_succ_r. f_equal. f_equal.
  zify; Z.to_euclidean_division_equations; lia.
Qed.

(** One direction of Wilson's theorem *)
Theorem prod_elements_prime {p : positive} (Hp : Z.prime p) : ∏ elements p = opp one.
Proof.
  rewrite (euler_criterion_subproof Hp one).
  rewrite (proj2 (existsb_exists _ _)), pow_1_l, mul_1_r; cbn [of_bool negb]; trivial.
  exists one; rewrite ?pow_1_l, ?eqb_eq ; auto using in_elements.
Qed.

Lemma euler_criterion_existsb {p : positive} a (Hp : Z.prime p) :
  pow a ((p-1)/2) = of_bool p (existsb (fun x => eqb (pow x 2) a) (elements p)).
Proof.
  pose proof euler_criterion_subproof Hp a as H.
  rewrite prod_elements_prime in H by trivial.
  apply (f_equal opp) in H; rewrite ?of_bool_negb, ?mul_opp_l, ?opp_opp in H.
  case existsb in *; cbn [of_bool] in *;
    rewrite H, ?mul_opp_l, ?opp_opp, ?mul_1_l; trivial.
Qed.

Theorem euler_criterion {p : positive} (a : Zstar p) (Hp : Z.prime p):
  pow a ((p-1)/2) = one <-> exists x, pow x 2 = a.
Proof.
  split.
  { case (Pos.leb_spec 3 p) as []; cycle 1.
    { exists one. apply wlog_eq_Zstar_3_pos; lia. }
    rewrite euler_criterion_existsb, of_bool_1_iff, existsb_exists by trivial.
    intros [[x [_ Hx%eqb_eq]]|]; try lia; eauto. }
  { intros [x Hx]; eapply euler_criterion_square; eauto. }
Qed.

Lemma euler_criterion_nonsquare {p : positive} (Hp : Z.prime p)
  (a : Zstar p) (Ha : forall x, pow x 2 <> a) : pow a ((p-1)/2) = opp one.
Proof.
  rewrite euler_criterion_existsb by trivial.
  case existsb eqn:H; trivial; exfalso.
  apply existsb_exists in H; case H as [x [_ H%eqb_eq]].
  case (Ha x); trivial.
Qed.

Lemma euler_criterion_neq_one {p : positive} (Hp : Z.prime p)
  (a : Zstar p) (H : pow a ((p-1)/2) <> one) : forall x, pow x 2 <> a.
Proof.
  rewrite euler_criterion in H by trivial; intros x Hx; case H; eauto.
Qed.

Lemma euler_criterion_m1 {p : positive} (Hp : Z.prime p) (Hp' : 3 <= p)
  (a : Zstar p) (H : pow a ((p-1)/2) = opp one) : forall x, pow x 2 <> a.
Proof.
  apply euler_criterion_neq_one; trivial; rewrite H; apply opp_1_neq_1; trivial.
Qed.
End Zstar.

Module Zmod.
Import ZstarBase ZmodDef.Zmod ZmodBase.Zmod Zmod.
Local Infix "*" := mul.
Local Infix "^" := pow.

Theorem euler_criterion_square_nz {p : positive} (Hp : Z.prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) (Hnz : a <> zero) :
  pow a ((p-1)/2) = one.
Proof.
  assert (sqrt_a <> zero). { intros ->; rewrite pow_0_l in *; congruence. }
  rewrite <-to_Z_0_iff in *; pose proof to_Z_range a; pose proof to_Z_range sqrt_a.
  assert (Z.coprime a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  assert (Z.coprime sqrt_a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  unshelve epose proof
    (E := Zstar.euler_criterion_square Hp (Zstar.of_Zmod a) (Zstar.of_Zmod sqrt_a) _).
  { apply Zstar.to_Zmod_inj; rewrite Zstar.to_Zmod_pow, 2Zstar.to_Zmod_of_Zmod; trivial. }
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E; trivial.
Qed.

Theorem euler_criterion_square {p : positive} (Hp : Z.prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) :
  a = zero \/ pow a ((p-1)/2) = one.
Proof.
  pose proof euler_criterion_square_nz Hp _ _ Ha.
  case (eqb_spec a zero); intuition idtac.
Qed.

Theorem euler_criterion {p : positive} a (Hp : Z.prime p) :
  (a = zero \/ a ^ ((p - 1) / 2) = one) <-> exists x : Zmod p, pow x 2 = a.
Proof.
  split; cycle 1.
  { intros []; eauto using euler_criterion_square. }
  intros [].
  { subst. exists zero. trivial. }
  pose proof (Z.prime_ge_2 _ Hp) as Hp'; pose proof one_neq_zero (m:=p) ltac:(lia).
  case (Pos.eq_dec p 2) as [->|]. {
    pose proof in_elements a ltac:(lia) as C; case C as [<-| [<-| [] ] ];
      [exists zero|exists one]; trivial. }
  assert (((p - 1) / 2) <> 0)%Z by (zify; Z.div_mod_to_equations; nia).
  assert (a <> zero). { intros ->; rewrite pow_0_l in *. congruence. lia. }
  rewrite <-to_Z_0_iff in H2; pose proof to_Z_range a.
  assert (Z.coprime a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  case (proj1 (@Zstar.euler_criterion p (Zstar.of_Zmod a) Hp)) as [x Hx].
  { apply Zstar.to_Zmod_inj.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1; trivial. }
  { exists x. apply (f_equal Zstar.to_Zmod) in Hx.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod in Hx; trivial. }
Qed.

End Zmod.

Module Reciprocity. Module Zstar.
Import ZmodDef.
Import ZmodDef.Zmod ZmodBase.Zmod CRT.Zmod QuadraticReciprocity.Zmod.
Import ZstarDef.Zstar ZstarBase.Zstar CRT.Zstar QuadraticReciprocity.Zstar.
#[local] Notation "∏ xs" := (prod xs) (at level 40).

Module Z.
Lemma pow_m1_l : forall n, 0 <= n -> Z.pow (-1) n = if Z.odd n then -1 else 1.
Proof.
  eapply Wf_Z.natlike_ind; trivial; intros.
  rewrite Z.pow_succ_r, Z.odd_succ, <-Z.negb_odd by trivial.
  case Z.odd in *; cbv [negb]; lia.
Qed.
End Z.

#[local] Lemma mul_signed_subgroups_abs (p q : positive) (Hp : p mod 2 = 1) (Hq : q mod 2 = 1) x y :
  abs x = abs y :> Zstar (p*q) -> Z.smodulo x p * Z.smodulo x q = Z.smodulo y p * Z.smodulo y q.
Proof.
  intros []%eq_abs_iff; [congruence|subst y].
  rewrite to_Zmod_opp, to_Z_opp.
  symmetry.
  rewrite <-Z.smod_mod, Z.mod_mod_divide, Z.smod_mod by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), Z.mod_mod_divide, Z.smod_mod by (exists p; lia).
  rewrite <-(Z.smod_idemp_opp _ p), <-(Z.smod_idemp_opp _ q).
  pose proof Z.smod_pos_bound x p ltac:(lia).
  pose proof Z.smod_pos_bound x q ltac:(lia).
  rewrite !(Z.smod_small (- _)); (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma square_prod_positives {p : positive} (prime_p : Z.prime p) (odd_p : 3 <= p) :
  pow (∏ positives p) 2 = opp (pow (opp one) ((p - 1) / 2)).
Proof.
  rewrite pow_2_r.
  pose proof prod_elements_prime prime_p as H.
  rewrite elements_by_sign in H by lia.
  rewrite negatives_as_positives_odd in H by auto using odd_prime.
  apply (f_equal opp) in H; rewrite ?opp_opp in H.
  rewrite prod_app, prod_opp, prod_rev, (mul_comm (pow _ _)), mul_assoc, <-mul_opp_r in H.
  rewrite length_rev, length_positives_prime in H by trivial.
  replace (Z.of_nat (N.to_nat (Pos.pred_N p / 2))) with ((p - 1) / 2) in H by lia.
  apply (f_equal (fun x => mul x (inv (opp (pow (opp one) ((p - 1) / 2)))))) in H.
  rewrite Z2Nat.id in H by (Z.div_mod_to_equations; lia).
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r in H.
  rewrite mul_1_l, inv_opp, inv_pow_m1 in H; exact H.
Qed.

#[local] Lemma prod_snd_abspairs
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  ∏ map snd (list_prod (elements p) (positives q)) =
  (-1)^((p-1)/2) * (-1)^((q-1)/2*((p-1)/2)) mod q :> Z.
Proof.
  rewrite List.snd_list_prod, prod_concat, map_repeat, prod_repeat.
  rewrite length_elements_prime, Z2Nat.id by (trivial || Z.div_mod_to_equations; lia).
  replace (p-1) with (2 * ((p-1)/2)) at 1; cycle 1.
  { pose proof odd_prime _ prime_p odd_p. (zify; Z.to_euclidean_division_equations; nia). }
  rewrite pow_mul_r, square_prod_positives, <-mul_m1_l, pow_mul_l, <-pow_mul_r by trivial.
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite ?to_Z_mul, ?to_Z_pow_nonneg_r, ?to_Z_opp, ?to_Z_1, ?Z.mod_pow_l, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?(Z.mod_small 1);
    trivial; try (Z.to_euclidean_division_equations; nia).
Qed.

#[local] Lemma prod_fst_abspairs
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  ∏ map fst (list_prod (elements p) (positives q)) = (-1)^((q-1)/2) mod p :> Z.
Proof.
  erewrite List.fst_list_prod, prod_flat_map, map_ext, prod_pow, prod_elements_prime; trivial.
  2: { intros. instantiate (1:=((q-1)/2)).
    rewrite prod_repeat, length_positives_prime; trivial; f_equal.
    zify; Z.to_euclidean_division_equations; nia. }
  rewrite to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite to_Z_pow_nonneg_r, to_Z_opp, to_Z_1, Z.mod_pow_l, ?(Z.mod_small 1); trivial;
    Z.to_euclidean_division_equations; nia.
Qed.

#[local] Abbreviation combine p q :=
  (fun xy : Zstar _ * Zstar _ => Zstar.of_Zmod (Zmod.of_Z (p*q)%positive (Z.combinecong p%positive q%positive (fst xy) (snd xy)))).

Lemma prod_combinecong
  {p q : positive} {Hp : 3 <= p} {Hq : 3 <= q} {coprime_p_q : Z.coprime p q} (ps : list (Zstar p * Zstar q)) :
  ∏ (map (combine p q)) ps =
  Zstar.of_Zmod (Zmod.of_Z (p*q) (Z.combinecong p q (∏ map fst ps) (∏ map snd ps))).
Proof.
  induction ps as [|[x y]]; cbn [fst snd map]; rewrite ?prod_nil, ?prod_cons; [|rewrite IHps; clear IHps].
  { erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg with (a:=1);
    repeat (rewrite ?Z.mod_small, ?to_Zmod_1, ?to_Z_1;
      trivial; try (Z.to_euclidean_division_equations; nia)). }
  rewrite ?to_Zmod_mul, ?to_Z_mul.
  symmetry; erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg with
    (a:=(Z.combinecong p q x y) * (Z.combinecong p q (∏ map fst ps) (∏ map snd ps)))
    by (trivial; try lia; rewrite <-Zmult_mod_idemp_r, <-Zmult_mod_idemp_l,
      ?(proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?Zmult_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmod_mod; trivial).
  rewrite of_Z_mod, of_Z_mul, of_Zmod_mul; trivial;
  rewrite to_Z_of_Z, Z.coprime_mod_l_iff, ?Pos2Z.inj_mul; apply Z.coprime_mul_r;
  rewrite <-Z.coprime_mod_l_iff,
      ?(proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), ?Z.coprime_mod_l_iff;
  auto using to_Zmod_range.
Qed.

Lemma abs_prod_abs m xs : @abs m (∏ map abs xs) = abs (∏ xs).
Proof.
  induction xs; cbn [map]; rewrite ?prod_nil, ?prod_cons; trivial.
  rewrite <-abs_mul_abs_r, IHxs, abs_mul_abs_abs; trivial.
Qed.

Lemma abs_prod_positives_semiprime
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  abs (∏ positives (p*q)) = abs (∏ map (combine p q) (list_prod (elements p) (positives q))).
Proof.
  intros.
  pose (absq (x : Zstar (p*q)) := if 0 <? Z.smodulo x q then x else opp x).
  assert (abs_absq : forall x, abs (absq x) = abs x). {
    intros. cbv [absq]. destruct Z.ltb; auto using abs_opp. }
  erewrite <-abs_prod_abs, map_ext, <-map_map, abs_prod_abs by (symmetry; apply abs_absq).
  f_equal.
  eapply prod_Permutation .
  eapply Permutation.NoDup_Permutation_bis; cbv [incl].
  { eapply NoDup_map_inv with (f:=abs).
    erewrite map_map, map_ext by (eapply abs_absq).
    pose proof @NoDup_positives (p*q).
    assert (map abs (positives (p * q)) = positives (p*q)).
    { erewrite map_ext_in, map_id; try intros x ?%in_positives; auto using abs_pos. lia. }
    rewrite <-H0 in H; exact H. }
  { rewrite ?length_map, ?length_prod, ?length_elements_prime by trivial.
    pose proof odd_prime p prime_p odd_p as Hp'.
    pose proof odd_prime q prime_q odd_q as Hq'.
    assert (p <> q) by (cbv [Z.coprime] in *; intro; subst; rewrite Z.gcd_diag in *; lia).
    rewrite length_positives_prime, length_positives_odd, length_elements_semiprime by
      (trivial; Z.to_euclidean_division_equations; lia).
    zify. rewrite Nat2Z.inj_div in *. zify. Z.to_euclidean_division_equations. nia. }
  setoid_rewrite in_map_iff.
  intros ? (?&[]&?).
  exists (of_Zmod (of_Z p (absq x)), of_Zmod (of_Z q (absq x))); cbn [fst snd].
  rewrite in_prod_iff, in_positives; [|lia].
  pose proof coprime_to_Zmod x as C; apply Z.coprime_mul_r_iff in C; case C as [].
  pose proof coprime_to_Zmod (absq x) as C;apply Z.coprime_mul_r_iff in C; case C as [].
  repeat rewrite ?to_Zmod_of_Zmod, ?to_Z_of_Z, ?signed_of_Z,
    ?Z.combinecong_mod_l, ?Z.combinecong_mod_r, ?Z.coprime_mod_l_iff; trivial; [].
  (intuition auto using in_elements); [|]; cycle 1. 
  { cbv [absq]; case (Z.ltb_spec 0 (Z.smodulo x q)) as []; trivial. 
    rewrite to_Zmod_opp, to_Z_opp, <-Z.smod_mod, Z.mod_mod_divide, Z.smod_mod, <-Z.smod_idemp_opp by
      (exists p; lia).
    pose proof Z.smod_pos_bound x q ltac:(lia).
    case (Z.eqb_spec (Z.smodulo x q) 0) as [E|].
    { apply (f_equal (fun x => x mod q)) in E; rewrite Z.mod_smod, Zmod_0_l in E.
      rewrite <-Z.coprime_mod_l_iff, E, Z.coprime_0_l_iff in *. lia. }
    rewrite Z.smod_small; try lia.
    pose proof odd_prime q prime_q odd_q as Hq'; Z.to_euclidean_division_equations; nia. }
  erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg by (trivial; lia).
  rewrite of_Z_mod, of_Z_to_Z, of_Zmod_to_Zmod; trivial.
Qed.

Lemma add_seq a b c : map (Nat.add a) (seq b c) = seq (a+b) c.
Proof.
  revert b; induction c; intros;
    cbn [seq map]; rewrite ?IHc, ?Nat.add_succ_r; trivial.
Qed.

Lemma add_seq_0_l a b : map (Nat.add a) (seq 0 b) = seq a b.
Proof. rewrite add_seq, Nat.add_0_r; trivial. Qed.

#[local] Open Scope nat_scope.
Lemma filter_0mod_seq_0_mul : (forall m, m <> 0 -> forall n,
  filter (fun i => i mod m =? 0) (seq 0 (n * m)) = map (Nat.mul m) (seq 0 n))%nat.
Proof.
  intros until n; induction n; intros; trivial; [].
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, Nat.add_0_l.
  case m as [|pred_m] eqn:pred_m_eq at 2; [contradiction|]; cbn [seq filter].
  rewrite Nat.Div0.mod_0_l, Nat.eqb_refl.
  erewrite filter_ext_in, filter_false; cycle 1.
  { intros ??%in_seq; apply Nat.eqb_neq; intros [[]X]%Nat.Div0.mod_divides; nia. }
  cbn [map "++"]; rewrite Nat.mul_0_r; f_equal.
  erewrite <-add_seq_0_l, filter_map_swap, filter_ext, IHn; cycle 1.
  { intros. rewrite <-Nat.Div0.add_mod_idemp_l, Nat.Div0.mod_same, Nat.add_0_l; trivial. }
  symmetry. rewrite <-add_seq_0_l, 2map_map; apply map_ext; lia.
Qed.

Lemma filter_cong_seq_mul_mul k m (Hm : m <> 0) : forall n s,
  filter (fun i => i mod m =? k mod m) (seq (s*m) (n*m)) = map (fun i => i*m + k mod m) (seq s n).
Proof.
  induction n; trivial; intros.
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, <-Nat.mul_succ_l, IHn.
  enough (filter _ _ = [_]) as -> by exact eq_refl.
  pose proof Nat.mod_bound_pos k m ltac:(lia) ltac:(lia).
  replace m with ((k mod m) + (1 + (m-(k mod m+1)))) at 2 by lia.
  rewrite ?seq_app, ?filter_app.
  erewrite filter_ext_in, filter_false, filter_ext_in, filter_true, filter_ext_in, filter_false;
    trivial; intros i ?%in_seq; try apply Nat.eqb_eq; try apply Nat.eqb_neq; assert (s = i / m);
      zify; rewrite ?Nat2Z.inj_div, ?Nat2Z.inj_mod in *; Z.to_euclidean_division_equations; nia.
Qed.

Lemma filter_cong_seq k m (Hm : m <> 0) n s :
  filter (fun i => i mod m =? k mod m) (seq s n) =
  filter (fun i : nat => i mod m =? k mod m) (seq s (n mod m)) ++
  map (Nat.add (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) mod m))
      (map (Nat.mul m) (seq (s / m) (n / m))).
Proof.
  match goal with |- _ = ?R => set R end.
  pose proof Nat.mod_bound_pos s m ltac:(lia) ltac:(lia).
  pose proof Nat.mod_bound_pos n m ltac:(lia) ltac:(lia).
  rewrite (Nat.div_mod n m), Nat.add_comm, seq_app, (Nat.mul_comm m) by lia.
  rewrite (Nat.div_mod s m) at 2 by lia.
  rewrite <-Nat.add_assoc, Nat.add_comm, <-add_seq by lia.
  rewrite filter_app, filter_map_swap.

  unshelve erewrite (Nat.mul_comm m), (filter_ext _ _ _ (seq (_*m) _)), (filter_cong_seq_mul_mul (k mod m+m-s mod m + m - n mod m)) by lia; shelve_unifiable.
  { intros i; apply eq_true_iff_eq; rewrite 2Nat.eqb_eq; split; intros R.
    { rewrite <-R; clear R.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=-2%Z) by lia.
      replace ((s mod m + n mod m + i) mod m + m - s mod m + m - n mod m + - (2) * m)%Z
         with ((s mod m + n mod m + i) mod m - (s mod m + n mod m))%Z by lia.
      rewrite Zminus_mod_idemp_l. f_equal. lia. }
    { rewrite <-Nat.Div0.add_mod_idemp_r, R by lia; clear R; rewrite !Nat.Div0.add_mod_idemp_r, ?Zmod_mod.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.add _ _) (b:=-2%Z) by lia.
      replace (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) + - (2) * m)%Z
         with (k mod m)%Z by lia.
      apply Z.mod_mod; lia.  } }

  erewrite map_map, map_ext, <-map_map with
    (f:=Nat.mul m)
    (g:=Nat.add(s mod m + n mod m + ((k mod m + m - s mod m + m - n mod m) mod m))).
  2:{ intros i; cbv beta. lia. }

  epose proof fun x => filter_In (fun i : nat => i mod m =? k mod m) x (seq s (n mod m)).
  setoid_rewrite in_seq in H1.

  exact eq_refl.
Qed.
Local Close Scope nat_scope.

#[local] Lemma coprime_prime_r a p (H : Z.prime p) : Z.coprime a p <-> a mod p <> 0.
Proof.
  rewrite Z.coprime_comm. etransitivity. { apply Z.coprime_prime_l_iff; trivial. }
  pose proof Z.not_prime_0.
  rewrite Z.mod_divide; intuition subst; contradiction.
Qed. 

#[local] Lemma mul_eq_1_iff a b : a*b = 1 <-> a = 1 /\ b = 1 \/ a = -1 /\ b = -1.
Proof. pose proof Z.eq_mul_1 a b; nia. Qed.
#[local] Lemma filter_filter {A} f g l :
    @filter A f (filter g l) = filter (fun a => f a && g a) l.
Proof. induction l; cbn; auto. case g; cbn; case f; cbn; rewrite ?IHl; auto. Qed.
Lemma seq_mul_r s n c : seq s (n*c) = flat_map (fun i => seq (s + i*c) c) (seq O n).
Proof.
  revert s; induction n; intros; rewrite ?flat_map_nil_l, ?Nat.add_0_r; trivial.
  cbn [Nat.mul]; rewrite Nat.add_comm, seq_app.
  rewrite seq_S, flat_map_app, IHn; cbn [flat_map]; rewrite app_nil_r; trivial.
Qed.
Lemma seq_0_mur n c : seq O (n*c) = flat_map (fun i => seq (i*c) c) (seq O n).
Proof. apply seq_mul_r. Qed.
Lemma prod_map_filter {A} {m} (f : A -> Zstar m) g (xs : list A) :
  ∏ map f (filter g xs) = div (∏ map f xs) (∏ map f (filter (fun x => negb (g x)) xs)).
Proof.
  induction xs; cbn [map filter]; rewrite ?prod_nil, ?prod_cons, ?div_same; trivial.
  case g; cbn [negb map]; rewrite ?prod_cons, !IHxs, ?div_mul_l; trivial.
  rewrite <-!mul_inv_r, ?inv_mul, ?mul_assoc, ?(mul_comm (f a)), ?mul_assoc; f_equal.
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r; trivial.
Qed.
#[local] Lemma to_Zmod_prod {m} xs : @to_Zmod m (∏ xs) = fold_right Zmod.mul Zmod.one (map to_Zmod xs).
Proof. induction xs; cbn [map fold_right]; rewrite ?prod_nil, ?prod_cons, ?to_Zmod_1, ?to_Zmod_mul, ?IHxs; auto. Qed.
#[local] Lemma of_Zmod_prod {m} xs (Hm : 0 < m) : Forall (fun x : Zmod m => Z.coprime x m) xs -> @of_Zmod m (fold_right Zmod.mul Zmod.one xs) = ∏ (map of_Zmod xs).
Proof.
  intros H. apply wlog_eq_Zstar_3_pos; trivial; intro Hm'.
  induction H; cbn [fold_right map]; rewrite ?prod_nil, ?prod_cons, ?of_Zmod_1, ?of_Zmod_mul, ?IHForall; auto.
  clear H IHForall x; induction H0; cbn [fold_right];
    rewrite ?to_Z_1, ?to_Z_mul, ?Z.coprime_mod_l_iff, ?Z.coprime_mul_l_iff;
    auto using Z.coprime_1_l.
Qed.
Lemma prod_positives_semiprime
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  Z.smodulo (∏ positives (p*q)) p =  (-1)^((q-1)/2) * Z.smodulo (q^((p-1)/2)) p.
Proof.
  assert (tl_seq : forall start len, tl (seq start len) = seq (S start) (len-1)).
  { destruct len; rewrite ?Nat.sub_1_r; trivial. }
  assert (
    map_add_seq: forall len start shift : nat, map (Nat.add shift) (seq start len) = seq (shift + start) len
    ).
  { clear; induction len; cbn [seq map]; intros; rewrite ?IHlen, ?Nat.add_succ_r; trivial. }
  assert (
    seq_as_0_l : forall len start shift : nat, seq start len = map (Nat.add start) (seq O len)
    ).
  { clear -map_add_seq; intros. rewrite map_add_seq, Nat.add_0_r; trivial. }
  assert (
div_mul_same_r:
  forall {m : positive} (x y z : Zstar m), div (mul y x) (mul z x) = div y z
  ).
  { clear; intros.
    repeat rewrite <-?mul_inv_r, ?inv_mul, ?(mul_comm x), <-?mul_assoc.
    rewrite mul_inv_same_l, mul_1_r; trivial. }

  assert (div_abs1_r : forall m (x y : Zstar m), abs y = one -> div x y = mul x y).
  { clear; intros m x y H.
    rewrite <-abs_1 in H; eapply eq_sym, eq_abs_iff in H; case H as [->| ->];
        rewrite <-?mul_inv_r, ?inv_opp, ?inv_1; trivial. }

  pose proof odd_prime p prime_p odd_p as Hp'.
  pose proof odd_prime q prime_q odd_q as Hq'.
  rewrite Z.coprime_comm in coprime_p_q.

  assert ((p / 2) < p) by (Z.div_mod_to_equations; nia).

  rewrite <-(Z.smod_smod_divide _ (Pos.mul p q)), smod_unsigned by (exists q; lia).

  (* injecting product into [Zmod p] *)
  rewrite <-signed_of_Z, <-(to_Zmod_of_Zmod (of_Z _ _)); cycle 1.
  { rewrite to_Z_of_Z, <-smod_unsigned, <-Z.mod_smod, Z.smod_smod_divide, Z.mod_smod, Z.coprime_mod_l_iff
      by (exists q; lia).
    pose proof coprime_to_Zmod (∏ positives (p * q)) as Hc;
      apply Z.coprime_mul_r_iff in Hc; case Hc as []; trivial. }

  cbv [positives].
  erewrite to_Zmod_prod, map_map, map_ext_in, map_id; cbv beta.
  2: { intros ? [_ E]%filter_In. apply Z.eqb_eq in E.
    rewrite to_Zmod_of_Zmod by assumption; exact eq_refl. }

  rewrite <-(@of_Z_mod p), <-(Z.mod_smod _ p).
  rewrite <-(@smod_unsigned (p*q)), Z.smod_smod_divide, Z.mod_smod by (exists q; lia).
  rewrite <-Zmod.mod_to_Z.
  assert (forall xs, fold_right Zmod.mul Zmod.one xs mod (p*q)%positive = fold_right Z.mul 1 (map to_Z xs) mod (p*q)%positive) as ->.
  { clear -odd_p odd_q. induction xs; cbn [fold_right map]; rewrite ?to_Z_1, ?to_Z_mul, ?Zmod_mod by lia; trivial.
    rewrite <-Z.mul_mod_idemp_r by lia.
    set ((unsigned (fold_right _ _ _) mod _)) in *.
    rewrite IHxs.
    rewrite Z.mul_mod_idemp_r by lia; trivial. }
  rewrite Z.mod_mod_divide, of_Z_mod by (exists q; lia).
  eassert (forall xs, of_Z _ (fold_right Z.mul 1 xs) = fold_right Zmod.mul Zmod.one (map (of_Z _) xs)) as ->.
  { clear. induction xs; cbn [fold_right map]; rewrite ?of_Z_mul, ?IHxs; trivial. }

  rewrite !map_map.
  rewrite of_Zmod_prod, ?map_map; try lia; cycle 1.
  { eapply Forall_map, Forall_forall; intros ? [? E%Z.eqb_eq]%filter_In.
    apply Z.coprime_mul_r_iff in E; case E as [].
    rewrite to_Z_of_Z, Z.coprime_mod_l_iff by (exists q; lia); trivial. }

  (* inclusion-exclusion principle for [Zmod (p * q)] *)
  erewrite filter_ext, <-filter_filter; cbv beta; cycle 1.
  { instantiate (1:=fun x => Z.gcd x p =? 1). instantiate (1:=fun x => Z.gcd x q =? 1).
    intros x. apply eq_true_iff_eq.
    rewrite andb_true_iff, !Z.eqb_eq, and_comm; apply Z.coprime_mul_r_iff. }

  cbv [Zmod.positives].
  rewrite 2 filter_map_swap, ?map_map.
  rewrite prod_map_filter, filter_filter.
  erewrite (filter_ext_in (fun k => andb _ _) (fun k => (Z.of_nat k mod q) =? 0)); cycle 1.
  { intros ? G; apply in_seq in G.
    rewrite (proj2 (Z.ltb_lt _ _)) in G by lia; cbn [Z.b2z] in G.
    eapply eq_true_iff_eq. rewrite andb_true_iff, <-eq_true_not_negb_iff, 3Z.eqb_eq.
    rewrite !to_Z_of_Z, <-!(Z.gcd_mod_l (Z.of_nat a mod (p * q))),
      !Z.mod_mod_divide, !Z.gcd_mod_l by ((exists q + exists p); lia).
    repeat setoid_rewrite (Z.coprime_comm (Z.of_nat a)).
    rewrite !Z.coprime_prime_l_iff by trivial.
    case (Z.BoolSpec_divide q (Z.of_nat a)); intuition idtac;
    rewrite !Z.mod_divide in *; try trivial; try contradiction; try lia.
    case (Z.lcm_least p q (Z.of_nat a)) as [d ?]; trivial.
    cbv [Z.coprime] in coprime_p_q.
    rewrite Z.gcd_comm, Z.gcd_1_lcm_mul, Z.abs_eq in coprime_p_q by lia; rewrite coprime_p_q in *.
    assert (0 < d) by lia. zify; Z.div_mod_to_equations; nia. }

  eassert ( let f := _ in let n := _ in filter f (seq 1 n) = filter f (seq 0 (S n))) as ->.
  { cbn [seq filter]. rewrite to_Z_0. setoid_rewrite Z.gcd_0_l. rewrite (proj2 (Z.eqb_neq _ _)); trivial; lia. }
  rewrite (proj2 (Z.ltb_lt _ _)) by lia; cbn [Z.b2z].
  eassert (S _ = (Pos.to_nat p * Z.to_nat (q / 2) + S (Z.to_nat (p/2)))%nat)
    as -> by (Z.div_mod_to_equations; nia); rewrite Nat.mul_comm.

  (* filtering numerator *)
  erewrite List.filter_ext; cycle 1.
  { intros k. 
    rewrite to_Z_of_Z, <-Z.gcd_mod_l, Z.mod_mod_divide by (exists q; lia).
    exact eq_refl. }

  rewrite seq_app, seq_mul_r, List.flat_map_concat_map.
  repeat rewrite <-?List.concat_filter_map, ?map_app, ?concat_map, ?map_map, ?filter_app.
  cbn [Nat.add].

  erewrite List.map_ext; cycle 1.
  { intros i.
    replace (Pos.to_nat p) with (S (Pos.to_nat p-1)) at 2 by lia.
    cbn [List.seq List.filter].
    rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
    erewrite filter_ext_in, filter_true; [exact eq_refl|]; intros j ?%in_seq; cbv beta.
    rewrite Z.gcd_mod_l, Z.gcd_comm.
    apply Z.eqb_eq, Z.coprime_prime_l_iff; trivial.
    rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat i)); lia. }

  cbn [List.seq List.filter].
  rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
  erewrite filter_ext_in, filter_true; cycle 1. 
  { intros j ?%in_seq; cbv beta.
  rewrite Z.gcd_mod_l, Z.gcd_comm.
    apply Z.eqb_eq, Z.coprime_prime_l_iff; trivial.
  rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat (Z.to_nat (q/2)))); lia. }

  (* multiplying numerator *)
  rewrite prod_app, prod_concat, map_map.
  erewrite map_ext_in, (map_const (opp one)), prod_repeat, length_seq, Z2Nat.id; revgoals.
  { intros i **.
    rewrite <-Nat.add_1_l, Nat.add_comm. rewrite <-map_add_seq, map_map.
    erewrite map_ext_in; cycle 1.
    { intros k Hk; apply in_seq in Hk.
      rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm.
      rewrite Z.mod_add, of_Z_mod by lia. exact eq_refl. }
    rewrite <-map_map. rewrite <-tl_seq.
    rewrite <-tl_map.
    eassert (map _ _ = Zmod.elements p) as -> by trivial.
      pose proof to_Zmod_elements_prime p ltac:(trivial).
    eassert (map of_Zmod _ = Zstar.elements p) as ->.
    { erewrite <-to_Zmod_elements_prime, map_map, map_ext_in, map_id; trivial; intros.
      rewrite of_Zmod_to_Zmod. trivial. }
    rewrite prod_elements_prime by trivial. exact eq_refl. }
  { clear -odd_q; Z.div_mod_to_equations; nia. }

  erewrite <-Nat.add_1_r, <-map_add_seq, map_map, map_ext_in; cycle 1.
  { intros k **; cbv beta. rapply f_equal.
      rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm, Z2Nat.id by
      (clear -odd_p; Z.div_mod_to_equations; nia).
    rewrite Z.mod_add, of_Z_mod by lia; trivial. }

  (* filtering denominator *)
  eassert (filter _ (seq 1 _) = map (Nat.mul (Z.to_nat q)) (seq 1 (Z.to_nat (p/2)))) as ->.
  { erewrite filter_ext with (g:=fun x => (x mod Pos.to_nat q =? 0 mod Z.to_nat q)%nat); cycle 1.
    { intros i; eapply eq_true_iff_eq.
      rewrite Nat.Div0.mod_0_l.
      rewrite Z.eqb_eq, Nat.eqb_eq, <-Nat2Z.inj_iff, Nat2Z.inj_mod; lia. }
    rewrite filter_cong_seq by lia.
    rewrite Nat.Div0.mod_0_l, Nat.add_0_l, !(Nat.mod_small 1), !(Nat.div_small 1) by lia.
    assert (2 * (Z.to_nat ((Z.abs (p * q) - 1) / 2) mod Z.to_nat q) <= Z.to_nat q)%nat.
    { repeat rewrite ?Nat2Z.inj_le, ?Nat2Z.inj_mod, ?Nat2Z.inj_mul by lia.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia. }
    erewrite filter_ext_in, filter_false; cycle 1; cbn [List.app].
    { intros i ?%in_seq; apply Nat.eqb_neq; intros [d X]%Nat.Lcm0.mod_divide.
      subst i; destruct d; try nia. }
    rewrite map_ext_in with (g:=Nat.add (Z.to_nat q)), map_map; cycle 1.
    { intros iq [i [? Hi%in_seq]]%in_map_iff; subst iq.
      repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_mod, ?Nat2Z.inj_div, ?Nat2Z.inj_add, ?Nat2Z.inj_sub, ?Nat2Z.inj_mul; [|(zify; Z.to_euclidean_division_equations; nia)..].
      rewrite Zminus_mod_idemp_r.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=-2%Z) by lia.
      eassert (_+-2*q = - (1 + (Z.abs (p*q)-1)/2)) as -> by lia.
      rewrite Z_mod_nz_opp_full by
        (rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia).
      enough ((1 + (Z.abs (p * q) - 1) / 2) mod q = 1 + ((Z.abs (p * q) - 1) / 2) mod q) by lia.
      rewrite <-Z.add_mod_idemp_r by lia. rewrite Z.mod_small; trivial.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia.
    }
    rewrite map_ext with (g:=fun i => Nat.mul (Z.to_nat q) (S i)), <-map_map, seq_shift by nia.
    f_equal. f_equal. repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_div;
      zify; Z.to_euclidean_division_equations; nia. }

  (* multiplying denominator *)
  erewrite map_map, (map_ext_in (fun x : nat => of_Zmod (of_Z p (to_Z _)))); cycle 1.
  { intros ? L%in_seq.
    rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_mul, Z2Nat.id, of_Z_mod, of_Z_mul by lia.
    rewrite of_Zmod_mul; cycle 1.
    { rewrite to_Z_of_Z,  Z.coprime_mod_l_iff; trivial. }
    { rewrite to_Z_of_Z,  Z.coprime_mod_l_iff, Z.coprime_comm.
      apply Z.coprime_prime_small; trivial; lia. }
    exact eq_refl. }
  rewrite <-map_map with (g := mul _), prod_map_mul, length_map, length_seq.

  (* cancellation *)
  rewrite div_mul_same_r, Z2Nat.id by (zify; Z.div_mod_to_equations; lia).
  eassert ((p / 2) = (p-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  eassert ((q / 2) = (q-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  rewrite div_abs1_r by (rewrite euler_criterion_existsb, abs_of_bool; trivial).

  pose proof (@euler_criterion_existsb p (of_Zmod (of_Z _ q)) ltac:(trivial)) as Heul.
  apply to_Zmod_inj_iff, signed_inj_iff in Heul; revert Heul.

  (* zification *)
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite signed_mul, ?signed_pow_nonneg_r, ?signed_opp_small, ?signed_1 by
    (rewrite ?signed_1; zify; Z.div_mod_to_equations; lia).
  rewrite to_Zmod_of_Zmod by (rewrite to_Z_of_Z, Z.coprime_mod_l_iff; trivial).
  rewrite signed_of_Z, Z.smod_pow_l.
  intro Heul.
  rewrite 2Z.smod_small; trivial.

  all : clear -Heul odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.gcd_opp_l 1), Z.gcd_1_l; trivial];
     try (zify; Z.to_euclidean_division_equations; nia).
  all : destruct existsb in *; rewrite ?signed_true, ?signed_false in * by lia.
  all : rewrite Heul; clear Heul.
  all : rewrite Z.smod_small; try (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma quadratic_reciprocity'
  (p q : positive) (prime_p : Z.prime p) (prime_q : Z.prime q) (odd_p : 3 <= p) (odd_q : 3 <= q) (coprime_p_q : Z.gcd p q = 1) :
  Z.smodulo (q ^ ((p - 1) / 2)) p * Z.smodulo (p ^ ((q - 1) / 2)) q =
  (-1) ^ ((q - 1) / 2 * ((p - 1) / 2)).
Proof.
  pose proof odd_prime p prime_p odd_p as Hp'.
  pose proof odd_prime q prime_q odd_q as Hq'.

  unshelve epose proof abs_prod_positives_semiprime(p:=p)(q:=q) _ as H; trivial.
  unshelve erewrite prod_combinecong, prod_snd_abspairs, prod_fst_abspairs in H; trivial.
  progress rewrite ?Z.combinecong_mod_l, ?Z.combinecong_mod_r in H.
  apply mul_signed_subgroups_abs, eq_sym in H; trivial.
  progress replace (Z.smodulo (∏ positives (p*q)) q) with (Z.smodulo (∏ positives (q*p)) q) in H
    by (rewrite Z.mul_comm; trivial).
  erewrite 2@prod_positives_semiprime in H by (trivial || rewrite Z.coprime_comm; trivial).

  rewrite !to_Zmod_of_Zmod, !to_Z_of_Z in H.
  2: rewrite to_Z_of_Z, Z.coprime_mod_l_iff; apply Z.coprime_mul_r_iff;
    split; rewrite <-Z.coprime_mod_l_iff;
    rewrite (proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q))
    || rewrite (proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)); rewrite Z.coprime_mod_l_iff.
  rewrite <-(Z.smod_mod _ p), Z.mod_mod_divide,
    (proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), Z.mod_mod_divide,
    (proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists p; lia).

  rewrite ?(Z.smod_small ((-1)^_)), ?(Z.smod_small ((-1)^_*(-1)^_)) in H.
  enough ((-1) ^ ((p - 1) / 2) * (-1) ^ ((q - 1) / 2) <> 0) by nia.
  all : clear -odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.coprime_opp_l 1); trivial using Z.coprime_1_l];
     try (zify; Z.to_euclidean_division_equations; nia).
Qed.

End Zstar.

End Reciprocity.
