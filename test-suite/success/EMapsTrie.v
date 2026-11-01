(* Extensional tries (EMaps.Trie): interface instance and computation checks *)
From Stdlib Require Import PArith List String.
From Stdlib Require Import OrderedTypeEx FMapInterface FMapFacts EMaps.Trie.
Import ListNotations.
#[local] Open Scope positive_scope.
#[local] Open Scope string_scope.

(* The tries implement [FMapInterface.S], including the facts functors. *)
Module M : S with Module E := PositiveOrderedTypeBits := Trie.FMap.
Module F := FMapFacts.Properties Trie.FMap.
Module OF := FMapFacts.OrdProperties Trie.FMap.

Import Trie.FMap.

Definition m1 := add 5 "five" (add 1 "one" (add 3 "three" (empty string))).

Check eq_refl : elements m1 = [(1, "one"); (5, "five"); (3, "three")].
Check eq_refl : elements (remove 3 m1) = [(1, "one"); (5, "five")].
Check eq_refl : elements (mapi (fun k s => (k, s)) m1)
  = [(1, (1, "one")); (5, (5, "five")); (3, (3, "three"))].
Check eq_refl : elements (map String.length m1) = [(1, 3%nat); (5, 4%nat); (3, 5%nat)].
Check eq_refl : elements (map2 (fun a b =>
    match a, b with
    | Some a, Some b => Some (a ++ b)
    | Some a, None => Some a
    | None, Some b => Some b
    | None, None => None
    end) m1 (add 2 "two" (add 5 "FIVE" (empty string))))
  = [(2, "two"); (1, "one"); (5, "fiveFIVE"); (3, "three")].
Check eq_refl : fold (fun k _ acc => k :: acc) m1 nil = [3; 5; 1].
Check eq_refl : cardinal m1 = 3%nat.
Check eq_refl : equal String.eqb m1 m1 = true.
Check eq_refl : equal String.eqb m1 (remove 5 m1) = false.
Check eq_refl : mem 5 m1 = true.
Check eq_refl : find 7 m1 = None.
(* [to_list] is in preorder, [elements] in the order of [PositiveOrderedTypeBits]. *)
Check eq_refl : Trie.to_list m1 = [(1, "one"); (3, "three"); (5, "five")].

(* Extensionality: equal maps are Leibniz-equal, so these hold by computation. *)
Check eq_refl : remove 1 (add 1 "x" (empty string)) = empty string.
Check eq_refl : add 3 "a" (add 1 "b" (empty string)) = add 1 "b" (add 3 "a" (empty string)).
Check eq_refl : add 1 "a" (add 1 "b" (empty string)) = add 1 "a" (empty string).

Goal forall A (m m' : t A), Equal m m' -> m = m'.
Proof. intros. now apply Trie.FMapAdditionalFacts.Equal_eq. Qed.
