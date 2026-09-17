- in `Zdivisibility.v`

  + lemmas `Z.coprime_mul_l_iff`, `Z.coprime_mul_r_iff`, `Z.coprime_pow_l_iff`,
    `Z.coprime_pow_r_iff` and `Z.coprime_prime_prime`
    (`#306 <https://github.com/coq/stdlib/pull/306>`_,
    by Andres Erbsen and Jason Gross).

- in `Factoring.v`

  + new file with the prime-power factorization `ppfactor`, the sorted prime
    factorization `factor`, the `p`-adic valuation `val`, Euler's `totient`,
    the fundamental theorem of arithmetic (`fundamental_theorem_of_arithmetic`
    and its `Permutation` form) and the induction principles `factor_ind` and
    `ppfactor_ind`
    (`#306 <https://github.com/coq/stdlib/pull/306>`_,
    by Andres Erbsen and Jason Gross).

- in `List.v`, `Sorted.v` and `Permutation.v`

  + lemmas `Forall_repeat`, `repeat_inj`, `Sorted_repeat`, `StronglySorted_app`,
    `NoDup_StronglySorted`, `HdRel_map`, `Sorted_map`,
    `StronglySorted_Permutation_unique`, `Sorted_Permutation_unique` and
    `fold_right_Permutation`
    (`#306 <https://github.com/coq/stdlib/pull/306>`_,
    by Andres Erbsen and Jason Gross).
