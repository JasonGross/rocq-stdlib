- in `QuadraticReciprocity.v`

  + new file with Euler's criterion for `Zstar` and `Zmod`
    (`Zstar.euler_criterion`, `Zmod.euler_criterion`), the product of all
    units modulo a prime (`Zstar.prod_elements_prime`), the Chinese remainder
    decomposition of `Zmod.elements` and `Zstar.elements` for coprime moduli
    (`CRT.Zmod.elements_mul_coprime`, `CRT.Zstar.elements_mul_coprime`) and
    the law of quadratic reciprocity
    (`Reciprocity.Zstar.quadratic_reciprocity'`)
    (`#307 <https://github.com/coq/stdlib/pull/307>`_,
    by Andres Erbsen and Jason Gross).

- in `List.v`, `Finite.v`, `Permutation.v`, `Zdiv.v` and `Zdivisibility.v`

  + lemmas `filter_filter`, `negb_existsb`, `existsb_as_filter`,
    `list_prod_nil_l`, `list_prod_cons_l`, `list_prod_map_l`,
    `list_prod_map_r`, `list_prod_map_map`, `list_prod_filter_l`,
    `list_prod_filter_r`, `list_prod_filter_filter`, `NoDup_list_prod`,
    `Permutation_partition`, `Z.mod_prod_mod_factor_l`,
    `Z.mod_prod_mod_factor_r` and `Z.coprime_comm`
    (`#307 <https://github.com/coq/stdlib/pull/307>`_,
    by Andres Erbsen and Jason Gross).
