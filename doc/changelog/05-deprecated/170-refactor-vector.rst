- in `Vectors/VectorDef.v`, `Vectors/VectorSpec.v`, `Vectors/VectorEq.v` and `Vectors/Fin.v`

  + the `Vector` and `Fin` interfaces are deprecated in favor of
    `Compat.Vector92` and `Compat.Fin92`. `Vector.t` and `Fin.t`
    are now abbreviations for `Vector92.t` and `Fin92.t`, so
    the old and the new interface share one type and old code
    keeps compiling with deprecation warnings. Each deprecated
    definition that has a counterpart in the new files names it in
    its `use` attribute, and the lemmas `*_92` (for instance
    `Vector.map_92`, `Vector.nth_92`, `Fin.of_nat_lt_92`) equate
    the old operations with the new ones. The definitions without a
    counterpart (`Vector.shiftout`, `Vector.shiftrepeat`,
    `Vector.trunc`, `Vector.fold_right2`, `Vector.fold_left2`,
    `Fin.weak`, `Fin.L_R`, `Fin.depair`, ...) are kept and
    deprecated; please open an issue if you need one of them
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    fixes `#54 <https://github.com/coq/stdlib/issues/54>`_,
    by Andres Erbsen, with help of Jason Gross).
