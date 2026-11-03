- in `Vectors/VectorSpec.v` and `Vectors/VectorEq.v`

  + every lemma of the two files is deprecated: their content (old and new) is in
    `Vectors/Vector.v`; the files stay with the deprecated copies, so
    `From Stdlib Require VectorSpec` and the qualified names still work
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    by Andres Erbsen, with help of Jason Gross).

- in `Vectors/VectorDef.v`, `Vectors/Vector.v` and `Vectors/Fin.v`

  + the historical `Vector` and `Fin` interfaces are deprecated in favor
    of the new names (`vec`, `fin`, `finO`, `finS`, `toNat`, `mk`, `app`,
    `getFin`, ...). `Vector.t`, `Vector.t_ind`, `Fin.t`, `Fin.F1`,
    `Fin.FS`, `Vector.append`, `Vector.const`, ... are deprecated
    abbreviations of the new names, so old code keeps compiling with
    deprecation warnings. The old definitions that differ from their
    replacement (`nth`, `nth_order`, `replace`, `shiftin`, `take`,
    `splitat`, `rev_append_tail`, `Fin.of_nat`,
    `Fin.of_nat_lt`, ...) are kept, deprecated, with lemmas that equate
    them to the new ones (`nth_getFin`, `shiftin_snoc`,
    `Fin.of_nat_lt_mk`, ...). The old `Fin.to_nat`, which returns
    `{i | i < n}`, is deprecated in favor of `Fin.toNat : fin n -> nat`
    (a coercion), with `Fin.to_nat_toNat` relating the two. `hd`, `tl`, `last`, `rev`, `rev_append`,
    `map2` and `cast` keep their names and types with new definitions.
    The definitions without a counterpart (`shiftout`, `shiftrepeat`,
    `trunc`, `fold_right2`, `fold_left2`, `Fin.weak`, `Fin.L_R`,
    `Fin.depair`, ...) are kept and deprecated; please open an issue if
    you need one of them
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    fixes `#54 <https://github.com/coq/stdlib/issues/54>`_,
    by Andres Erbsen, with help of Jason Gross).

- in `Vectors/FinFun.v`

  + the file is deprecated: no project of Rocq's CI uses its definitions,
    only its re-export of `Finite`. `Reals/Runcountable.v` now requires
    `Finite` directly
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    by Andres Erbsen, with help of Jason Gross).
