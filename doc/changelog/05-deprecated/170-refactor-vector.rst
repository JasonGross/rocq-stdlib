- in `Vectors/VectorDef.v`, `Vectors/VectorSpec.v`, `Vectors/VectorEq.v` and `Vectors/Fin.v`

  + the historical `Vector` and `Fin` interfaces are deprecated in favor
    of the new names (`vec`, `fin`, `finO`, `finS`, `val`, `mk`, `app`,
    `getFin`, ...). `Vector.t`, `Vector.t_ind`, `Fin.t`, `Fin.F1`,
    `Fin.FS`, `Vector.append`, `Vector.const`, ... are deprecated
    abbreviations of the new names, so old code keeps compiling with
    deprecation warnings. The old definitions that differ from their
    replacement (`nth`, `nth_order`, `replace`, `shiftin`, `take`,
    `splitat`, `rev_append_tail`, `Fin.to_nat`, `Fin.of_nat`,
    `Fin.of_nat_lt`, ...) are kept, deprecated, with lemmas that equate
    them to the new ones (`nth_getFin`, `shiftin_snoc`, `Fin.to_nat_val`,
    `Fin.of_nat_lt_mk`, ...). `hd`, `tl`, `last`, `rev`, `rev_append`,
    `map2` and `cast` keep their names and types with new definitions.
    The definitions without a counterpart (`shiftout`, `shiftrepeat`,
    `trunc`, `fold_right2`, `fold_left2`, `Fin.weak`, `Fin.L_R`,
    `Fin.depair`, ...) are kept and deprecated; please open an issue if
    you need one of them
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    fixes `#54 <https://github.com/coq/stdlib/issues/54>`_,
    by Andres Erbsen, with help of Jason Gross).
