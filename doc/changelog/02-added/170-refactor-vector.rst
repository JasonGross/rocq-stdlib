- in `Compat/Vector92.v`, `Compat/Fin92.v` and `Vectors/VectorFin.v`

  + new interface for length-indexed lists (`vec`) and bounded
    natural numbers (`fin`). The types are the same inductives as
    before, but the element type and the length are implicit
    arguments of the constructors, and the lemmas reason through
    the injective conversions `to_list` and `to_nat` and the small
    inversions `inj_0` and `inj_S` instead of dependent pattern
    matching. Operations follow the names of `List`: `app`, `rev`,
    `firstn`, `skipn`, `repeat`, `snoc`, `get`, `put`, `getFin`,
    `putFin`, `cast`
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    fixes `#54 <https://github.com/coq/stdlib/issues/54>`_,
    by Andres Erbsen, with help of Jason Gross).

- in `Lists/List.v`

  + lemma `rev_cons`
    (`#170 <https://github.com/coq/stdlib/pull/170>`_,
    by Andres Erbsen).
