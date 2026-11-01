- in `EMaps/Trie.v`

  + new file with extensional finite maps on `positive` keys, as canonical
    binary tries (`trie`, `get`, `set`, `remove`, `map_filter`, `combine`,
    `extensionality`), and the module `Trie.FMap`, an instance of
    `FMapInterface.S` for `PositiveOrderedTypeBits` where `Equal` maps are
    Leibniz-equal (`FMapAdditionalFacts.Equal_eq`); adapted from the
    ptree library of Andrew W. Appel and Xavier Leroy
    (`#NNN <https://github.com/coq/stdlib/pull/NNN>`_, originally
    `rocq-prover/rocq#17044 <https://github.com/rocq-prover/rocq/pull/17044>`_,
    by Andres Erbsen, completed by Jason Gross with Claude Fable 5.1).
