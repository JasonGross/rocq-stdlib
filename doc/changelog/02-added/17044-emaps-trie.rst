- in `EMaps/Trie.v` and `FSets/FMapTrie.v`

  + new files with extensional finite maps on `positive` keys, as canonical
    binary tries (`trie`, `get`, `set`, `remove`, `map_filter`, `combine`,
    `to_list`, `extensionality`), and the module `TrieMap`, an instance of
    `FMapInterface.S` for `PositiveOrderedTypeBits` where `Equal` maps are
    Leibniz-equal (`TrieMapAdditionalFacts.Equal_eq`); adapted from the
    ptree library of Andrew W. Appel and Xavier Leroy
    (`#NNN <https://github.com/coq/stdlib/pull/NNN>`_, originally
    `rocq-prover/rocq#17044 <https://github.com/rocq-prover/rocq/pull/17044>`_,
    by Andres Erbsen, completed by Jason Gross with Claude Fable 5.1).
