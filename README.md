# Linear Lambda Calculus

This respository contains a formalization of the simply-typed lambda calculus extended with booleans, products and linear types. The main results are: (a) a syntactic proof of type soundness; and (b) a proof of equivalence between the nondeterministic and algorithmic typing relations for the language. The syntax and typing judgments are defined in the locally nameless style with cofinite quantification (see [The Locally Nameless Representation][1] and [Engineering Formal Metatheory][2] for details). The language definition is derived with minor modifications from David Walker's article [Substructural Type Systems][5] (important differences are noted below).

## Requirements

The project was developed with

* [Coq 8.7.1][3]
* [The Penn Locally Nameless Metatheory Library][4] (Metalib)

## Organization

* The language definition and infrastructure required to interface with the `Metalib` library are located in the `Linear.Language` and `Linear.Infrastructure` modules.
* The `Linear.Properties.Structural` module contains important structural lemmas such as exchange, linear weakening and strengthening, and unrestricted contraction.
* The `Linear.Properties.Soundness` and `Linear.Properties.Algorithmic` modules contain the main soundness and equivalence results mentioned above, including substitution lemmas.

## Notes

* This library does not compile with the current release of MetaLib.

* In contrast with [Walker][5] the typing and store typing relations maintain separate linear and unrestricted contexts. This simplifies the proofs of type soundness and equivalence, in addition to the definition of the store typing relation (in particular, the linear context contributes no assumptions to the typing derivation in the unrestricted case for the typing store relation).

* In the definition of the algorithmic typing relation, the inductively obtained output context cannot occur as a constructor parameter in the abstraction cases, since the synthesized output context might depend on the cofinitely quantified variable. To circumvent this problem, we existentially quantify over the output context in order to instantiate it after the cofinite quantifier.

* The product cases were removed during  restructuring of the project and never re-added. The difficulties encountered in the product cases (e.g., in the proof of preservation) are simple extensions of the difficulties encountered in the abstraction and application cases. The `Linear.Environment` and `Linear.Data` modules could use restructuring.

## License

This project is licensed under the MIT license.

[1]: http://www.chargueraud.org/softs/ln/
[2]: https://www.cis.upenn.edu/~bcpierce/papers/binders.pdf
[3]: https://coq.inria.fr
[4]: https://github.com/plclub/metalib
[5]: http://mitp-content-server.mit.edu:18180/books/content/sectbyfn?collid=books_pres_0&id=1104&fn=9780262162289_sch_0001.pdf
