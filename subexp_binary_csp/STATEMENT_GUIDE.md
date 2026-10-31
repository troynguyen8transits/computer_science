# Reading the claims and formal statements

The main endpoints live in namespace `CSPConsequence`.

| Claim | Source entry point |
| --- | --- |
| Original tuple-list CSP satisfaction | `lean/Downstream/SparseDecision.lean`: `Satisfiable`; `SparseNormalization.RawValid` in its imports |
| One globally correct native decision machine | `lean/Downstream/MarxConjecture.lean`: `Correct`; `lean/Downstream/SparseNativeMachine.lean`: `exists_native` |
| Native runtime on the same machine and original size measure | `lean/Downstream/MarxConjecture.lean`: `Fast`; `lean/Downstream/SparseOrdinarySize.lean` |
| Numerical treewidth and unboundedness | `lean/Downstream/GraphWidthNumber.lean`; `MarxConjecture.tail_unbounded` |
| Closed conjecture counterexample | `lean/Downstream/MarxConjecture.lean`: `counterexample` |
| Uniform-domain exact counting | `lean/Downstream/DenseCSPTheorem.lean`: `exists_counter` |
| Network factorization and exact value | `lean/Downstream/BitNetwork.lean`: `factor_lt`, `value_eq_count` |
| Network admissibility and implemented access | `lean/Downstream/BitNetworkValidity.lean`: `is_valid`; `lean/Downstream/ProviderGive.lean`: `isNetwork` |

Read the definitions before interpreting theorem names. `Statement` is defined
as the negation of `Counterexample`; therefore `not_statement` is an immediate
logical consequence. The substantive construction is `counterexample`, along
with its CSP semantics, runtime, graph witnesses, and the paper's comparison
with Marx's actual conjecture.

The machine and constants are selected before the input and domain size. Global
correctness covers every scope-valid sparse CSP, including instances outside
the fast graph class. The fast estimate uses the same machine. The graph factor
depends on the graph and fixed constants, not on domain or relation data.

`Counterexample` packages unbounded treewidth, a little-o exponent, finite
alphabets, correctness, and runtime. Bounded degree, isomorphism closure,
treewidth at least two, and the coefficient formula are properties of the
particular witnesses and supporting lemmas in its proof.

The graph construction chooses a fixed finite base graph from an existence
theorem. No effective choice of that base is claimed. The solver does not need
to recognize membership in the graph family.

Exact counting is claimed for the complete-table format. The sparse result is
decision: support pruning need not preserve the count of assignments to unused
isolated variables. The manuscript keeps these conclusions separate.

Lean checks the formal propositions. Independent assessment is still needed
for their correspondence with conventional definitions and literature, and
for originality and significance. The paper's network contract and CSP
factorization proof are intended to make that assessment possible without
reconstructing the reduction from source code.
