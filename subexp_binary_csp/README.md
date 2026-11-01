# A Sublinear Treewidth Exponent for Binary Constraint Satisfaction

Troy Nguyen · October 2026

[Paper](paper.pdf) · [LaTeX](paper.tex) · [Reproduction instructions](lean/REPRODUCE.md) · [Guide to the formal statements](STATEMENT_GUIDE.md)

This paper applies the counting machinery from Anthropic's recent ETH
refutation to binary constraint satisfaction with unrestricted domain size.
The resulting algorithm correctly decides every valid binary CSP instance.
On a bounded-degree graph class of unbounded treewidth, its running time is

$$
f(G)\,\lVert I\rVert^{c\,\operatorname{tw}(G)/\sqrt{\log\operatorname{tw}(G)}}.
$$

Here $G$ is the primal graph, and $f(G)$ depends only on the graph, independently
of the domain size and constraint relations. Since the exponent is
$o(\operatorname{tw}(G))$, this gives a counterexample to Conjecture 1.4 of
Marx's *Can You Beat Treewidth?* as stated. His ETH-conditional Theorem 1.3
remains valid.

The main step is an exact-counting bound that holds uniformly as the domain
size grows. For each fixed maximum degree $\Delta$, sufficiently large
complete-table instances with $k$ variables, domain size $D\geq2$, and input
length $L$ can be counted in time

$$
A_\Delta L^{p_\Delta}D^{C_\Delta k/\sqrt{\log k}}.
$$

The constants are independent of $D$ and the relations. Support pruning
extends the decision algorithm to sparse tuple-list inputs, and a
bounded-degree expander family connects the bound to treewidth.

The result is asymptotic; practical speedups and small constants have not been
established. The fast treewidth bound is proved for the constructed graph
class. Its construction uses an existence theorem for a finite base graph;
the solver does not need to recognize membership in the class.

## Formalization and verification

The Lean development contains 82 modules covering the CSP semantics, counting
bound, sparse-input algorithm, native machine runtime, and graph argument.
The [statement guide](STATEMENT_GUIDE.md) points to the definitions and theorem
statements behind the paper's claims.

A [fresh source replay](evidence/clean_reproduction/README.md) passed on
October 31, 2026, using a new clone of the public release and a separate pinned
upstream checkout. It rebuilt the selected imported research dependencies and
all 82 downstream modules with Lean 4.33.1, using the official mathlib cache.
All 269 printed axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The replay ran on the same machine as the original development;
independent reproduction and specialist review are still welcome.

To reproduce the compilation, follow [these instructions](lean/REPRODUCE.md).
To check the supplied files and recorded compiler output without running Lean,
run this command from the repository root:

```sh
python3 subexp_binary_csp/verify_evidence.py
```

The source is in [lean/](lean/), and the build logs and verification records
are in [evidence/](evidence/). The [editorial comparison](editorial/2026-10-31-tone/README.md)
includes the earlier manuscript and an explanation of the wording changes.

## Contributions and dependencies

I initiated and directed this investigation with GPT 6.1 Sol (OpenAI), which
developed the downstream argument, formalization, and manuscript. The paper
describes these contributions in more detail.

The counting recursion, grouping machinery, and native simulation come from
[Anthropic's formal-math repository](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth).
The expander and separator foundations were ported from
[OpenAI's math repository](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a).
The source revisions, Apache-2.0 notices, and details of the graph port are
recorded under [lean/](lean/). The contribution here is the domain-uniform CSP
application and its transfers to sparse inputs and the treewidth conjecture.
