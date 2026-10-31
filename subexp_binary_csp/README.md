# A Sublinear Treewidth Exponent for Binary Constraint Satisfaction

**Troy Nguyen — Bothell, Washington, USA**

[Read the paper](paper.pdf) · [LaTeX source](paper.tex) ·
[Lean reproduction](lean/REPRODUCE.md) · [Statement guide](STATEMENT_GUIDE.md)

## Result

The manuscript derives a deterministic binary-CSP decision algorithm whose
input-size exponent is sublinear in treewidth on a bounded-degree graph class
of unbounded treewidth:

```text
f(G) · ||I||^(c · tw(G) / sqrt(log tw(G))).
```

The same algorithm is correct on every valid binary CSP instance. The fast
bound applies on the stated graph class, with a graph-only factor independent
of domain size and constraint relations. The quantitative ingredient is an
exact-counting bound, uniform in the domain size D, for sufficiently large
complete-table instances of fixed maximum degree Delta:

```text
A_Delta · L^p_Delta · D^(C_Delta · k / sqrt(log k)).
```

This is a consequence of imported counting machinery, not an independent ETH
algorithm. The manuscript compares the result with the literal formulation of
Conjecture 1.4 in Marx's *Can You Beat Treewidth?* It does not contradict the
paper's ETH-conditional Theorem 1.3. Practical speedups and small constants are
not established. The graph family is existentially selected; an effective
selection of its base graph is not part of the formal result.

## Contents

- `paper.pdf`, `paper.tex`, `references.bib`: the 16-page manuscript and sources.
- `lean/`: 82 downstream Lean modules, a source-integrity manifest, a replay
  script, and imported graph-source attribution and license information.
- `evidence/`: retained successful compiler output and source/object/log hash
  receipts. These are historical verification evidence, not a new compilation
  on the reader's machine.
- `STATEMENT_GUIDE.md`: where to inspect the definitions behind the claims.

No toolchain binaries, dependency clones, compiled objects, caches, failed runs,
or development scratchwork are included.

## Verification and review status

The retained verification uses Lean 4.33.1, 82 downstream modules, and a selected
633-module imported backend closure. The final endpoint reports only
`propext`, `Classical.choice`, and `Quot.sound`. Follow
[the reproduction instructions](lean/REPRODUCE.md) for a fresh source replay.
For a lightweight integrity check of this release, run:

```sh
python3 subexp_binary_csp/verify_evidence.py
```

That command checks supplied files and retained compiler output; it does not
invoke Lean, independently validate the imported algorithm, or establish novelty.
The manuscript is provided for technical assessment. Independent human review,
exhaustive novelty assessment, and publication acceptance are not claimed.

## Credits and source provenance

Troy Nguyen elicited the downstream investigation from GPT 6.1 Sol (OpenAI) and
directed it. GPT 6.1 Sol contributed the downstream argument, formalization, and
manuscript. The paper gives the full contribution statement.

The counting recursion, grouping machinery, and native simulation infrastructure
are imported from [Anthropic's formal-math repository](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth).
Graph and separator foundations are source-ported from
[OpenAI's math repository](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a).
Imported Apache-2.0 notices, the upstream license, exact source ranges, and port
changes are retained under `lean/`. See the manuscript for scholarly references.
