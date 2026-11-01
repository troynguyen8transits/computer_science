# Editorial revision: October 31, 2026

This revision adjusts tone, historical context, and contribution language.
It retains the mathematical claims, bounds, proofs, source dependencies, and
verification scope. No Lean source or retained verification receipt was edited.

## Compare the versions

- [Current PDF](../../paper.pdf) and [current LaTeX](../../paper.tex).
- [Previous PDF](before-paper.pdf) and [previous LaTeX](before-paper.tex), copied
  byte-for-byte before this revision.
- [Exact manuscript diff](paper.patch), showing every LaTeX change in this revision.

The patch compares the archived source to the source produced by this editorial
revision. It includes the subsequent restoration of the original introduction at the author's request; other later manuscript edits are not included.

## What changed and why

| Location | Previous wording or emphasis | Revised wording or emphasis | Reason |
| --- | --- | --- | --- |
| Abstract | “contradicts the literal formulation” | “gives a counterexample … as stated” | Express the mathematical consequence directly, without suggesting a dispute with the author. |
| Introduction | Broad claims that a substantial part of complexity must be reassessed | Original paragraph retained after initially being narrowed | The author preferred the broader motivation; the other tone and attribution edits remain. |
| Conjecture discussion | “in its displayed formulation” | Explain that the conjecture followed an ETH-conditional theorem, while its displayed statement has no ETH hypothesis | Acknowledge the historical context and explain precisely which statement the result addresses. |
| Corollary | “The literal formulation … is false” | The main theorem “gives a counterexample … as stated” | Retain the same mathematical claim with constructive wording. |
| Conditional theorem discussion | “does not contradict that conditional theorem” | “the conditional theorem remains valid” | State the status of Marx's proved result affirmatively. |
| Formal endpoint table | “explicitly formalized literal conjecture” | “formalized conjecture statement” | Reduce repeated emphasis on “literal.” |
| Contribution statements | “elicited the discovery”; objective of finding a contrary algorithm for a major conjecture | Who initiated, directed, developed, and formalized the work | Preserve explicit AI attribution with factual contribution language. |

The README and manuscript metadata were aligned with these changes. The release
hashes were refreshed to identify the revised manuscript and this comparison
record. These editorial changes do not assert a new full Lean replay or an
independent review of correctness or novelty.
