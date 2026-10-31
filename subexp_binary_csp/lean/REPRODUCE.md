# Reproducing the Lean result

This directory is a source overlay for a pinned upstream project, not a
standalone Lake package. All 82 supplied modules use Lean 4.33.1 and mathlib
revision `0df444a360eaa60ab8c11dca51a86af692955474`.

## Prepare the dependency project

Install the official Lean 4.33.1 toolchain through elan. Set `OVERLAY` to the
absolute path of this `lean` directory, then prepare the pinned upstream tree:

```sh
OVERLAY=/absolute/path/to/computer_science/subexp_binary_csp/lean
git clone https://github.com/anthropics/formal-math.git
cd formal-math
git checkout 16a5ce41304fcdaea4e0be7c132e1c361dc26da5
cd eth
cp -R "$OVERLAY/Downstream" .
cp "$OVERLAY/downstream_sources.json" "$OVERLAY/mathlib_roots.txt" "$OVERLAY/replay_downstream.py" .
```

Keep the upstream `lean-toolchain` and `lake-manifest.json` unchanged. From the
upstream `eth` directory, fetch the selected mathlib cache roots, build the
required imported endpoints, and compile the downstream modules:

```sh
python3 -c 'import pathlib,subprocess; subprocess.run(["lake","exe","cache","get",*pathlib.Path("mathlib_roots.txt").read_text().split()],check=True)'
lake build CountedInstance.Main ExplicitCost.GroupingLemma ExplicitCost.GroupingPoly
python3 replay_downstream.py
```

The replay validates the supplied source hashes, orders downstream imports,
and invokes Lean on every module. It rejects compiler failures, sorry warnings,
unexpected axiom reports, and source changes during a check. Fresh object and
log hashes are written to `downstream_replay_logs/results.json`. One compiler
worker is used to limit memory pressure. A failure stops the replay.

Fresh objects and logs need not match the retained Darwin-run hashes across
platforms. The supplied Lean source hashes should match on every platform.
For only a source-integrity and downstream-import check, run:

```sh
python3 replay_downstream.py --check-sources
```

That option does not invoke Lean or verify a proof.

## Endpoints and scope

Inspect `Downstream/MarxConjecture.lean`, particularly `Correct`, `Fast`,
`Counterexample`, and the proof of `counterexample`. The standalone counting
endpoint is `Downstream/DenseCSPTheorem.lean`.

The retained evidence covers 82 downstream modules and the selected imported
633-module backend closure. It is not a full replay of all 1050 upstream modules
or an independent nanoda check. Upstream challenge templates containing holes
are not in the selected endpoint closure. No polynomial-space result is claimed.

Graph sources were ported from OpenAI revision
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Their source ranges, adaptations,
and Apache-2.0 notices appear in `GraphPortManifest.json`,
`GraphPortAdaptations.diff`, `LICENSE.upstream`, and the source blocks.
