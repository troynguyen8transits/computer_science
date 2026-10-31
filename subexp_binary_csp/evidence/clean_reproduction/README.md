# Fresh source reproduction

**Result: passed.** The public release was cloned into a new directory, and
the documented dependency build and complete downstream replay succeeded.
No proof-source or dependency-version changes were required.

## Procedure

1. Clone the public `computer_science` release and the upstream Anthropic
   repository separately; check out the pinned upstream revision.
2. Copy only the published source overlay, source manifest, mathlib root list,
   and replay script into the new upstream checkout.
3. Download the selected official mathlib cache into a separate cache directory.
4. Build the three imported endpoints listed in `lean/REPRODUCE.md`.
5. Run the published replay script on all 82 supplied Lean modules.
6. Check the resulting source, object, and log hashes, axiom reports, pinned
   revisions, tracked-source cleanliness, and dependency-manifest stability.

The run reused the installed official Lean 4.33.1 compiler on the original
Darwin arm64 host. It reused no proof objects from the original investigation.
The selected official mathlib cache was downloaded; mathlib was not rebuilt
from source. The imported research endpoints and all downstream modules were
compiled in the new checkout. The directory contained no borrowed proof-object
links, and no inherited Lean search path pointed back to the original build.
The imported build produced 633 research-module objects in about 59 minutes;
the downstream replay completed in about 85 minutes. Dependency cache setup
took about two minutes. These are measured stage durations on this host, not
runtime requirements or performance guarantees for other machines.

## Evidence

- `summary.json`: tested public-release commit, dependency revisions, stage
  durations and hashes, module counts, and scope.
- `build.log`: the successful imported-endpoint build, reporting 4,434 Lake
  jobs. That count includes cached library jobs, not 4,434 fresh source modules.
- `cache.log`: retrieval of the 3,822 selected official mathlib cache files.
- `replay.log`: the complete downstream replay's progress and final result.
- `results.json`: fresh source/object/log receipts and axiom reports for all
  82 downstream modules.
- `logs/`: fresh per-module compiler output, including the final counting and
  conjecture-counterexample endpoints.

All 269 printed downstream axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. The supplied Lean source hashes match
the public release. Fresh compiled objects are not distributed here.

This is a fresh checkout and source replay on the same host, not independent
reproduction by another researcher or another proof checker. It does not
establish novelty, practical speedup, or correspondence between every informal
claim and its formal statement. It does not claim a full build of all 1,050
upstream research modules. See `../README.md` for the earlier retained evidence
and `../../lean/REPRODUCE.md` for instructions.
