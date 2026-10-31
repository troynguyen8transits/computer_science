# Retained verification evidence

- `verification.json`: final endpoint, compiler/dependency revisions, hashes,
  axiom reports, and the scope of the retained verification.
- `downstream_checks.json`: the 82 successful downstream source/object/log
  hash receipts.
- `logs/`: unmodified successful compiler output corresponding to those
  receipts. Commands may contain paths from the original verification host.
- `retained_audit.json`: summary of the retained downstream audit.
- `backend_receipt.json`: selected imported backend module hashes and endpoint
  evidence; the upstream module sources and objects are not vendored here.

The original full per-run JSON snapshots and failed development logs are
omitted. No compiled objects are shipped. Supplied log and source hashes can be
checked with `../verify_evidence.py`; that check cannot revalidate the omitted
objects or the original before/after source snapshots. For independent proof
checking, perform the source replay described in `../lean/REPRODUCE.md`.

These receipts record a successful Lean 4.33.1 verification on the original
host. They do not assert a new compiler replay at repository publication time,
an independent human review, or a proof of novelty.
