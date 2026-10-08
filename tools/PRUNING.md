# Classification extraction audit

The only promised artifact of this extracted package is
`NoExoticSixSphere.noExoticSixSpheres`. Do not seed all declarations in the
Classification module: this would retain unrelated results accidentally.

`DeclarationTrace.lean` is adapted from the autoformalization-cleanup skill's
`deadcode_trace.lean`. Run it only after the classification root compiles:

```
lake env lean --run tools/DeclarationTrace.lean > declaration-ranges.txt
```

Optional arguments are import module, root declaration, then additional protected
root declarations. The extra roots are an explicit ledger of elaboration dependencies
restored after a failed pruning check. Source attribution uses module names, so
`NoExoticSixSphere` names and `_private` names in Wikipedia modules are included.
The traversal itself crosses module and namespace boundaries, including external
constants, so its printed axiom closure is a separate sanity check.

The output is an inventory, not an authorization to delete every DEAD line.
`DEADMOD` means no proof-term dependency, not no elaboration side effects.
Names without source ranges remain in the inventory and require attribution or
manual inspection before their source commands can be removed.

## Safe application

1. Save an immutable copy of the compiling extraction and its exact axiom audit.
   Ensure the root and a known immediate proof dependency are LIVE, and confirm
   source ranges exist for representative public/private declarations.
2. Group source ranges by file. Keep any entire range overlapping a LIVE range,
   including structures, inductives, generated projections/recursors, and mutual
   definitions. Never delete a source command only because one generated name is
   DEAD. Treat partial-line boundaries conservatively; use parser command spans
   or inspect the complete source command before deleting it.
3. Preserve syntactic support: macros, tactics, notation, elaborators, attributes,
   local instance registrations, scoped openings/options, and import-only barrels.
   Search surviving sources for candidate names and syntactic clients. This is a
   conservative supplement; short-name text search alone is not a proof of absence.
   Proof-erased simp bridges and discarded tactic hints can require declarations
   not present in the final proof term. Keep examples until explicitly reviewed.
4. Apply bounded deletion batches from bottom to top, including each declaration's
   own `... in` wrapper but not a shared section or namespace. Remove stale imports
   only when their elaboration effects and transitive requirements are preserved.
5. Main agent rebuilds the actual classification target, audits the exact standard
   axiom closure and unchanged root type, then builds/audits the S6 adapter and
   Comparator. Restore individual hidden elaboration dependencies from the saved
   snapshot or remove genuinely unused tactic hints. Add restored names to the
   extra-root ledger and re-run tracing.
6. Repeat tracing after the first successful pruning pass; source closures change
   when discarded declarations no longer require imports. Report retained support
   separately from proof-term-live lines, and exclude external Mathlib from savings.

No deletions have been performed by preparing this tool.

## Conservative review inventory

After the complete root trace, run:

```
uv run --no-project python tools/analyze_pruning.py declaration-ranges.txt \
  --output pruning-review.json
```

This read-only analyzer requires a completed trace, a LIVE expected root, and no
nonstandard axioms. It ranks whole proof-term-dead modules and isolated declaration
ranges for manual review, recording source hashes and retained import edges.
It protects overlapping LIVE ranges, ancestors of LIVE generated names even when
the child has no range, attributes, syntax/instance support, preceding wrappers,
and any short-name textual client anywhere in the extracted source tree.

The output is deliberately not a deletion manifest: whole modules can contain
elaboration effects, imports can re-export required support, and line-only ranges
do not certify command boundaries. Review candidates against the immutable source
snapshot and apply only bounded batches with the gates above. The scanner does not
rewrite imports, prune commands, or invoke Lean. A smoke trace can be parsed with
`--expected-root Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification.matrix_mul`;
its candidates are not valid for the classification root.

## Reviewed theorem pruning

A subsequent pass removed 1,162 proof-term-dead theorem commands across 866 files,
totaling 12,274 lines. Source hashes, live-range overlap, generated descendants,
textual clients, complete command boundaries, comments and attributes were checked
before deletion. Definitions, abbreviations and direct-term proofs were deferred.
The classification target rebuilt successfully without restoring any deletion.

The surviving source in each of those files is byte-identical to the baseline
after applying only the reviewed range deletions. The separate change to the
classification theorem expands its statement rather than changing its proof.
This remains a conservative pruning pass, not a declaration-minimal extraction.

The second full trace records 70,067 project constants, 49,308 live project
constants, and a 136,495-constant total closure. The strict audit and the trace
both report exactly the three standard axioms. A separate Lean type check confirms
that the expanded public theorem still inhabits the original `SixSphereRigidity`
type. The declaration list remains useful for further review; unreferenced support
and direct-term theorem proofs have not been indiscriminately removed.
