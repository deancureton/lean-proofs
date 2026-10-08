# Smooth six-sphere classification

An extraction of Boris Alexeev's smooth six-sphere classification development from
[plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e),
ported to Lean 4.35.0-rc3 and Mathlib
`6b7abb3c7686292736be2955bd3eb9ebf63b456a`.

The intended entry point is
`Wikipedia.NoExoticSixSphere.Classification`, whose theorem
`NoExoticSixSphere.noExoticSixSpheres` says that a smooth six-dimensional manifold
homeomorphic to the standard six-sphere is diffeomorphic to it. The topology and
smooth atlas on the candidate are independent inputs. The target uses Mathlib's
standard stereographic smooth structure.

This package extracts classical prerequisites, not the upstream complex-structure
construction. It includes the stable homotopy and differential topology needed by
the classification proof. The package's supported endpoint is the classification
theorem; other retained declarations support its proof or elaboration.

## Provenance

The package branch descends from the exact upstream commit.
`UPSTREAM-SHA256.json` records original hashes for retained upstream sources from commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Retained original license notices are
unchanged. The root `LICENSE` is the upstream notice, not a new blanket license.

The port adopts Lean's module system, repairs Mathlib API changes, and explicitly
transports the old finite-coordinate simplex representation to Mathlib's current
simplex. It also narrows several imports to avoid unrelated branches of the
upstream development.

The classical Hopf-fibration proof now uses a direct normalized Hermitian projector
for homotopy lifting and elementary circle-orbit algebra for its fibers. Chosen
real linear isometries identify the unit spheres with the standard Euclidean
spheres; no orientation convention is required. This replaces the upstream route
through a constructed threefold, removing its analytic construction from the
classification dependency.

The retained source closure has 6,789 Lean modules and 629,506 lines. This is a
large classical prerequisite development, even after pruning. The latest pass
removed 1,162 unused theorem commands (12,274 lines) after compiled dependency
tracing and conservative source review. The public classification theorem now
spells out its hypotheses and diffeomorphism conclusion directly.

## Verification

The classification target builds on the pinned toolchain (11,021 jobs). Its exact
recursive axiom audit visits 136,495 constants and accepts only `propext`,
`Classical.choice`, and `Quot.sound`. The final classification statement retains
the independently supplied smooth atlas. A separate type check confirms that the
expanded public statement still inhabits the original `SixSphereRigidity` type.

To repeat the checks:

```sh
lake exe cache get
lake build Wikipedia.NoExoticSixSphere.Classification
lake env lean Audit.lean
lake env lean --run tools/DeclarationTrace.lean
```

`Audit.lean` recursively inspects the endpoint's constant dependencies.
`tools/DeclarationTrace.lean` records declaration liveness and independently lists
the axiom closure. See `tools/PRUNING.md` for the source-pruning procedure.

The post-pruning dependency trace records 70,067 imported project declarations,
49,308 in the classification proof closure, and the same 136,495-constant axiom
audit. Unused imported declarations that remain can support elaboration or await
further conservative pruning; this is not a claim of declaration-minimality.
