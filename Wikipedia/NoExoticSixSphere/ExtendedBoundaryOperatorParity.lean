module

public import Wikipedia.NoExoticSixSphere.FramedCollaredDiskParity

@[expose] public section

/-!
# Original sphere parity from an extending boundary operator

The smooth disk need not be an immersion at interior points. It suffices
that its actual combined boundary operator, with the prescribed raw normal
columns, extends through injective operators. The native boundary chain
rule and positive collar height identify the same collar homotopy as
before, giving the original source-twisted sphere obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary
open SphereThreeTangentFrame CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)


end NoExoticSixSphere.EuclideanEmbedding
