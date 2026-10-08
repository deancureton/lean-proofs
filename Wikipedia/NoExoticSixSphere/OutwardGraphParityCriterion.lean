module

public import Wikipedia.NoExoticSixSphere.OutwardGraphNormalCoordinates
public import Wikipedia.NoExoticSixSphere.BoundaryOperatorParityCriterion

@[expose] public section

/-!
# Original geometric sphere parity from a framed hypersurface boundary operator

The original boundary frame is an appended normal frame, in explicitly
retained normal-model coordinates. Graph the height derivative and use
the proved two-stage homotopy. The resulting extension criterion concerns
the original geometric sphere parity, not a newly assigned obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary OutwardGraphFrame CollaredDiskFrame

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)


end NoExoticSixSphere.EuclideanEmbedding
