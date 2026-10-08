module

public import Wikipedia.NoExoticSixSphere.SixSphereFramedAttachingProduct
public import Wikipedia.NoExoticSixSphere.NormalizedFramedAttachingProduct

@[expose] public section

/-! # Radius-normalized framed attaching data are constructed for the actual candidate -/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)


end NoExoticSixSphere.EuclideanEmbedding
