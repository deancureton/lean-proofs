module

public import Wikipedia.NoExoticSixSphere.AnnulusCollarAmbientExtension
public import Wikipedia.NoExoticSixSphere.CompactRelativeManifoldSmoothing

@[expose] public section

/-!
# Relative smoothing of the original annulus with both collars fixed

Compact-image tubular retraction works without compactness of the target.
The actual annulus map is smoothed near the entire annulus, with both
prescribed end collars fixed exactly. A compact middle region is kept in
the specified open target set; the remaining interior values stay there
because the original map is unchanged on the protected collars.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereAnnulus

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
  (e : EuclideanEmbedding n M)


end NoExoticSixSphere.EuclideanEmbedding
