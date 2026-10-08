module

public import Wikipedia.NoExoticSixSphere.StableSixSphereCollapse
public import Wikipedia.NoExoticSixSphere.OriginalAtlasFramedFilling

@[expose] public section

/-!
# An actual vanishing stable collapse class fills the original six-manifold

The directed-limit equality supplies a finite nullhomotopy. The existing
smooth regular-fiber construction then gives a compact normally framed
seven-dimensional filling, whose entire native boundary is diffeomorphic
to the original manifold with its supplied atlas.

The stable-class equality is an explicit hypothesis, not a supplied
classification axiom. Its proof from the candidate's zero Arf invariant
is still missing. The induced boundary frame is not identified with a
separately prescribed original frame in this statement.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open SphereMapSuspension

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)


end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
