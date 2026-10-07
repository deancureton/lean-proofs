module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseSevenTwistHalfExterior

@[expose] public section

/-!
# Even attaching twists inside the positive half of a supplied filling

Start with a smooth embedded core contained in the positive region of the
original defining time. A common small radius places both actual twisted
tubes there. Compactness gives a positive uniform margin, so the same time
and regular zero set supply genuine surgery TimeData. No positive tube or
uniform margin is left as an extra existence premise.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel
open SingularMayerVietoris FramedAttachingProduct

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}

theorem exists_timeData_of_positive_tube (A : FramedAttachingProduct e a f)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s : Sphere 3, ∀ w ∈ closedBall (0 : Vector 4) A.radius,
      0 < t (A.tube (s, w))) :
    ∃ T : UnitSurgery.TimeData A, T.time = t := by
  have hc : Continuous (fun p : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦
      t (A.tube (p.1, p.2.val))) := ht.continuous.comp A.tube_embedded.continuous
  obtain ⟨δ, hδ, hδA⟩ := isCompact_univ.exists_forall_le' hc.continuousOn
    (fun p _ ↦ hpos p.1 p.2.val p.2.property)
  exact ⟨{
    time := t
    smooth := ht
    regular := hreg
    margin := δ
    margin_pos := hδ
    tube_time := fun s w hw ↦ hδA (s, ⟨w, hw⟩) (mem_univ _) }, rfl⟩

variable [T2Space M] [IsManifold (𝓡 7) ∞ M]


end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
