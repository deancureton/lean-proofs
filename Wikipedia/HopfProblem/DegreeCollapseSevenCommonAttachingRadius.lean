module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseSevenEvenAttachingTwists
public import Wikipedia.HopfProblem.DegreeCollapseSevenNormalizedFramedAttachingProduct
public import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingLocalization

@[expose] public section

/-!
# Restrict and normalize two actual attaching products at the same radius

Restriction preserves every geometric map and normal-frame value. Applying
the same positive scale to two tubes related by an orthogonal twist retains
their exact twist formula and normalizes both available radii to two.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}

def normalizeAtRadius (A : FramedAttachingProduct e a f) (r : ℝ) (hr : 0 < r)
    (h : r ≤ A.radius) : FramedAttachingProduct e a f :=
  (A.restrict r hr h).normalizedRadius

theorem normalizeAtRadius_radius (A : FramedAttachingProduct e a f)
    (r : ℝ) (hr : 0 < r) (h : r ≤ A.radius) :
    (A.normalizeAtRadius r hr h).radius = 2 := rfl

theorem normalizeAtRadius_disk (A : FramedAttachingProduct e a f)
    (r : ℝ) (hr : 0 < r) (h : r ≤ A.radius) :
    (A.normalizeAtRadius r hr h).disk = A.disk := rfl

theorem normalizeAtRadius_tube (A : FramedAttachingProduct e a f)
    (r : ℝ) (hr : 0 < r) (h : r ≤ A.radius) (s : Sphere 3) (w : Vector 4) :
    (A.normalizeAtRadius r hr h).tube (s, w) = A.tube (s, (r / 2) • w) := rfl

theorem normalizeAtRadius_twist (A B : FramedAttachingProduct e a f)
    (ρ : C(Sphere 3, OrthogonalOperators 4))
    (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))
    (r : ℝ) (hr : 0 < r) (hA : r ≤ A.radius) (hB : r ≤ B.radius)
    (s : Sphere 3) (w : Vector 4) :
    (B.normalizeAtRadius r hr hB).tube (s, w) =
      (A.normalizeAtRadius r hr hA).tube (s, (ρ s).1.1 w) := by
  rw [normalizeAtRadius_tube, normalizeAtRadius_tube, ht, map_smul]


end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
