module

public import Wikipedia.HopfProblem.DegreeCollapseReflectedSeamDiffeomorph
public import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingLocalization
public import Wikipedia.HopfProblem.DegreeCollapseSevenNormalizedFramedAttachingProduct

@[expose] public section

/-!
# Seven-dimensional surgery attachments stay uniformly away from the seam

Apply the compact closed-manifold construction to the actual reflected
double. A supplied embedded three-sphere in its positive half gets a full
normalized framed attaching product in that half. Compactness of the whole
closed attaching face gives a strictly positive time margin.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization SevenSurgery

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def time (p : Fiber d) : ℝ := p.val.1

theorem continuous_time : Continuous (time d) :=
  continuous_fst.comp continuous_subtype_val

theorem contMDiff_time (k : ℕ) (hd : m = n + k) : letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, ℝ) ∞ (time d) := by
  let := fiberAtlas d k hd
  exact contMDiff_fst.comp (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b
    (regular_map d) (k + 1) (CylinderFiberNormalFrame.dimension_eq hd))

variable (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)



end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
