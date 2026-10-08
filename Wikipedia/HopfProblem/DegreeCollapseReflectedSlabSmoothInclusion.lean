module

public import Wikipedia.HopfProblem.DegreeCollapseReflectedFiberNormalFraming
public import Wikipedia.NoExoticSixSphere.FramedSlabData

@[expose] public section

/-!
# The original framed slab embeds smoothly into the native reflected double

The original slab atlas is retained. Its Euclidean inclusion and the actual
cylinder retraction prove smoothness into the independently constructed
double. Its original immersion proves injectivity of the native derivative.
The actual boundary is precisely the zero-time seam, with matching frames.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def originalSlabPoint (p : CylinderFiberSlab.slab d.map b 0 1) : Fiber d :=
  ⟨p.val.val, (map_original d p.property p.val.val.2).trans p.val.property⟩

theorem originalSlabPoint_ambient (p : CylinderFiberSlab.slab d.map b 0 1) :
    ambientInclusion d (originalSlabPoint d p) = d.slabEuclideanInclusion p := rfl

theorem originalSlabPoint_left (x : {x : Sphere m // d.leftMap x = b}) :
    originalSlabPoint d (d.leftEndpoint x).val =
      seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x := rfl



variable (k : ℕ) (hd : m = n + k) (a : Sphere m) (A : d.FramedSlabData k hd a)

theorem contMDiff_originalSlabPoint : letI := A.atlas; letI := fiberAtlas d k hd;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) (𝓡 (k + 1)) ∞ (originalSlabPoint d) := by
  let := A.atlas
  let := fiberAtlas d k hd
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) :=
    ⟨by simp [GLOrthonormalization.Vector]⟩
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (CylinderFiberNormalFrame.dimension_eq hd) (originalSlabPoint d)).mpr
  change ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞
    (fun p : CylinderFiberSlab.slab d.map b 0 1 ↦ p.val.val)
  have he : (fun p : CylinderFiberSlab.slab d.map b 0 1 ↦
      CylinderLevelEquations.retract a (d.slabEuclideanInclusion p)) =
        (fun p ↦ p.val.val) :=
    funext (fun p ↦ CylinderLevelEquations.retract_inclusion a p.val.val)
  rw [← he]
  intro p
  have hn : (d.slabEuclideanInclusion p).snd ≠ 0 :=
    ne_zero_of_mem_unit_sphere p.val.val.2
  exact (CylinderLevelEquations.contMDiffAt_retract (m := m) a hn).comp p
    A.smooth_inclusion.contMDiffAt




end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
