module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthNormalFrame
public import Wikipedia.NoExoticSixSphere.LocalInverse

@[expose] public section

/-!
# Quaternion tail coordinates are genuine local target coordinates at the south pole

The tail is the literal quaternion component of the standard four-sphere.
Its original native derivative at the south pole is bijective, so the
inverse-function theorem supplies a smooth local chart agreeing with it.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere.QuaternionicHopf

def tailCoordinates (x : Sphere 4) : ℍ := tailQuaternion x.val

theorem contMDiff_tailCoordinates : ContMDiff (𝓡 4) 𝓘(ℝ, ℍ) ∞ tailCoordinates := by
  let : Fact (Module.finrank ℝ (V 5) = 4 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact tailQuaternion.contDiff.contMDiff.comp contMDiff_coe_sphere


def tailDerivative : V 4 →L[ℝ] ℍ := mfderiv (𝓡 4) 𝓘(ℝ, ℍ) tailCoordinates south

theorem tailCoordinates_derivative : tailDerivative =
      tailQuaternion.comp (sphereAmbientDerivative south (Subtype.val : Sphere 4 → V 5)) := by
  let : Fact (Module.finrank ℝ (V 5) = 4 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 4) 𝓘(ℝ, V 5) ∞ (Subtype.val : Sphere 4 → V 5) := contMDiff_coe_sphere
  change mfderiv (𝓡 4) 𝓘(ℝ, ℍ) (tailQuaternion ∘ (Subtype.val : Sphere 4 → V 5)) south = _
  rw [mfderiv_comp south tailQuaternion.differentiableAt.mdifferentiableAt
    (hs.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem tailCoordinates_derivative_surjective :
    Function.Surjective tailDerivative := by
  let : Fact (Module.finrank ℝ (V 5) = 4 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let A := sphereAmbientDerivative south (Subtype.val : Sphere 4 → V 5)
  have hA : A.range = (ℝ ∙ south.val)ᗮ := range_mvfderiv_subtypeVal (n := 4) south
  intro w
  let z : V 5 := SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple w)
  have hz : z ∈ A.range := by
    rw [hA, Submodule.mem_orthogonal_singleton_iff_inner_right, south_inner_head]
    simp only [z, SphereCylinder.join_head, neg_zero]
  obtain ⟨u, hu⟩ := hz
  change A u = z at hu
  refine ⟨u, ?_⟩
  rw [tailCoordinates_derivative]
  change tailQuaternion (A u) = w
  rw [hu]
  exact tailQuaternion_join 0 w

theorem tailCoordinates_derivative_bijective :
    Function.Bijective tailDerivative := by
  have hd : Module.finrank ℝ (V 4) = Module.finrank ℝ ℍ := by
    rw [finrank_euclideanSpace_fin, Quaternion.finrank_eq_four]
  refine ⟨?_, tailCoordinates_derivative_surjective⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    tailCoordinates_derivative_surjective




end NoExoticSixSphere.QuaternionicHopf
