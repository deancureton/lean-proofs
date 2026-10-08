module

public import Wikipedia.HopfProblem.DegreeCollapseRadialTraceBoundary
public import Wikipedia.HopfProblem.SphereHomologyTop
public import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism

@[expose] public section

/-!
# The actual normal boundary map has integral coefficient one or minus one

Use the proved integral top-homology marking of the literal two-sphere.
An actual homology isomorphism, compared with the genuine native sphere
parametrization, becomes an automorphism of the integers. Its coefficient
is therefore a unit. No orientation or generator primitivity is assumed.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

theorem two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : S₂ ≃ₜ Y) (g : C(S₂, Y)) (hg : Bijective (singularHomologyMap g 2)) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap g 2 = k • singularHomologyMap (e : C(S₂, Y)) 2 := by
  let H := unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (singularHomologyMap g 2) hg
  let J := homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, NoExoticSixSphere.IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := NoExoticSixSphere.IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 2 + 1)]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
