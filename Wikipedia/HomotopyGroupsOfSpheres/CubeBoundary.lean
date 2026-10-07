module

public import Wikipedia.HomotopyGroupsOfSpheres.SphereTwo
public import Wikipedia.HomotopyGroupsOfSpheres.Circle
public import Wikipedia.HopfProblem.DegreeCollapseDiskCube
public import Wikipedia.HopfProblem.SixSphereCubeInterior
public import Mathlib.Topology.TietzeExtension

@[expose] public section

/-! # Extending circle-valued maps from the boundary of a three-cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem.DegreeCollapse

abbrev cubeBoundaryCoordinates : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] (Fin 3 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- The geometric boundary of the three-cube is the ordinary two-sphere. -/
def sphereTwoCubeBoundary : Sphere 2 ≃ₜ Cube.boundary (Fin 3) where
  toFun v := ⟨DiskCube.homeomorph cubeBoundaryCoordinates
      ⟨v.val, by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact (mem_sphere_zero_iff_norm.mp v.property).le⟩,
    (DiskCube.boundary_iff cubeBoundaryCoordinates _).mpr (mem_sphere_zero_iff_norm.mp v.property)⟩
  invFun u := ⟨((DiskCube.homeomorph cubeBoundaryCoordinates).symm u.val).val,
    mem_sphere_zero_iff_norm.mpr ((DiskCube.symm_boundary_iff cubeBoundaryCoordinates u.val).mpr u.property)⟩
  left_inv v := by
    apply Subtype.ext
    change (((DiskCube.homeomorph cubeBoundaryCoordinates).symm
      ((DiskCube.homeomorph cubeBoundaryCoordinates) ⟨v.val, _⟩)).val) = v.val
    rw [Homeomorph.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    exact (DiskCube.homeomorph cubeBoundaryCoordinates).apply_symm_apply u.val
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance cubeBoundary_three_simplyConnected : SimplyConnectedSpace (Cube.boundary (Fin 3)) :=
  sphereTwoCubeBoundary.symm.toHomotopyEquiv.simplyConnectedSpace

instance cubeBoundary_three_locallyPathConnected :
    LocallyPathConnectedSpace (Cube.boundary (Fin 3)) := by
  let : LocallyPathConnectedSpace (Sphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2)) (M := Sphere 2)
  exact sphereTwoCubeBoundary.isQuotientMap.locallyPathConnectedSpace

/-- Every map from the three-cube boundary to the circle has a continuous real logarithm. -/
theorem cubeBoundary_circle_log (g : C(Cube.boundary (Fin 3), Circle)) :
    ∃ F : C(Cube.boundary (Fin 3), ℝ), ∀ u, Circle.exp (F u) = g u := by
  let u₀ : Cube.boundary (Fin 3) := ⟨0, ⟨0, Or.inl rfl⟩⟩
  obtain ⟨F, ⟨_, hF⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g u₀ (Complex.arg (g u₀)) (Circle.exp_arg (g u₀))
  exact ⟨F, fun u => congrFun hF u⟩

/-- Tietze extension of the real logarithm extends every boundary map to the circle. -/
theorem cubeBoundary_circle_extension (g : C(Cube.boundary (Fin 3), Circle)) :
    ∃ G : C(Fin 3 → I, Circle), ∀ u : Cube.boundary (Fin 3), G u.val = g u := by
  obtain ⟨F, hF⟩ := cubeBoundary_circle_log g
  obtain ⟨K, hK⟩ := F.exists_restrict_eq
    (HopfProblem.SixSphereCube.isClosed_cubeBoundaryN 3)
  refine ⟨⟨fun u => Circle.exp (K u), by fun_prop⟩, fun u => ?_⟩
  change Circle.exp (K u.val) = g u
  have hu : K u.val = F u := DFunLike.congr_fun hK u
  rw [hu, hF]

end Wikipedia.HomotopyGroupsOfSpheres
