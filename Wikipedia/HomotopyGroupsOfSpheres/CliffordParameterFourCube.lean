module

public import Wikipedia.HomotopyGroupsOfSpheres.CliffordSixBalanced
public import Wikipedia.HomotopyGroupsOfSpheres.SphereFour
public import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
public import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
public import Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-! # An actual generating four-cube based at the Clifford pole -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open SphereCubeGenerator

local notation "Ambient" => EuclideanSpace ℝ (Fin 5)

def parameterFourBasepointIsometry : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ ((point 4).val - pole.val))ᗮ.reflection

theorem parameterFourBasepointIsometry_apply :
    parameterFourBasepointIsometry (point 4).val = pole.val := by
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp (point 4).property,
    mem_sphere_zero_iff_norm.mp pole.property]

def basedSphereFourHomeomorph : Sphere 4 ≃ₜ UnitSphere :=
  SphereCenteredCoordinates.sphereIsometry parameterFourBasepointIsometry

theorem basedSphereFourHomeomorph_point : basedSphereFourHomeomorph (point 4) = pole :=
  Subtype.ext parameterFourBasepointIsometry_apply

def parameterFourCube : GenLoop (Fin 4) UnitSphere pole :=
  pointedMapGenLoop (basedSphereFourHomeomorph : C(Sphere 4, UnitSphere)) (point 4) pole
    basedSphereFourHomeomorph_point (quotientCube 4)

def parameterFourClass : π_ 4 UnitSphere pole := ⟦parameterFourCube⟧

theorem parameterFourCube_apply (t : Fin 4 → I) :
    parameterFourCube t = basedSphereFourHomeomorph (quotient 4 t) := rfl

theorem parameterFourClass_generates :
    Function.Surjective (fun k : ℤ ↦ parameterFourClass ^ k) :=
  PointedCubeGenerators.homeomorph_cube_generates basedSphereFourHomeomorph (point 4) pole
    basedSphereFourHomeomorph_point (quotientCube 4)
    (quotientClass_generates (pi4_sphere_four_mulEquiv (point 4)))

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
