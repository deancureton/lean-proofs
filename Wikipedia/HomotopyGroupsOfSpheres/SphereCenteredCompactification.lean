module

public import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
public import Mathlib.Topology.Compactification.OnePoint.Sphere

@[expose] public section

/-! # Compactification retaining the actual centered stereographic coordinates -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def compactification (z : UnitSphere E) : OnePoint (Tangent z) ≃ₜ UnitSphere E :=
  onePointHyperplaneHomeoUnitSphere (by simp : ‖-z.val‖ = 1)

theorem compactification_coe (z : UnitSphere E) (v : Tangent z) :
    compactification z (v : OnePoint (Tangent z)) = inverse z v := rfl

theorem compactification_zero (z : UnitSphere E) :
    compactification z ((0 : Tangent z) : OnePoint (Tangent z)) = z := by
  rw [compactification_coe, inverse_zero]



end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
