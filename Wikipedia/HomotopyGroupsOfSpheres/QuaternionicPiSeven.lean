module

public import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPiSixVanishing
public import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorHomotopy
public import Wikipedia.HomotopyGroupsOfSpheres.Circle

@[expose] public section

/-!
# The actual seventh homotopy group of Sp(2) is infinite cyclic

Compose the checked symplectic, frame, and orthogonal comparisons with the
spinor circle connecting isomorphism and the actual circle winding number.
The resulting integral marking defines a generator of the original group.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

namespace OrthogonalLowGroups

def spinorPiTwoMulEquiv (q : RankSixComplexProjection.UnitSpinor) :
    π_ 2 (OrthogonalComplexStructures.Space 6) (RankSixComplexProjection.fromSpinor q) ≃*
      Multiplicative ℤ :=
  (RankSixComplexProjection.SpinorFibration.connectingMulEquiv q 1 (by decide)).trans
    (HomotopyGroup.pi1MulEquivFundamentalGroup.trans (circleFundamentalGroupEquiv 1))

def piThreeRankSixMulEquiv : π_ 3 (OrthogonalOperators 6) 1 ≃* Multiplicative ℤ :=
  (rankSixDegreeShiftMulEquiv 2 (by decide)).symm.trans
    (spinorPiTwoMulEquiv (Classical.choice (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one)))

end OrthogonalLowGroups

namespace QuaternionicColumns

/-- The checked composite stays abstract in subsequent group calculations. -/
@[irreducible] def piSevenSpTwoMulEquiv :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃* Multiplicative ℤ :=
  (piSevenSpTwoEquivThirdOrthogonal 6 (by decide)).trans OrthogonalLowGroups.piThreeRankSixMulEquiv

def piSevenSpTwoGenerator : π_ 7 QuaternionicFibration.SpTwo 1 :=
  piSevenSpTwoMulEquiv.symm (Multiplicative.ofAdd 1)

theorem piSevenSpTwoMulEquiv_generator :
    piSevenSpTwoMulEquiv piSevenSpTwoGenerator = Multiplicative.ofAdd 1 :=
  piSevenSpTwoMulEquiv.apply_symm_apply _

theorem piSevenSpTwoGenerator_zpow_coordinates (a : π_ 7 QuaternionicFibration.SpTwo 1) :
    piSevenSpTwoGenerator ^ (piSevenSpTwoMulEquiv a).toAdd = a := by
  apply piSevenSpTwoMulEquiv.injective
  rw [map_zpow, piSevenSpTwoMulEquiv_generator]
  change Multiplicative.ofAdd ((piSevenSpTwoMulEquiv a).toAdd • (1 : ℤ)) =
    piSevenSpTwoMulEquiv a
  simp


end QuaternionicColumns
end Wikipedia.HomotopyGroupsOfSpheres
