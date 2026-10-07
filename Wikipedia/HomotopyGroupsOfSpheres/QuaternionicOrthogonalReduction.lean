module

public import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicThirdBottReduction
public import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameStableRange

@[expose] public section

/-! # Reduction of the remaining symplectic groups to actual orthogonal groups -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization
open BalancedRealInvolutions.FrameProjection

def piSixSpTwoEquivSecondOrthogonal (n : ℕ) (hn : 4 < n) :
    π_ 6 QuaternionicFibration.SpTwo 1 ≃* π_ 2 (OrthogonalOperators n) 1 :=
  (piSixSpTwoEquivThirdBalancedReal n hn).trans
    (balancedOrthogonalMulEquiv n 2 (by omega))

def piSevenSpTwoEquivThirdOrthogonal (n : ℕ) (hn : 5 < n) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃* π_ 3 (OrthogonalOperators n) 1 :=
  (piSevenSpTwoEquivFourthBalancedReal n hn).trans
    (balancedOrthogonalMulEquiv n 3 (by omega))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
