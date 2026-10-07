module

public import Wikipedia.HopfProblem.HopfProjector
public import Wikipedia.HomotopyGroupsOfSpheres.HopfDirectAction

@[expose] public section

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfDirect

theorem hopf_exists_homotopy_lift {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Base)) (a₀ : C(X, Total))
    (ha₀ : ∀ x, sphereMap (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, Total), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, sphereMap (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  HopfProblem.HopfProjector.exists_lift_stationary H a₀ ha₀

end Wikipedia.HomotopyGroupsOfSpheres
