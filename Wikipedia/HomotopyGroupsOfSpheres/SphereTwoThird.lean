module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HomotopyGroupsOfSpheres.HopfInjectivity
public import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
public import Wikipedia.HomotopyGroupsOfSpheres.HopfDirectCoordinates

@[expose] public section

/-!
# The third homotopy group of the two-sphere

The actual Hopf sphere map induces an isomorphism on third homotopy groups.
Homeomorphisms to the ordinary Euclidean spheres and the third Hurewicz
calculation for the three-sphere identify this group with the integers.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfDirect

/-- Transport the chosen base point along an actual equality. -/
def basepointMulEquiv {X : Type} [TopologicalSpace X] {x y : X} (h : x = y) :
    π_ 3 X x ≃* π_ 3 X y := by
  cases h
  exact MulEquiv.refl _

/-- The third native homotopy group of the standard two-sphere is infinite cyclic. -/
def pi3_sphere_two_mulEquiv (x : Sphere 2) :
    π_ 3 (Sphere 2) x ≃* Multiplicative ℤ := by
  let eB := HopfDirect.baseCoordinates
  let eE := HopfDirect.totalCoordinates
  let v : Total := Classical.choose (sphereMap_surjective (eB.symm x))
  have hv : sphereMap v = eB.symm x :=
    Classical.choose_spec (sphereMap_surjective (eB.symm x))
  let e₃ : π_ 3 (Total) v ≃* Multiplicative ℤ :=
    (homeomorphMulEquiv (N := Fin 3) eE v).trans (pi3_sphere_three_mulEquiv (eE v))
  let e₂ : π_ 3 (Base) (eB.symm x) ≃* Multiplicative ℤ :=
    (basepointMulEquiv hv.symm).trans
      ((hopfPi3MulEquiv v).symm.trans e₃)
  exact (homeomorphMulEquiv (N := Fin 3) eB.symm x).trans e₂

end Wikipedia.HomotopyGroupsOfSpheres
