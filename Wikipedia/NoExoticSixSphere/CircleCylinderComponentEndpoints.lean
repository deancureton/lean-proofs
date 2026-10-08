module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.CircleCylinderComponentState
public import Wikipedia.NoExoticSixSphere.DiffeomorphSumClopen

@[expose] public section

/-!
# The chosen component retains the whole left endpoint and either all or none of the right

A preconnected endpoint maps into a single genuine connected component.
Thus the component through an original left seam point contains every
left seam point, and its restricted boundary is either the full original
endpoint sum or exactly the original left summand. No conclusion about
connectedness of the whole double is imposed.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem leftInclusion_mem_component [PreconnectedSpace {x : Sphere m // d.leftMap x = b}]
    (x y : {x : Sphere m // d.leftMap x = b}) :
    leftInclusion d y ∈ connectedComponent (leftInclusion d x) := by
  apply (leftInclusion d).continuous.mapsTo_connectedComponent x
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ y

theorem rightInclusion_mem_component_of_mem
    [PreconnectedSpace {x : Sphere m // d.rightMap x = b}] (p : Fiber d)
    (x : {x : Sphere m // d.rightMap x = b})
    (hx : rightInclusion d x ∈ connectedComponent p) (y : {x : Sphere m // d.rightMap x = b}) :
    rightInclusion d y ∈ connectedComponent p := by
  rw [connectedComponent_eq hx]
  apply (rightInclusion d).continuous.mapsTo_connectedComponent x
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ y




end NoExoticSixSphere.CircleCylinder
