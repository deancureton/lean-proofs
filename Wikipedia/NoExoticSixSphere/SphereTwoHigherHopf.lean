module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.HigherHopfNativeEquivalence
public import Wikipedia.HomotopyGroupsOfSpheres.SphereTwoThird
public import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix

@[expose] public section

/-!
# Higher Hopf comparison on the literal two- and three-spheres

The actual normal and meridian sphere homeomorphisms put the ORIGINAL
Hopf projection on the standard Euclidean spheres. Its higher native
isomorphisms retain that continuous map and explicit image-basepoint
equality. In degree six the proved quaternionic calculation therefore
also computes the actual sixth homotopy group of the two-sphere.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres
open Wikipedia.HomotopyGroupsOfSpheres.HopfDirect

namespace NoExoticSixSphere.HigherHopf

def sphereProjection : C(Sphere 3, Sphere 2) :=
  (HopfDirect.baseCoordinates : C(_, _)).comp
    ((sphereMap).comp (HopfDirect.totalCoordinates.symm : C(_, _)))

theorem sphereProjection_surjective : Function.Surjective sphereProjection :=
  HopfDirect.baseCoordinates.surjective.comp
    ((sphereMap_surjective).comp HopfDirect.totalCoordinates.symm.surjective)

def spherePiMulEquiv (n : ℕ) (x : Sphere 3) :
    π_ (n + 3) (Sphere 3) x ≃* π_ (n + 3) (Sphere 2) (sphereProjection x) :=
  (homeomorphMulEquiv (N := Fin (n + 3)) HopfDirect.totalCoordinates.symm x).trans
    ((piMulEquiv n
      (HopfDirect.totalCoordinates.symm x)).trans
        (homeomorphMulEquiv (N := Fin (n + 3)) HopfDirect.baseCoordinates
          (sphereMap (HopfDirect.totalCoordinates.symm x))))

theorem spherePiMulEquiv_apply (n : ℕ) (x : Sphere 3) (c : π_ (n + 3) (Sphere 3) x) :
    spherePiMulEquiv n x c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection (y := x) rfl c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

def spherePointedPiEquiv (n : ℕ) (x : Sphere 3) (y : Sphere 2) (h : sphereProjection x = y) :
    π_ (n + 3) (Sphere 3) x ≃* π_ (n + 3) (Sphere 2) y :=
  (spherePiMulEquiv n x).trans (basepointEqMulEquiv h)

theorem spherePointedPiEquiv_apply (n : ℕ) (x : Sphere 3) (y : Sphere 2)
    (h : sphereProjection x = y) (c : π_ (n + 3) (Sphere 3) x) :
    spherePointedPiEquiv n x y h c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection h c := by
  cases h
  exact spherePiMulEquiv_apply n x c

def preimage (x : Sphere 2) : Sphere 3 := (sphereProjection_surjective x).choose

theorem preimage_projection (x : Sphere 2) : sphereProjection (preimage x) = x :=
  (sphereProjection_surjective x).choose_spec

def sphereTwoPiEquiv (n : ℕ) (x : Sphere 2) :
    π_ (n + 3) (Sphere 2) x ≃* π_ (n + 3) (Sphere 3) (preimage x) :=
  (spherePointedPiEquiv n (preimage x) x (preimage_projection x)).symm

theorem sphereTwoPiEquiv_symm_apply (n : ℕ) (x : Sphere 2)
    (c : π_ (n + 3) (Sphere 3) (preimage x)) :
    (sphereTwoPiEquiv n x).symm c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection (preimage_projection x) c :=
  spherePointedPiEquiv_apply n (preimage x) x (preimage_projection x) c

def piSixSphereTwoMulEquiv (x : Sphere 2) : π_ 6 (Sphere 2) x ≃* Multiplicative (ZMod 12) :=
  (sphereTwoPiEquiv 3 x).trans (pi6_sphere_three_mulEquiv (preimage x))

end NoExoticSixSphere.HigherHopf
