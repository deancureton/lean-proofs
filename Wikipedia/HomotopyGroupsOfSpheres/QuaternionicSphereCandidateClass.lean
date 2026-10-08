module

public import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpherePreimages
public import Wikipedia.HomotopyGroupsOfSpheres.ProjectedSphereDegree

@[expose] public section

/-! # The global candidate defines an actual native class with its actual projected degree -/

noncomputable section

open scoped Topology unitInterval Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicFibration
open Wikipedia.HopfProblem.SphereHomology

def sphereCandidateBasepoint : Sphere 7 := sphereSourcePoint 0 0 axis

theorem sphereCandidateBasepoint_image : sphereCandidate sphereCandidateBasepoint = 1 :=
  sphereCandidate_outer_zero (Latitude.point 5 0 (sphereFiveHomeomorph.symm axis))

def sphereCandidateClass : π_ 7 SpTwo 1 :=
  pointedMap sphereCandidate sphereCandidateBasepoint 1 sphereCandidateBasepoint_image
    (sphereSevenGenerator sphereCandidateBasepoint)

def sphereCandidateDegreeMap : C(Sphere 7, Sphere 7) := projectedSphereMap sphereCandidate

theorem sphereCandidateClass_projectionDegree :
    (projectionDegree sphereCandidateClass).toAdd = sphereSevenDegree sphereCandidateDegreeMap :=
  projectionDegree_pointed_sphereMap sphereCandidate sphereCandidateBasepoint
    sphereCandidateBasepoint_image


end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
