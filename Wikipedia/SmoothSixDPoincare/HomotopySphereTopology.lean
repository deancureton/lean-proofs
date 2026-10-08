module

public import Wikipedia.SmoothSixDPoincare.Statement
public import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

@[expose] public section

/-!
# Native simple connectivity from the original homotopy-sphere hypothesis

The sphere simple-connectivity proof is reused with its retained source
provenance. Native homotopy invariance transfers it to the original space;
no homeomorphism or sphere-recognition principle is used here.
-/

open ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M]

/-- Simple connectivity follows from the original homotopy equivalence with the six-sphere. -/
theorem simplyConnectedSpace_of_homotopySixSphere (e : M ≃ₕ SixSphere) :
    SimplyConnectedSpace M := by
  let : SimplyConnectedSpace SixSphere := EuclideanSphere.simplyConnectedSpace 4
  exact e.simplyConnectedSpace



end Wikipedia.SmoothSixDPoincare
