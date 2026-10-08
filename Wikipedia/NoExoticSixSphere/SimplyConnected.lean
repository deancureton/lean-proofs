module

public import Wikipedia.NoExoticSixSphere.Definitions
public import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

@[expose] public section

/-!
# Simple connectivity of candidates for exotic six-spheres

This is a topological prerequisite for applying the smooth h-cobordism theorem,
not a substitute for that theorem or the smooth classification.
-/

namespace NoExoticSixSphere

universe u

/-- Every loop on the standard six-sphere contracts. -/
theorem sphere_six_simplyConnected : SimplyConnectedSpace (Sphere 6) :=
  EuclideanSphere.simplyConnectedSpace 4

/-- A candidate exotic six-sphere is simply connected, independently of its atlas. -/
theorem simplyConnectedSpace_of_homeomorph {M : Type u} [TopologicalSpace M]
    (e : M ≃ₜ Sphere 6) : SimplyConnectedSpace M := by
  let _ := sphere_six_simplyConnected
  exact e.toHomotopyEquiv.simplyConnectedSpace


end NoExoticSixSphere
