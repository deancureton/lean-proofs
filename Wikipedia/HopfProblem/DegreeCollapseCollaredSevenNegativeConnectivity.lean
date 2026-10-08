module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseTimeCollarNegativeConnectivity
public import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenNegativeHomology
public import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero

@[expose] public section

/-!
# The original negative half is simply connected

Use the native ambient manifold charts for local path connectedness and
the existing positive-half simple connectivity. Van Kampen and the actual
collar homotopy equivalences give simple connectivity of the literal
negative half. Its original inclusion also induces an isomorphism on H0.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

theorem negativeHalf_simplyConnected [SimplyConnectedSpace B] :
    SimplyConnectedSpace S.NegativeHalf := by
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space
  let : SimplyConnectedSpace (TimeCollar.NonnegativeHalf (fun p : S.Space ↦ -S.time p)) :=
    S.collar.negativeHalf_simplyConnected
  exact S.negativeHalfTimeHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem negativeHalf_simplyConnected_of_sphere (eBoundary : B ≃ₜ Sphere 6) :
    SimplyConnectedSpace S.NegativeHalf := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  exact S.negativeHalf_simplyConnected


end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
