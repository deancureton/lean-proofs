module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseMeridianSphereDerivative
public import Wikipedia.HopfProblem.DegreeCollapseFirstHandleBasinControl

@[expose] public section

/-!
# A smooth transverse sphere at the first positive two-handle

The original boundary supplies the lower cap. The glued and relatively
smoothed sphere retains the exact meridian germ, one transverse whole-belt
intersection, and crossing of the original zero level at every other
source point. Global embedding and transport to the higher cut remain
separate constructions.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)


variable [SimplyConnectedSpace B]


end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
