module

public import Wikipedia.HopfProblem.DegreeCollapseBasinSublevelPaths
public import Wikipedia.HopfProblem.DegreeCollapseUnitSphereOnePoints
public import Wikipedia.HopfProblem.DegreeCollapseZeroOneBasinCancellation
public import Wikipedia.SmoothSixDPoincare.MorseCellCover

@[expose] public section

/-!
# Distinct attaching components give a single minimum-basin branch

The two actual attaching points of an index-one handle cannot have a common
forward limit strictly below its lower level if their images are not joined
in that original sublevel. Once one branch is known to limit to a chosen
critical point, exactly one attaching parameter and exactly one lower-level
basin point have that endpoint.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.one_handle_forward_parameters_single
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : f p < S.toSurgeryWindows.lower q)
    (hone : nativeMorseIndex E f q = 1)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v))
    (hu : Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap u).val) atTop (𝓝 p.val)) :
    {w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 |
      Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap w).val) atTop (𝓝 p.val)}.ncard = 1 := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  apply ncard_unitSphere_predicate_one hindex _ u v hu
  intro hv
  exact hnot (joined_sublevel_of_common_forward_limit S.flow hf.continuous
    (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
    ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v) hp hu hv)


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
