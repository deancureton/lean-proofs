module

public import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSegment
public import Wikipedia.SmoothSixDPoincare.CompactFlow

@[expose] public section

/-!
# Realizing a supported holonomy correction by the original native field

The complete compact suspension is inserted in a genuine regular-height
tube. Its exact model trajectories remain in that original tube, so native
ODE uniqueness identifies the prescribed endpoint transition and every
fixed-locus segment with the new complete native flow. The zero set,
strict descent, and all exterior field germs are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A flow vertical outside the support preserves every base region
containing that support, by applying its inverse flow to a proposed exit. -/
theorem flow_preserves_base_region (F : Flow ℝ (E × ℝ)) {K U : Set E} (hKU : K ⊆ U)
    (hfix : ∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t))
    {p : E × ℝ} (hp : p.1 ∈ U) (t : ℝ) : (F t p).1 ∈ U := by
  by_contra hout
  have hnotK : (F t p).1 ∉ K := fun h => hout (hKU h)
  have hh := hfix (F t p).1 hnotK (F t p).2 (-t)
  change F (-t) (F t p) = ((F t p).1, (F t p).2 + -t) at hh
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
  have he := congrArg (fun z : E × ℝ => z.1) hh
  change p.1 = (F t p).1 at he
  exact hout (he ▸ hp)

variable [FiniteDimensional ℝ E]
  {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M] [CompactSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
