module

public import Wikipedia.HopfProblem.DegreeCollapseOneHandleBasinUniqueness

@[expose] public section

/-!
# Actual minimum endpoints below the first positive-index handle

If every lower critical point has index zero, compact strict descent gives
each lower-level point an actual minimum endpoint. Distinct attaching
components force distinct endpoints for the two branches. No endpoint or
connection is supplied to this theorem.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.lower_level_forward_minimum
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (x : (S.data q).LowerLevel) :
    ∃ p : criticalPoints E f, nativeMorseIndex E f p = 0 ∧
      f p < S.toSurgeryWindows.lower q ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val) := by
  obtain ⟨r, hr, p, hp, -, hlim, hheight⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct (x : M)
  have hx : (x : M) ∉ criticalPoints E f := (S.data q).lower_regular x x.property
  have hlow : f p < S.toSurgeryWindows.lower q := by
    change f p < f q - (S.data q).radius ^ 2
    have hh := (hheight hx).1
    simpa only [x.property] using hh
  exact ⟨⟨p, hp⟩, hbefore ⟨p, hp⟩ (hlow.trans (S.toSurgeryWindows.lower_lt_value q)),
    hlow, hlim⟩


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
