module

public import Wikipedia.HopfProblem.DegreeCollapseNativeMorseIndexNegation
public import Wikipedia.HopfProblem.DegreeCollapseMinimalExcellentMorse

@[expose] public section

/-!
# Transporting the native Morse minimization and cancellation argument by negation

Negation preserves excellent functions and minimality of the critical count.
It reverses both critical values and complementary indices, preserving their
order. A genuine pair removal for the negative function gives a genuine
pair removal for the original function with the reversed outer band.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

theorem distinct_critical_values_neg (hinj : InjOn f (criticalPoints E f)) :
    InjOn (fun x => -f x) (criticalPoints E (fun x => -f x)) := by
  rw [criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

theorem minimal_excellent_morse_neg
    (hminimal : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) :
    ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E (fun x => -f x)).ncard ≤ (criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh := hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [criticalPoints_neg] using hh

variable [FiniteDimensional ℝ E]



end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
