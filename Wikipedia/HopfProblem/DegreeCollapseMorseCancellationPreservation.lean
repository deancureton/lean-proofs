module

public import Wikipedia.HopfProblem.DegreeCollapseNativeCubicCancellation
public import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Native Morse nondegeneracy survives supported critical-pair removal

Every surviving critical point has its entire original function germ.
All other points of the replacement are regular. Consequently an original
Morse function remains Morse, using the actual maximal atlas and Hessians.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellationPreservation

open Wikipedia.SmoothSixDPoincare ManifoldMorse
open LocalFunctionReplacement NativeCubicCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]

omit [FiniteDimensional ℝ E] in
theorem isMorseAt_of_same_germ {f g : M → ℝ} {x : M}
    (hf : IsMorseAt E f x) (heq : g =ᶠ[𝓝 x] f) : IsMorseAt E g x := by
  obtain ⟨e, he, hx, hgood⟩ := hf
  refine ⟨e, he, hx, ?_⟩
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.symm.continuousAt (e.map_source hx)
    rw [ContinuousAt, e.left_inv hx] at h
    exact h
  have hc : g ∘ e.symm =ᶠ[𝓝 (e x)] f ∘ e.symm := heq.comp_tendsto ht
  rw [hc.fderiv_eq, (hc.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hgood

variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem isMorseAt_of_regular {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {x : M} (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) : IsMorseAt E g x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  refine ⟨e, he, hx, Or.inl ?_⟩
  intro hc
  exact hreg ((mem_criticalPoints_iff hg he hx).mpr hc)

omit [FiniteDimensional ℝ E] in
/-- Retaining every surviving critical germ suffices to retain the Morse property. -/
theorem isMorse_of_critical_germs {f g : M → ℝ} (hf : IsMorse E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hkeep : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 → g =ᶠ[𝓝 x] f) :
    IsMorse E g := by
  intro x
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
  · exact isMorseAt_of_same_germ (hf x) (hkeep x hx)
  · exact isMorseAt_of_regular hg hx

variable [T2Space M]

omit [FiniteDimensional ℝ E] in
/-- Replacing the coordinate pair by a regular function preserves global Morse nondegeneracy. -/
theorem isMorse_replace {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {f : M → ℝ} {b₀ b₁ : D → ℝ} {K : Set D}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hb : ContDiff ℝ ∞ b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x)
    (hregular : ∀ x ∈ Φ.source, fderiv ℝ b₁ x ≠ 0) :
    IsMorse E (replace Φ f b₁) := by
  apply isMorse_of_critical_germs hm (contMDiff_replace Φ hf hb hK hKΦ hmodel hfix)
  intro y hy
  have hnot := ((critical_points_after_replacement Φ hb hK hKΦ hmodel hfix hregular y).mp hy).2
  apply replace_germ_off_support Φ hK hKΦ hmodel hfix
  rintro ⟨x, hx, rfl⟩
  exact hnot (Φ.map_source' (hKΦ hx))

variable [CompactSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellationPreservation
