module

public import Wikipedia.HopfProblem.DegreeCollapseSheetPassageChartGerm

@[expose] public section

/-!
# Put the constructed passages at one common crossing time

The clock is an actual increasing smooth diffeomorphism fixing zero and
one. Its germ at one half is a translation, so the positive longitudinal
crossing rate is retained. Comparing two passages can therefore use the
same radial parameter chart at the same source point.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_centered_passage_clock {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧ D 1 = 1 ∧ D (1 / 2) = τ ∧ StrictMono D ∧
      MapsTo D (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ((D : ℝ → ℝ) =ᶠ[𝓝 (1 / 2 : ℝ)] fun t => t + (τ - 1 / 2)) ∧
      HasDerivAt (D : ℝ → ℝ) 1 (1 / 2) := by
  obtain ⟨D, hfix, hgerm, hpoint, hmono, -⟩ :=
    MorseRearrangement.exists_increasing_interval_translation
      (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num) hτ
  have h0 : D 0 = 0 := hfix 0 (by simp)
  have h1 : D 1 = 1 := hfix 1 (by simp)
  refine ⟨D, h0, h1, hpoint, hmono, ?_, hgerm, ?_⟩
  · intro t ht
    exact ⟨h0 ▸ hmono.monotone ht.1, h1 ▸ hmono.monotone ht.2⟩
  · exact ((hasDerivAt_id (1 / 2 : ℝ)).add_const (τ - 1 / 2)).congr_of_eventuallyEq hgerm

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
