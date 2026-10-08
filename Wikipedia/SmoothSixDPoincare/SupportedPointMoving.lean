module

public import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
public import Wikipedia.SmoothSixDPoincare.CompactAmbientIsotopy
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Constructed supported point-moving isotopies

The scalar cutoff and positive motion radius are constructed from the open
chart domain. Every sufficiently nearby coordinate point can be reached by
a smooth family of global native diffeomorphisms fixed outside that chart.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)

/-- The point-moving family, its compactly supported cutoff, and its radius are all constructed. -/
theorem exists_supported_pointMoving {x : E} (hx : x ∈ Φ.source) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ⊆ Φ.source ∧ ∀ y ∈ Metric.ball x ε,
      ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
        (∀ z, A (0, z) = z) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
        (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧
        A (1, Φ x) = Φ y := by
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hx)
  obtain ⟨δ, hδ, hmove⟩ := exists_small_supported_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx)
  refine ⟨min δ ρ, lt_min hδ hρ, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hρsource
  · intro y hy
    have hnear : ‖y - x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show dist y x < min δ ρ from hy).trans_le (min_le_left _ _)
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove (y - x) hnear
    refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
    · intro t z hz
      apply hfix t z
      rintro ⟨q, hq, rfl⟩
      exact hz (Φ.map_source' (hβsupport hq))
    · have hterminal := hend x hx
      rw [hβx, one_smul] at hterminal
      have hxy : x + (y - x) = y := by abel
      exact hterminal.trans (congrArg Φ hxy)

variable [CompactSpace M]


end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
