module

public import Wikipedia.SmoothSixDPoincare.TangentIdentityGermIsotopy

@[expose] public section

/-!
# Germ isotopies preserving a fixed locus and a linear coordinate projection

The local coordinate constraints are only assumed on the original open
domain. Compact support makes every point outside that domain stationary.
Inside it, the scalar displacement formula proves both constraints at every
time, not just at the endpoint.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The constructed isotopy retains the original fixed locus and normal projection at all times. -/
theorem exists_relative_tangent_identity_isotopy {f : E → E} {U S : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E)
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x)
    (hS : ∀ x ∈ U ∩ S, f x = x) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧ K ⊆ U ∧ ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ x, A (0, x) = x) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
      (∀ t x, x ∉ K → A (t, x) = x) ∧
      (∀ t x, Q (A (t, x)) = Q x) ∧
      (∀ t x, x ∈ S → A (t, x) = x) ∧
      (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hscalar, hgerm⟩ :=
    exists_supported_tangent_identity_isotopy hU hzero hf hf₀ hdf
  refine ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, ?_, ?_, hgerm⟩
  · intro t x
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, map_add, map_smul, map_sub, hQ x hx, sub_self, smul_zero, add_zero]
    · rw [hfix t x (fun h => hx (hKU h))]
  · intro t x hxS
    by_cases hx : x ∈ U
    · obtain ⟨c, _, heq⟩ := hscalar t x
      rw [heq, hS x ⟨hx, hxS⟩, sub_self, smul_zero, add_zero]
    · exact hfix t x (fun h => hx (hKU h))


end Wikipedia.SmoothSixDPoincare.SmallPerturbation
