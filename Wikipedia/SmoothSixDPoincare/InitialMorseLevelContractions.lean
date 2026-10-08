module

public import Wikipedia.SmoothSixDPoincare.MorseDiskPropagation
public import Wikipedia.SmoothSixDPoincare.ManifoldFermat
public import Wikipedia.SmoothSixDPoincare.IsolatedMorseBand
public import Wikipedia.NoExoticSixSphere.SphereConnectivity

@[expose] public section

/-!
# Circle contractions in the initial regular Morse level

Distinct critical values make the compact manifold's global minimum unique.
The actual small sublevel disk and its boundary homeomorphism then supply the
initial level's circle contractions. No sphere-recognition theorem for the
whole manifold is used.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

namespace SublevelDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] {f : M → ℝ} {a : ℝ} {n : ℕ}

/-- The boundary of an actual sublevel disk of dimension at least three has circle contractions. -/
theorem circle_nullhomotopies (d : SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = a}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Hemisphere.Sphere n ≃ₜ {x : M // f x = a} := d.boundaryHomeomorph
  let forward : C(Hemisphere.Sphere n, {x : M // f x = a}) := ⟨e, e.continuous⟩
  let backward : C({x : M // f x = a}, Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := NoExoticSixSphere.sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

end SublevelDisk

namespace ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- All levels between a unique minimum and the next critical value have circle contractions. -/
theorem SignedMorseChart.circle_nullhomotopies_before_next_critical
    {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ criticalPoints E f)
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = b}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨d⟩ := c.nonempty_sublevelDisk_before_next_critical hf hunique hb hregular
  have d' : SublevelDisk (n + 1) f b := hdim ▸ d
  exact d'.circle_nullhomotopies hn

variable [Nonempty M]


end ManifoldMorse

end Wikipedia.SmoothSixDPoincare
