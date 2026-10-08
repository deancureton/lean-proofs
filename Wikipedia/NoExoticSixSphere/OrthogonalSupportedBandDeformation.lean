module

public import Wikipedia.NoExoticSixSphere.OrthogonalBandDeformation
public import Wikipedia.NoExoticSixSphere.UpperEnergyHomotopyCutoff

@[expose] public section

/-!
# Noncritical-band descent on all admissible polygons

The existing sublevel deformation is extended by an upper time cutoff. It
acts on the entire admissible polygon space, fixes both the lower and upper
energy regions, never increases energy, and lowers a prescribed intermediate
sublevel. Critical points outside the active band need not be excluded.
-/

open Set unitInterval
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem isCompact_energySublevel_of_le (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) {E B : ℝ} (hEB : E ≤ B)
    (hB : IsCompact (energySublevel a b τ B)) : IsCompact (energySublevel a b τ E) := by
  have he : ContinuousOn (energy a b τ) (energySublevel a b τ B) :=
    (contMDiffOn_energy a b τ).continuousOn.mono (fun _ hz ↦ hz.1)
  have heq : energySublevel a b τ E = energySublevel a b τ B ∩ energy a b τ ⁻¹' Iic E := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.trans hEB⟩, hz.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.2⟩
  rw [heq]
  exact (he.preimage_isClosed_of_isClosed hB.isClosed isClosed_Iic).isCompact

theorem exists_supported_band_deformation (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (l k u v E : ℝ) (hlk : l < k) (huv : u < v) (hvE : v < E)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ z ∈ energyBand a b τ l E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) z ≠ 0) :
    ∃ F : C(admissible a b m, admissible a b m),
      ∃ H : ContinuousMap.HomotopyRel (ContinuousMap.id _) F
        {z : admissible a b m | energy a b τ z.1 ≤ l ∨ v ≤ energy a b τ z.1},
        (∀ t z, energy a b τ (H (t, z)).1 ≤ energy a b τ z.1) ∧
          ∀ z, energy a b τ z.1 ≤ u → energy a b τ (F z).1 ≤ k := by
  obtain ⟨F₀, H₀, hle, hlow⟩ := exists_band_deformation a b τ l k E hlk hcompact hn
  let f : C(admissible a b m, ℝ) := ⟨fun z ↦ energy a b τ z.1,
    (contMDiffOn_energy a b τ).continuousOn.comp_continuous continuous_subtype_val
      (fun z ↦ z.2)⟩
  let A := {z : admissible a b m | f z < E}
  let inc : C(A, energySublevel a b τ E) := ⟨fun z ↦ ⟨z.1.1, z.1.2, z.2.le⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let H : C(I × A, admissible a b m) := ⟨fun tz ↦
    ⟨(H₀ (tz.1, inc tz.2)).1, (H₀ (tz.1, inc tz.2)).2.1⟩,
    (continuous_subtype_val.comp (H₀.continuous.comp
      (continuous_fst.prodMk (inc.continuous.comp continuous_snd)))).subtype_mk _⟩
  have hzero : ∀ z : A, H (0, z) = z.1 := by
    intro z
    apply Subtype.ext
    change (H₀ (0, inc z)).1 = z.1.1
    exact congrArg (fun w : energySublevel a b τ E ↦ w.1) (H₀.apply_zero (inc z))
  have hfixed : ∀ (t : I) (z : A), f z.1 ≤ l → H (t, z) = z.1 := by
    intro t z hz
    apply Subtype.ext
    change (H₀ (t, inc z)).1 = z.1.1
    exact congrArg (fun w : energySublevel a b τ E ↦ w.1)
      (H₀.eq_fst t (x := inc z) hz)
  have hEnergy : ∀ (t : I) (z : A), f (H (t, z)) ≤ f z.1 :=
    fun t z ↦ hle t (inc z)
  have hLower : ∀ z : A, f (H (1, z)) ≤ k := by
    intro z
    change energy a b τ (H₀ (1, inc z)).1 ≤ k
    rw [H₀.apply_one]
    exact hlow (inc z)
  exact UpperEnergyHomotopyCutoff.exists_extension f l k u v E huv hvE H hzero hfixed hEnergy hLower


end NoExoticSixSphere.OrthogonalPolygon
