module

public import Wikipedia.NoExoticSixSphere.OrthogonalCutoffDescent
public import Wikipedia.NoExoticSixSphere.EnergyDeformationIteration
public import Wikipedia.NoExoticSixSphere.OrthogonalNoncriticalMargin
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# Deforming a polygon sublevel across a noncritical band

Compactness, the explicit velocity-jump descent and finite iteration give a
native relative homotopy from the identity on an upper energy sublevel to a
map into a lower sublevel. All slices are energy nonincreasing, and polygons
below the cutoff threshold remain fixed.
-/

open Set unitInterval
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem exists_band_deformation (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k E : ℝ) (hlk : l < k) (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ v ∈ energyBand a b τ l E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ F : C(energySublevel a b τ E, energySublevel a b τ E),
      ∃ H : ContinuousMap.HomotopyRel (ContinuousMap.id _) F
        {v : energySublevel a b τ E | energy a b τ v.1 ≤ l},
      (∀ s v, energy a b τ (H (s, v)).1 ≤ energy a b τ v.1) ∧
        ∀ v, energy a b τ (F v).1 ≤ k := by
  obtain ⟨δ, hδ, H, hzero, hfixed, hle, hdrop⟩ :=
    exists_cutoff_descent a b τ l k E hlk hcompact hn
  exact EnergyDeformationIteration.exists_lowering_homotopy H
    (fun v ↦ energy a b τ v.1) {v | energy a b τ v.1 ≤ l} k E δ hδ
    (fun v ↦ v.2.2) hzero hfixed hle hdrop


end NoExoticSixSphere.OrthogonalPolygon
