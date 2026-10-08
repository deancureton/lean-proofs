module

public import Wikipedia.HopfProblem.OrbitPairCleanCollisionArcs
public import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

@[expose] public section

/-!
# Saturated two-branch neighborhoods of a collision-arc boundary

The full fixed-time preimage of the two projected boundary arcs is exactly
the union of their two source arcs. Compact injectivity neighborhoods and
compactness of the source then give one open target neighborhood whose
entire slice preimage splits into two disjoint injective open branches.

This controls the full time slice, not just the chosen parametrizations.
It does not yet give a time-uniform neighborhood of the six-dimensional
track or the adapted chart around a Whitney disk.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

theorem CollisionArcPair.preimage_image_source_arcs
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) :
    (fun z => F (t, z)) ⁻¹'
        ((fun z => F (t, z)) ''
          (range (fun s : unitInterval => a.firstArc s) ∪
            range (fun s : unitInterval => a.secondArc s))) =
      range (fun s : unitInterval => a.firstArc s) ∪
        range (fun s : unitInterval => a.secondArc s) := by
  ext z
  constructor
  · rintro ⟨w, (⟨s, rfl⟩ | ⟨s, rfl⟩), heq⟩
    · rcases (a.first_fiber s s.property z).mp heq.symm with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inl ⟨s, hz.symm⟩
      · exact Or.inr ⟨0, a.second_zero.trans hz.symm⟩
      · exact Or.inr ⟨1, a.second_one.trans hz.symm⟩
    · rcases (a.second_fiber s s.property z).mp heq.symm with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inr ⟨s, hz.symm⟩
      · exact Or.inl ⟨0, a.first_zero.trans hz.symm⟩
      · exact Or.inl ⟨1, a.first_one.trans hz.symm⟩
  · intro hz
    exact ⟨z, hz, rfl⟩

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace M]


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
