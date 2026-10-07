module

public import Wikipedia.HopfProblem.OrbitPairCollisionArcNeighborhoods
public import Wikipedia.HopfProblem.OrbitPairSaturatedTwoBranchNeighborhood
public import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Saturated branch neighborhoods in the full time-retaining track

The track `(t,x) ↦ (t,F(t,x))` is proper when the spatial source is compact:
its projection to time is the proper product projection. The exact slice
fibers along the two arcs determine their complete track fibers because
equality of track values forces equality of times.

The resulting open target neighborhood controls all source times. Its
entire preimage splits into two disjoint injective immersive branches,
contained in any prescribed time band about the selected collision pair.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

theorem track_isProperMap {M N : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace N] [T2Space N]
    {F : ℝ × M → N} (hF : Continuous F) : IsProperMap (track F) := by
  apply isProperMap_of_comp_of_t2 (continuous_fst.prodMk hF)
    (continuous_fst : Continuous (Prod.fst : ℝ × N → ℝ))
  exact isProperMap_fst_of_compactSpace

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

theorem CollisionArcPair.preimage_image_track_arcs
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) :
    track F ⁻¹' (track F ''
        (range (fun s : unitInterval => (t, a.firstArc s)) ∪
          range (fun s : unitInterval => (t, a.secondArc s)))) =
      range (fun s : unitInterval => (t, a.firstArc s)) ∪
        range (fun s : unitInterval => (t, a.secondArc s)) := by
  ext q
  constructor
  · rintro ⟨w, (⟨s, rfl⟩ | ⟨s, rfl⟩), heq⟩
    · have hqt : q.1 = t := (congrArg (fun z : ℝ × N => z.1) heq).symm
      have hvalue : F (t, q.2) = F (t, a.firstArc s) := by
        have hh := (congrArg (fun z : ℝ × N => z.2) heq).symm
        change F q = F (t, a.firstArc s) at hh
        simpa only [← hqt] using hh
      rcases (a.first_fiber s s.property q.2).mp hvalue with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inl ⟨s, Prod.ext hqt.symm hz.symm⟩
      · exact Or.inr ⟨0, Prod.ext hqt.symm (a.second_zero.trans hz.symm)⟩
      · exact Or.inr ⟨1, Prod.ext hqt.symm (a.second_one.trans hz.symm)⟩
    · have hqt : q.1 = t := (congrArg (fun z : ℝ × N => z.1) heq).symm
      have hvalue : F (t, q.2) = F (t, a.secondArc s) := by
        have hh := (congrArg (fun z : ℝ × N => z.2) heq).symm
        change F q = F (t, a.secondArc s) at hh
        simpa only [← hqt] using hh
      rcases (a.second_fiber s s.property q.2).mp hvalue with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inr ⟨s, Prod.ext hqt.symm hz.symm⟩
      · exact Or.inl ⟨0, Prod.ext hqt.symm (a.first_zero.trans hz.symm)⟩
      · exact Or.inl ⟨1, Prod.ext hqt.symm (a.first_one.trans hz.symm)⟩
  · intro hq
    exact ⟨q, hq, rfl⟩

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace M]


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
