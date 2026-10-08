module

public import Wikipedia.HopfProblem.OrbitPairGlobalProjectedCollisionFiber

@[expose] public section

/-!
# Simultaneously exact global projected fibers at every ordinary collision

Prepare the finitely many collision values in succession. Every ambient
clock step creates no new projected coincidences with any collision source,
so an already exact global fiber remains exact. The synchronized collision
set is unchanged throughout, as are all exterior time slices.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

def HasGlobalProjectedCollisionFiber {M N : Type*} (F : ℝ × M → N)
    (p : ℝ × (M × M)) : Prop :=
  ∀ z : ℝ × M, F z = F (SynchronizedPairs.first p) ↔
    z = SynchronizedPairs.first p ∨ z = SynchronizedPairs.second p

theorem HasGlobalProjectedCollisionFiber.avoids_image {M N : Type*} {F : ℝ × M → N}
    {p : ℝ × (M × M)} (hp : HasGlobalProjectedCollisionFiber F p) {C : Set (ℝ × M)}
    (hfirst : SynchronizedPairs.first p ∉ C) (hsecond : SynchronizedPairs.second p ∉ C) :
    F (SynchronizedPairs.first p) ∉ F '' C := by
  rintro ⟨q, hq, heq⟩
  rcases (hp q).mp heq with rfl | rfl
  · exact hfirst hq
  · exact hsecond hq


variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

structure ProjectedFiberState (F F' : ℝ × M → N) (U : Set ℝ) : Prop where
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F'
  collisions : FamilyDoublePoints.doublePoints F' = FamilyDoublePoints.doublePoints F
  spatial : ∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)
  regular : SynchronizedPairs.RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2}
  finite : (FamilyDoublePoints.doublePoints F').Finite
  noTriples : FamilyDoublePoints.triplePoints F' = ∅
  full : ∀ q ∈ FamilyDoublePoints.collisionSources F',
    Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)
  fixed : ∀ t x, t ∉ U → F' (t, x) = F (t, x)
  noNew : ∀ q ∈ FamilyDoublePoints.collisionSources F, ∀ z, F' q = F' z → F q = F z


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
