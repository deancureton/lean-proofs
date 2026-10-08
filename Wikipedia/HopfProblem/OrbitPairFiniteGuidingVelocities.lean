module

public import Wikipedia.HopfProblem.OrbitPairCollisionGuidingVelocity

@[expose] public section

/-!
# Simultaneous transverse guiding directions at all collisions

Globally exact collision fibers imply that the first-source map on ordered
collisions is injective. The supported spatial construction therefore
prepares the finitely many ordered collisions one at a time, preserving
every earlier guiding direction and all globally exact collision fibers.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open FamilyDoublePoints SynchronizedPairs

theorem first_injOn_of_global_collision_fibers {M N : Type*} {F : ℝ × M → N}
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p) :
    InjOn first (doublePoints F) := by
  intro p hp q hq hfirst
  have hvalue : F (second q) = F (first p) := hq.2.symm.trans (congrArg F hfirst.symm)
  rcases (hglobal p hp (second q)).mp hvalue with h | h
  · exact False.elim (hq.1 (congrArg Prod.snd (hfirst.symm.trans h.symm)))
  · have ht : p.1 = q.1 := congrArg (fun z : ℝ × M => z.1) hfirst
    have hx : p.2.1 = q.2.1 := congrArg (fun z : ℝ × M => z.2) hfirst
    have hy : p.2.2 = q.2.2 := congrArg (fun z : ℝ × M => z.2) h.symm
    exact Prod.ext ht (Prod.ext hx hy)

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace K N]

structure GuidingVelocityState (F F' : ℝ × M → N) (T : Set ℝ) : Prop where
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F'
  spatial : ∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)
  regular : RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2}
  collisions : doublePoints F' = doublePoints F
  full : ∀ q ∈ collisionSources F', Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)
  globalFibers : ∀ p ∈ doublePoints F', HasGlobalProjectedCollisionFiber F' p
  fixed : ∀ t x, t ∉ T → F' (t, x) = F (t, x)
  fixedCollisions : ∀ q ∈ collisionSources F, F' q = F q


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
