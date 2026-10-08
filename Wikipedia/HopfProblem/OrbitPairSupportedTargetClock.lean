module

public import Wikipedia.HopfProblem.OrbitPairNativeTargetClock
public import Wikipedia.HopfProblem.OrbitPairTargetClockUnorderedTransport
public import Wikipedia.HopfProblem.OrbitPairGlobalProjectedNeighborhood
public import Mathlib.Geometry.Manifold.BumpFunction

@[expose] public section

/-!
# A supported target clock selecting one collision value

The globally exact fiber at the selected collision gives a target
neighborhood whose whole source preimage lies in the permitted time and
spatial region. A native target bump is one at this collision value and
zero at every other collision value. Its small multiples yield actual
native retimings, with exact event relocation and unchanged other events.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open FamilyDoublePoints SynchronizedPairs NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_supported_target_clock_at_collision
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (hfinite : (doublePoints F).Finite)
    {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ t x, t ≤ a → F (t, x) = F (a, x))
    (hhi : ∀ t x, b ≤ t → F (t, x) = F (b, x))
    {p : ℝ × (M × M)} (hglobal : HasGlobalProjectedCollisionFiber F p)
    (hptime : p.1 ∈ Ioo a b) {U : Set M} (hU : IsOpen U)
    (hxU : p.2.1 ∈ U) (hyU : p.2.2 ∈ U) :
    ∃ β : N → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ β ∧ HasCompactSupport β ∧
      β (F (first p)) = 1 ∧
      (∀ q ∉ Ioo a b ×ˢ U, β (F q) = 0) ∧
      (∀ q ∈ doublePoints F,
        F (first q) ≠ F (first p) → β (F (first q)) = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε →
        HasNativeRetiming (I := I) (J := J) F (fun z => δ * β z) a b := by
  classical
  let Z : Set N := F '' collisionSources F
  have hZ : Z.Finite := (finite_collisionSources hfinite).image F
  let O₀ : Set N := (Z \ {F (first p)})ᶜ
  have hO₀ : IsOpen O₀ := (hZ.sdiff (t := {F (first p)})).isClosed.isOpen_compl
  have hpO₀ : F (first p) ∈ O₀ := fun h => h.2 (mem_singleton _)
  have hVtime : Ioo a b ×ˢ U ⊆ Ioo a b ×ˢ (univ : Set M) :=
    fun _ h => ⟨h.1, mem_univ _⟩
  obtain ⟨O, hO, hOO₀, hpO, hpre⟩ := exists_open_projected_neighborhood_of_global_fiber
    hF.continuous hab hlo hhi hglobal (isOpen_Ioo.prod hU) hVtime
      ⟨hptime, hxU⟩ ⟨hptime, hyU⟩ hO₀ hpO₀
  obtain ⟨β, -, hβO⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := J) (F (first p))).mem_iff.mp (hO.mem_nhds hpO)
  have hone : β (F (first p)) = 1 := β.eventuallyEq_one.eq_of_nhds
  have hfixed : ∀ q ∉ Ioo a b ×ˢ U, β (F q) = 0 := by
    intro q hq
    by_contra hn
    exact hq (hpre (hβO (subset_tsupport β hn)))
  have hvalues : ∀ q ∈ doublePoints F,
      F (first q) ≠ F (first p) → β (F (first q)) = 0 := by
    intro q hq heq
    by_contra hn
    have hmem := hOO₀ (hβO (subset_tsupport β hn))
    exact hmem ⟨⟨first q, first_mem_collisionSources hq, rfl⟩, heq⟩
  refine ⟨β, β.contMDiff, β.hasCompactSupport, hone, hfixed, hvalues, ?_⟩
  exact exists_radius_native_target_clock hF hi hreg hfinite β.contMDiff
    (fun t x ht => hfixed (t, x) (fun h => ht h.1))

def relocateCollision (F : ℝ × M → N) (p : ℝ × (M × M)) (δ : ℝ)
    (q : ℝ × (M × M)) : ℝ × (M × M) := by
  classical
  exact (if F (first q) = F (first p) then q.1 + δ else q.1, q.2)

/-- An actual small event relocation, including exact transport of all
collision data and pointwise agreement outside the permitted region. -/
def HasSupportedCollisionRelocation (F : ℝ × M → N) (a b : ℝ)
    (p : ℝ × (M × M)) (U : Set M) : Prop :=
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε → ∃ F' : ℝ × M → N,
      ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F' ∧
      (∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)) ∧
      RegularOn (I := I) (J := J) F' {p | p.2.1 ≠ p.2.2} ∧
      (doublePoints F').Finite ∧ triplePoints F' = ∅ ∧
      (∀ q ∈ collisionSources F', Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)) ∧
      (∀ q ∈ doublePoints F', HasGlobalProjectedCollisionFiber F' q) ∧
      InjOn Prod.snd (collisionSources F') ∧
      Nonempty (unorderedDoublePoints F' ≃ unorderedDoublePoints F) ∧
      (∀ q ∉ Ioo a b ×ˢ U, F' q = F q) ∧
      doublePoints F' = relocateCollision F p δ '' doublePoints F ∧
      (p.1 + δ, p.2) ∈ doublePoints F'


end Wikipedia.HopfProblem.OrbitPair.TargetClock
