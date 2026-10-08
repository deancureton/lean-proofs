module

public import Wikipedia.NoExoticSixSphere.IntersectionTraceEndpointChart

@[expose] public section

/-!
# Reversing the actual intersection trace

Time reversal is a homeomorphism of the original coincidence loci. It
interchanges the actual endpoint sets and transports the constructed initial
half-line charts to terminal half-line charts, with coordinate `1 - t`.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.IntersectionTrace

open MapIntersections InvolutionQuotient

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : ℝ → X → Z) (g : ℝ → Y → Z)

def reverseAmbient : (ℝ × (X × Y)) ≃ₜ (ℝ × (X × Y)) where
  toFun q := (1 - q.1, q.2)
  invFun q := (1 - q.1, q.2)
  left_inv q := Prod.ext (by dsimp; ring) rfl
  right_inv q := Prod.ext (by dsimp; ring) rfl
  continuous_toFun := (continuous_const.sub continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_const.sub continuous_fst).prodMk continuous_snd

theorem reverseAmbient_mem_space_iff (q : ℝ × (X × Y)) :
    reverseAmbient q ∈ space (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) ↔ q ∈ space f g := by
  change ((0 ≤ 1 - q.1 ∧ 1 - q.1 ≤ 1) ∧
    f (1 - (1 - q.1)) q.2.1 = g (1 - (1 - q.1)) q.2.2) ↔ _
  have ht : 1 - (1 - q.1) = q.1 := by ring
  rw [ht]
  constructor
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨⟨by linarith, by linarith⟩, heq⟩
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨⟨by linarith, by linarith⟩, heq⟩

def reverseHomeomorph : space f g ≃ₜ space (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) :=
  reverseAmbient.subtype (fun q ↦ (reverseAmbient_mem_space_iff f g q).symm)

theorem reverseHomeomorph_val (q : space f g) :
    (reverseHomeomorph f g q).val = (1 - q.val.1, q.val.2) := rfl

theorem reverseHomeomorph_mem_ends_iff (q : space f g) :
    reverseHomeomorph f g q ∈ ends (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) ↔
      q ∈ ends f g := by
  change (1 - q.val.1 = 0 ∨ 1 - q.val.1 = 1) ↔ (q.val.1 = 0 ∨ q.val.1 = 1)
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith


end NoExoticSixSphere.IntersectionTrace
