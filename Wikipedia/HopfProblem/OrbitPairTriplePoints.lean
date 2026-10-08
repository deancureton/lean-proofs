module

public import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Finite ordered triple points and local branch removal

A perturbation is fixed outside one source patch and has an injective
time-retaining track on that patch. If the changed branch avoids every
old double-point target at the corresponding time, no new triple point
can touch the patch. All remaining triple points are exactly the old ones
whose three source points lie outside it.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

def triplePoints (F : ℝ × M → N) : Set (ℝ × (M × (M × M))) :=
  {q | q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2 ∧
    F (q.1, q.2.1) = F (q.1, q.2.2.1) ∧ F (q.1, q.2.1) = F (q.1, q.2.2.2)}

theorem mem_triplePoints_iff {F : ℝ × M → N} {q : ℝ × (M × (M × M))} :
    q ∈ triplePoints F ↔ q.2.2.1 ≠ q.2.2.2 ∧
      (q.1, (q.2.1, q.2.2.1)) ∈ doublePoints F ∧
      (q.1, (q.2.1, q.2.2.2)) ∈ doublePoints F := by
  constructor
  · intro h
    exact ⟨h.2.2.1, ⟨h.1, h.2.2.2.1⟩, ⟨h.2.1, h.2.2.2.2⟩⟩
  · rintro ⟨hyz, hxy, hxz⟩
    exact ⟨hxy.1, hxz.1, hyz, hxy.2, hxz.2⟩

theorem triplePoints_eq_of_doublePoints_eq {F G : ℝ × M → N}
    (h : doublePoints F = doublePoints G) : triplePoints F = triplePoints G := by
  ext q
  simp only [mem_triplePoints_iff, h]


theorem finite_triplePoints {F : ℝ × M → N} (hF : (doublePoints F).Finite) :
    (triplePoints F).Finite := by
  let combine : (ℝ × (M × M)) × (ℝ × (M × M)) → ℝ × (M × (M × M)) :=
    fun p => (p.1.1, (p.1.2.1, (p.1.2.2, p.2.2.2)))
  apply ((hF.prod hF).image combine).subset
  rintro ⟨t, x, y, z⟩ ⟨hxy, hxz, -, hFxy, hFxz⟩
  exact ⟨((t, (x, y)), (t, (x, z))), ⟨⟨hxy, hFxy⟩, ⟨hxz, hFxz⟩⟩, rfl⟩

theorem triple_rotate {F : ℝ × M → N} {t : ℝ} {x y z : M}
    (h : (t, (x, (y, z))) ∈ triplePoints F) : (t, (y, (z, x))) ∈ triplePoints F :=
  ⟨h.2.2.1, h.1.symm, h.2.1.symm, h.2.2.2.1.symm.trans h.2.2.2.2, h.2.2.2.1.symm⟩

theorem triple_first_outside_modified_patch {F G : ℝ × M → N} {S : Set (ℝ × M)}
    (hfixed : ∀ p ∉ S, G p = F p)
    (hinj : InjOn (fun p : ℝ × M => (p.1, G p)) S)
    (havoid : ∀ q ∈ S, ∀ p ∈ doublePoints F, p.1 = q.1 → G q ≠ F (p.1, p.2.1))
    {t : ℝ} {x y z : M} (h : (t, (x, (y, z))) ∈ triplePoints G) : (t, x) ∉ S := by
  intro hx
  have hy : (t, y) ∉ S := by
    intro hy
    have he := hinj hx hy (Prod.ext rfl h.2.2.2.1)
    exact h.1 (congrArg (fun p : ℝ × M => p.2) he)
  have hz : (t, z) ∉ S := by
    intro hz
    have he := hinj hx hz (Prod.ext rfl h.2.2.2.2)
    exact h.2.1 (congrArg (fun p : ℝ × M => p.2) he)
  have hold : (t, (y, z)) ∈ doublePoints F := by
    refine ⟨h.2.2.1, ?_⟩
    exact (hfixed (t, y) hy).symm.trans
      ((h.2.2.2.1.symm.trans h.2.2.2.2).trans (hfixed (t, z) hz))
  exact havoid (t, x) hx (t, (y, z)) hold rfl
    (h.2.2.2.1.trans (hfixed (t, y) hy))

theorem triplePoints_eq_outside_modified_patch {F G : ℝ × M → N} {S : Set (ℝ × M)}
    (hfixed : ∀ p ∉ S, G p = F p)
    (hinj : InjOn (fun p : ℝ × M => (p.1, G p)) S)
    (havoid : ∀ q ∈ S, ∀ p ∈ doublePoints F, p.1 = q.1 → G q ≠ F (p.1, p.2.1)) :
    triplePoints G = {q ∈ triplePoints F |
      (q.1, q.2.1) ∉ S ∧ (q.1, q.2.2.1) ∉ S ∧ (q.1, q.2.2.2) ∉ S} := by
  ext q
  rcases q with ⟨t, x, y, z⟩
  constructor
  · intro h
    have hx := triple_first_outside_modified_patch hfixed hinj havoid h
    have hy := triple_first_outside_modified_patch hfixed hinj havoid (triple_rotate h)
    have hz := triple_first_outside_modified_patch hfixed hinj havoid
      (triple_rotate (triple_rotate h))
    refine ⟨⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩, hx, hy, hz⟩
    · exact (hfixed (t, x) hx).symm.trans (h.2.2.2.1.trans (hfixed (t, y) hy))
    · exact (hfixed (t, x) hx).symm.trans (h.2.2.2.2.trans (hfixed (t, z) hz))
  · rintro ⟨h, hx, hy, hz⟩
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · exact (hfixed (t, x) hx).trans (h.2.2.2.1.trans (hfixed (t, y) hy).symm)
    · exact (hfixed (t, x) hx).trans (h.2.2.2.2.trans (hfixed (t, z) hz).symm)


end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
