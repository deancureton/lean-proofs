module

public import Wikipedia.HopfProblem.DegreeCollapseCyclicSurgeryIndex

@[expose] public section

/-!
# Centering the torsion coefficient by an even framing adjustment

If l does not divide p, subtracting a suitable even multiple of l makes
the coefficient nonzero and strictly smaller in absolute value than l.
Combined with the genuine cyclic-index formula, this gives a strict
decrease for the corresponding quotient of the same abelian group.
The divisible case is deliberately excluded, not treated as a unit case.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex

theorem centered_even_remainder (l p : ℤ) (hl : 0 < l) :
    ∃ j : ℤ, -l ≤ p - 2 * l * j ∧ p - 2 * l * j < l := by
  let j := (p + l) / (2 * l)
  have hn : 2 * l ≠ 0 := by omega
  have hpos : 0 < 2 * l := by omega
  have h0 := Int.emod_nonneg (p + l) hn
  have h1 := Int.emod_lt_of_pos (p + l) hpos
  have he := Int.emod_add_mul_ediv (p + l) (2 * l)
  refine ⟨j, ?_, ?_⟩ <;> dsimp [j] <;> omega

theorem strict_even_remainder (l p : ℤ) (hl : 0 < l) (hp : ¬ l ∣ p) :
    ∃ j : ℤ, p - 2 * l * j ≠ 0 ∧ (p - 2 * l * j).natAbs < l.natAbs := by
  obtain ⟨j, hlo, hhi⟩ := centered_even_remainder l p hl
  have hne : p - 2 * l * j ≠ 0 := by
    intro h
    apply hp
    refine ⟨2 * j, ?_⟩
    nlinarith
  have hlo' : -l < p - 2 * l * j := by
    by_contra h
    have he : p - 2 * l * j = -l := le_antisymm (le_of_not_gt h) hlo
    apply hp
    refine ⟨2 * j - 1, ?_⟩
    nlinarith
  refine ⟨j, hne, ?_⟩
  have ha : |p - 2 * l * j| < |l| := by
    rw [abs_of_pos hl]
    exact abs_lt.mpr ⟨hlo', hhi⟩
  have hc : ((p - 2 * l * j).natAbs : ℤ) < (l.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hc


end Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex
