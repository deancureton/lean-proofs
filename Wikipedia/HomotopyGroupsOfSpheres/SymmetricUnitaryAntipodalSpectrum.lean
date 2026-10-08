module

public import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponential

@[expose] public section

/-!
# Signed odd spectra for actual antipodal symmetric unitary generators

The endpoint equation `exp(iA) = -1` forces every real eigenvalue of a
symmetric `A` to be a signed odd multiple of `π`. For trace-zero matrices
outside the minimum-square locus, the previously constructed mixing
family gives constrained directions for the original matrix `iA`.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ImaginarySymmetricMatrices

open RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exp_imaginary_eq_neg_one_odd (x : ℝ)
    (hx : Complex.exp (Complex.I * (x : ℂ)) = -1) :
    ∃ m : ℤ, x = Real.pi * (2 * (m : ℝ) + 1) := by
  have he : Complex.exp (Complex.I * (x : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) := hx.trans Complex.exp_pi_mul_I.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hr := congrArg Complex.im hm
  simp at hr
  refine ⟨m, ?_⟩
  nlinarith only [hr]

theorem antipodal_diagonalization (A : Matrix N N ℝ) (hsym : A.transpose = A)
    (hexp : NormedSpace.exp (imaginary A) = -1) :
    ∃ (U : unitary (Matrix N N ℝ)) (m : N → ℤ),
      A = RealMatrixSquareNorm.conjugate U
        (Matrix.diagonal (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1))) ∧
      A.trace = ∑ a, Real.pi * (2 * (m a : ℝ) + 1) := by
  obtain ⟨U, μ, hA, htrace⟩ := symmetric_diagonalization A hsym
  have hA' : A = RealMatrixSquareNorm.conjugate U (Matrix.diagonal μ) := hA
  let F := Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) (toComplex U)
  have hD : NormedSpace.exp (imaginary (Matrix.diagonal μ)) = -1 := by
    apply F.injective
    change (toComplex U).val * NormedSpace.exp (imaginary (Matrix.diagonal μ)) *
      star (toComplex U).val = F (-1)
    rw [toComplex_star, ← exp_imaginary_conjugate, ← hA', hexp, map_neg, map_one]
  have hμ (a : N) : ∃ m : ℤ, μ a = Real.pi * (2 * (m : ℝ) + 1) := by
    apply exp_imaginary_eq_neg_one_odd
    have he := congrArg (fun B : Matrix N N ℂ ↦ B a a) hD
    simpa only [exp_imaginary_diagonal, Matrix.diagonal_apply_eq, Matrix.neg_apply,
      Matrix.one_apply_eq] using he
  choose m hm using hμ
  refine ⟨U, m, ?_, ?_⟩
  · rw [funext hm] at hA'
    exact hA'
  · simpa only [hm] using htrace

theorem minimal_odd_conjugate_square (U : unitary (Matrix N N ℝ)) (m : N → ℤ)
    (hm : ∀ a, m a = 0 ∨ m a = -1) :
    let A := RealMatrixSquareNorm.conjugate U
      (Matrix.diagonal (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1)))
    A * A = Real.pi ^ 2 • (1 : Matrix N N ℝ) := by
  dsimp only
  have hD :
      Matrix.diagonal (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1)) *
        Matrix.diagonal (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1)) =
      Real.pi ^ 2 • (1 : Matrix N N ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    apply congrArg Matrix.diagonal
    funext a
    rcases hm a with h | h <;> norm_num [h, pow_two]
  rw [RealMatrixSquareNorm.conjugate_mul, hD, map_smul]
  change Real.pi ^ 2 • (U.val * 1 * U.val.transpose) = Real.pi ^ 2 • (1 : Matrix N N ℝ)
  rw [mul_one, ← star_eq_transpose, Unitary.mul_star_self_of_mem U.property]

end ImaginarySymmetricMatrices

namespace BalancedRealInvolutions

open ImaginarySymmetricMatrices


end BalancedRealInvolutions

end Wikipedia.HomotopyGroupsOfSpheres
