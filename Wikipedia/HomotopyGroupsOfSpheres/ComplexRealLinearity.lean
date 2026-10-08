module

public import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

@[expose] public section

/-! # Real linearity of the actual complex-matrix realification -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

variable {N : Type*}

theorem matrix_add (A B : Matrix N N ℂ) : matrix (A + B) = matrix A + matrix B := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> simp [matrix, add_comm]


theorem matrix_real_smul (r : ℝ) (A : Matrix N N ℂ) : matrix (r • A) = r • matrix A := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> simp [matrix]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
