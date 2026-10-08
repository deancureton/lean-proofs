module

public import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeSymmetries
public import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometryPermutations

@[expose] public section

/-!
# The six signed summands in native cube recovery order

The existing enumeration of actual permutations is reordered to match the
six chamber homotopies. Its coefficients remain the literal permutation
signs used by the geometric tetrahedral subdivision.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open Geometry

/-- The order `012, 021, 201, 102, 120, 210` of the six recovery chambers. -/
def nativeCubeRecoveryPermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  cubePermutation ∘ Equiv.swap 2 3

theorem nativeCubeRecoveryPermutation_apply (i : Fin 6) :
    nativeCubeRecoveryPermutation i =
      ![1, Equiv.swap 1 2, nativeCubeCycle201, Equiv.swap 0 1,
        nativeCubeCycle120, Equiv.swap 0 2] i := by
  fin_cases i <;> rfl

/-- This is a bijection onto the original permutation type, not a replacement index. -/
theorem nativeCubeRecoveryPermutation_bijective :
    Function.Bijective nativeCubeRecoveryPermutation :=
  cubePermutation_bijective.comp (Equiv.swap 2 3).bijective

theorem nativeCubeRecoveryPermutation_injective :
    Function.Injective nativeCubeRecoveryPermutation :=
  nativeCubeRecoveryPermutation_bijective.injective



@[simp] theorem cubeOrientation_nativeCubeCycle120 :
    cubeOrientation nativeCubeCycle120 = 1 := by
  simp [cubeOrientation, nativeCubeCycle120, Equiv.Perm.sign_swap']

@[simp] theorem cubeOrientation_nativeCubeCycle201 :
    cubeOrientation nativeCubeCycle201 = 1 := by
  simp [cubeOrientation, nativeCubeCycle201, Equiv.Perm.sign_swap']

/-- The unsigned sum in the exact order used by cube recovery. -/
theorem sum_nativeCubeRecoveryPermutations {A : Type*} [AddCommMonoid A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, F e = F 1 + F (Equiv.swap 1 2) + F nativeCubeCycle201 +
      F (Equiv.swap 0 1) + F nativeCubeCycle120 + F (Equiv.swap 0 2) := by
  rw [← nativeCubeRecoveryPermutation_bijective.sum_comp F]
  simp [nativeCubeRecoveryPermutation_apply, Fin.sum_univ_succ, add_assoc]

/-- The exact six-term signed sum, valid in every additive commutative group. -/
theorem sum_oriented_nativeCubeRecoveryPermutations {A : Type*} [AddCommGroup A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, cubeOrientation e • F e =
      F 1 - F (Equiv.swap 1 2) + F nativeCubeCycle201 - F (Equiv.swap 0 1) +
        F nativeCubeCycle120 - F (Equiv.swap 0 2) := by
  rw [sum_nativeCubeRecoveryPermutations]
  simp [cubeOrientation, nativeCubeCycle120, nativeCubeCycle201,
    Equiv.Perm.sign_swap', sub_eq_add_neg]



theorem nativeCubeSwap01_mul_swap12 :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 = nativeCubeCycle120 := rfl




theorem nativeCubeSwap12_mul_swap01 :
    Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 = nativeCubeCycle201 := rfl


end Wikipedia.HopfProblem.ThirdHurewicz
