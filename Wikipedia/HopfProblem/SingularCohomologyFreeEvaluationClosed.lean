module

public import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

@[expose] public section

/-!
# Canonical evaluation of a closed integral functional on actual homology

A closed functional on the actual chain module vanishes on the actual
incoming boundary image.  It therefore descends to chains modulo
boundaries and restricts to Mathlib's actual homology object.  The
construction has no projectivity or freeness hypothesis.  Its literal
evaluation on every cycle proves naturality and annihilation of actual
coboundaries, independently of choices of representatives.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

open SingularMayerVietoris.ModuleHomology
open FirstHurewicz.ChainHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortOpchainsModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- Being closed means annihilating the literal incoming boundary map. -/
def IsClosedFunctional (φ : K.X n →ₗ[ℤ] ℤ) : Prop :=
  ∀ b : K.X (n + 1), φ ((K.d (n + 1) n).hom b) = 0

/-- A closed functional kills the incoming boundary submodule used by the actual homology object. -/
theorem closedFunctional_range_le_ker (φ : K.X n →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional K n φ) :
    LinearMap.range (K.sc n).f.hom ≤ LinearMap.ker φ := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev n) n).hom ≤ LinearMap.ker φ
  rw [ChainComplex.prev]
  rintro x ⟨b, rfl⟩
  exact hφ b

/-- Evaluation on actual homology, by restricting the descended chain functional. -/
def evaluationOfClosed (φ : K.X n →ₗ[ℤ] ℤ) (hφ : IsClosedFunctional K n φ) :
    K.homology n →ₗ[ℤ] ℤ :=
  ((LinearMap.range (K.sc n).f.hom).liftQ φ
    (closedFunctional_range_le_ker K n φ hφ)).comp (shortHomologyToChainClass (K.sc n))

/-- Evaluation on every actual cycle is literally evaluation on its chain representative. -/
@[simp] theorem evaluationOfClosed_cycleClass (φ : K.X n →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional K n φ) (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    evaluationOfClosed K n φ hφ
      (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = φ c.1 := by
  exact congrArg ((LinearMap.range (K.sc n).f.hom).liftQ φ
    (closedFunctional_range_le_ker K n φ hφ))
    (shortHomologyToChainClass_cycleClass (K.sc n) c)




variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}



end Wikipedia.HopfProblem.SingularCohomologyFree
