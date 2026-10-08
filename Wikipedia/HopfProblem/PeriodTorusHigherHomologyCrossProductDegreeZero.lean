module

public import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinear
public import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductPoints

@[expose] public section

/-!
# Actual singular cross products with a degree-zero factor

These products are literal point insertions on simplex generators. They are
bilinear on Mathlib's actual singular chains, natural under continuous maps,
and commute with the differential in the positive-degree factor.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Cross product with a degree-zero chain in the left factor. -/
def crossProductZeroLeft (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X 0 →ₗ[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) n :=
  chainBilinearLift X Y 0 n fun σ τ =>
    simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ)

/-- Cross product with a degree-zero chain in the right factor. -/
def crossProductZeroRight (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X n →ₗ[ℤ] Chains Y 0 →ₗ[ℤ] Chains (X × Y) n :=
  chainBilinearLift X Y n 0 fun σ τ =>
    simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ)

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

@[simp] theorem crossProductZeroLeft_simplex_left (n : ℕ) (σ : SingularSimplex X 0) :
    crossProductZeroLeft X Y n (simplexChain X 0 σ) =
      inducedChain (crossInsertLeft (Y := Y) (zeroSimplexValue σ)) n := by
  apply chainMap_ext Y n
  intro τ
  rw [crossProductZeroLeft, chainBilinearLift_simplex, inducedChain_simplex]

@[simp] theorem crossProductZeroLeft_simplex (n : ℕ)
    (σ : SingularSimplex X 0) (τ : SingularSimplex Y n) :
    crossProductZeroLeft X Y n (simplexChain X 0 σ) (simplexChain Y n τ) =
      simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ) := by
  rw [crossProductZeroLeft_simplex_left, inducedChain_simplex]

@[simp] theorem crossProductZeroRight_simplex_right (n : ℕ)
    (c : Chains X n) (τ : SingularSimplex Y 0) :
    crossProductZeroRight X Y n c (simplexChain Y 0 τ) =
      inducedChain (crossInsertRight (zeroSimplexValue τ)) n c := by
  have h : integerBilinearRightApply (crossProductZeroRight X Y n) (simplexChain Y 0 τ) =
      inducedChain (crossInsertRight (zeroSimplexValue τ)) n := by
    apply chainMap_ext X n
    intro σ
    simp only [integerBilinearRightApply_apply, crossProductZeroRight,
      chainBilinearLift_simplex, inducedChain_simplex]
  exact LinearMap.congr_fun h c

@[simp] theorem crossProductZeroRight_simplex (n : ℕ)
    (σ : SingularSimplex X n) (τ : SingularSimplex Y 0) :
    crossProductZeroRight X Y n (simplexChain X n σ) (simplexChain Y 0 τ) =
      simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ) := by
  rw [crossProductZeroRight_simplex_right, inducedChain_simplex]



/-- Naturality of the left degree-zero product under arbitrary continuous maps. -/
theorem crossProductZeroLeft_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Chains X 0) (b : Chains Y n) :
    inducedChain (f.prodMap g) n (crossProductZeroLeft X Y n a b) =
      crossProductZeroLeft X' Y' n (inducedChain f 0 a) (inducedChain g n b) := by
  have h : (inducedChain (f.prodMap g) n).comp
        (integerBilinearRightApply (crossProductZeroLeft X Y n) b) =
      (integerBilinearRightApply (crossProductZeroLeft X' Y' n) (inducedChain g n b)).comp
        (inducedChain f 0) := by
    apply chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, integerBilinearRightApply_apply, inducedChain_simplex,
      crossProductZeroLeft_simplex_left, zeroSimplexValue_comp]
    exact inducedChain_crossInsertLeft f g (zeroSimplexValue σ) n b
  exact LinearMap.congr_fun h a



end Wikipedia.HopfProblem.PeriodTorusHigherHomology
