module

public import Wikipedia.HopfProblem.SphereHomologyCoefficientsChainsFunctor
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

/-!
# The coefficient-module structure on native finite-coefficient homology

The groups `ModHomology p X n` were constructed in `ModuleCat ℤ` using the
coefficient object `ZMod p`. Multiplication by `p` is zero on that coefficient
object. Additivity of the actual coefficient and homology functors therefore
proves that it is zero on homology, giving the canonical `ZMod p` action.

This construction works for every space and degree, without any vanishing or
freeness assumption on its homology.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SphereHomologyCoefficients

/-- The native singular homology functor in its coefficient variable, with
the space and degree fixed. -/
def coefficientHomologyFunctor (X : Type) [TopologicalSpace X] (n : ℕ) :
    ModuleCat ℤ ⥤ ModuleCat ℤ :=
  nativeCoefficientFunctor X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n

instance coefficientHomologyFunctor_additive (X : Type) [TopologicalSpace X] (n : ℕ) :
    (coefficientHomologyFunctor X n).Additive := by
  unfold coefficientHomologyFunctor
  infer_instance

/-- Torsion is proved on the original native homology object by applying the
coefficient functor to the zero multiplication endomorphism. -/
theorem modHomology_nsmul_eq_zero (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ)
    (x : ModHomology p X n) : p • x = 0 := by
  have hc : p • 𝟙 (ModuleCat.of ℤ (ZMod p)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change p • z = 0
    simp [nsmul_eq_mul]
  have hh : p • 𝟙 (ModHomology p X n) = 0 := by
    change p • 𝟙 ((coefficientHomologyFunctor X n).obj (ModuleCat.of ℤ (ZMod p))) = 0
    rw [← CategoryTheory.Functor.map_id (coefficientHomologyFunctor X n),
      ← CategoryTheory.Functor.map_nsmul, hc, CategoryTheory.Functor.map_zero]
  exact congrArg (fun f : ModHomology p X n ⟶ ModHomology p X n ↦ f x) hh

/-- The canonical finite-coefficient module structure on actual singular homology. -/
abbrev modHomologyModule (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module (ZMod p) (ModHomology p X n) :=
  AddCommGroup.zmodModule (modHomology_nsmul_eq_zero p X n)


end NoExoticSixSphere
