module

public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

noncomputable section

namespace Wikipedia.HopfProblem

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def legacySimplexHomeomorph : stdSimplex ℝ ι ≃ₜ Convexity.StdSimplex ℝ ι where
  toFun s := {
    weights := Finsupp.equivFunOnFinite.symm s
    nonneg i := by simpa using s.property.1 i
    total := by simpa [Finsupp.sum_fintype] using s.property.2 }
  invFun s := ⟨s.weights, s.nonneg, s.total_of_fintype⟩
  left_inv s := by ext i; simp; rfl
  right_inv s := by ext i; simp; rfl
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    convert (continuous_subtype_val : Continuous (fun s : stdSimplex ℝ ι ↦ s.val))
      using 1
    funext s i
    simp [Function.comp_def]
    rfl
  continuous_invFun :=
    (continuous_pi (Convexity.StdSimplex.continuous_weights_apply ℝ)).subtype_mk _

@[simp] theorem legacySimplexHomeomorph_apply_weights (s : stdSimplex ℝ ι) (i : ι) :
    (legacySimplexHomeomorph s).weights i = s i := by
  simp [legacySimplexHomeomorph]

@[simp] theorem legacySimplexHomeomorph_symm_apply
    (s : Convexity.StdSimplex ℝ ι) (i : ι) :
    legacySimplexHomeomorph.symm s i = s.weights i := rfl

theorem legacySimplexHomeomorph_map (f : ι → κ) (s : stdSimplex ℝ ι) :
    legacySimplexHomeomorph (stdSimplex.map f s) =
      Convexity.StdSimplex.map f (legacySimplexHomeomorph s) := by
  classical
  ext i
  change FunOnFinite.linearMap ℝ ℝ f s i =
    (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s)) i
  rfl

theorem legacySimplexHomeomorph_symm_map
    (f : ι → κ) (s : Convexity.StdSimplex ℝ ι) :
    legacySimplexHomeomorph.symm (Convexity.StdSimplex.map f s) =
      stdSimplex.map f (legacySimplexHomeomorph.symm s) := by
  apply legacySimplexHomeomorph.injective
  rw [legacySimplexHomeomorph_map, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem
