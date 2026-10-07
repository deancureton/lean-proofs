module

public import Wikipedia.HomotopyGroupsOfSpheres.HopfDirectAction
public import Wikipedia.HopfProblem.HopfProjector
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.HopfDirect

open Metric

private theorem total_dimension : Module.finrank ℝ (WithLp 2 (ℂ × ℂ)) = 4 := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).toLinearEquiv.finrank_eq]
  simp

private theorem base_dimension : Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) = 3 := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).toLinearEquiv.finrank_eq]
  simp

def totalIsometry : WithLp 2 (ℂ × ℂ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((stdOrthonormalBasis ℝ (WithLp 2 (ℂ × ℂ))).reindex (finCongr (by exact total_dimension))).repr

def baseIsometry : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((stdOrthonormalBasis ℝ (WithLp 2 (ℂ × ℝ))).reindex (finCongr (by exact base_dimension))).repr

def totalCoordinates : Total ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ((WithLp.homeomorphProd 2 ℂ ℂ).symm.trans totalIsometry.toHomeomorph).subtype (fun z ↦ by
    change Complex.normSq z.1 + Complex.normSq z.2 = 1 ↔
      totalIsometry (WithLp.toLp 2 z) ∈ sphere 0 1
    rw [mem_sphere_zero_iff_norm, totalIsometry.norm_map]
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, WithLp.prod_norm_sq_eq_of_L2]
    simp only [Complex.normSq_eq_norm_sq]
    rfl)

def baseCoordinates : Base ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ((WithLp.homeomorphProd 2 ℂ ℝ).symm.trans baseIsometry.toHomeomorph).subtype (fun z ↦ by
    change Complex.normSq z.1 + z.2 ^ 2 = 1 ↔
      baseIsometry (WithLp.toLp 2 z) ∈ sphere 0 1
    rw [mem_sphere_zero_iff_norm, baseIsometry.norm_map]
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, WithLp.prod_norm_sq_eq_of_L2]
    simp only [Complex.normSq_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rfl)

theorem sphereMap_surjective : Function.Surjective sphereMap := by
  intro y
  have hex : ∃ v : ℂ × ℂ, HopfProblem.HopfProjector.project y.val v ≠ 0 := by
    by_cases h : 1 + y.val.2 = 0
    · refine ⟨(0, 1), ?_⟩
      intro he
      have h' := congrArg Prod.snd he
      simp only [HopfProblem.HopfProjector.project, map_zero, mul_zero, mul_one, zero_add,
        Prod.snd_zero, Complex.ofReal_eq_zero] at h'
      linarith
    · refine ⟨(1, 0), ?_⟩
      intro he
      have h' := congrArg Prod.fst he
      simp only [HopfProblem.HopfProjector.project, map_zero, mul_zero, mul_one, add_zero,
        Prod.fst_zero, Complex.ofReal_eq_zero] at h'
      exact h h'
  obtain ⟨v, hv⟩ := hex
  refine ⟨⟨HopfProblem.HopfProjector.normalize (HopfProblem.HopfProjector.project y.val v),
    HopfProblem.HopfProjector.normalize_size hv⟩, ?_⟩
  exact Subtype.ext (HopfProblem.HopfProjector.normalize_hopf y v hv)

end Wikipedia.HomotopyGroupsOfSpheres.HopfDirect
