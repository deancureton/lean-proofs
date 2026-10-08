module

public import Wikipedia.NoExoticSixSphere.GenericThreeSixJet

@[expose] public section

/-!
# One small perturbation controls both singular jets and double points

Both requirements hold almost everywhere in the same actual operator
parameter space. Their intersection therefore contains arbitrarily small
operators. The result does not choose unrelated perturbations for the
diagonal and off-diagonal problems.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.DoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem ae_regular_double_points [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ∀ᵐ A ∂μ, ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → difference f A q = 0 →
      Surjective (fderiv ℝ (difference f A) q) :=
  ParametricRegular.ae_affine_regular_operators_on μ (baseDifference f) direction
    (contDiff_baseDifference f hf) contDiff_direction (distinctDomain V)
    (fun _ h ↦ sub_ne_zero.mpr h)

theorem ae_generic_families [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ,
      OperatorRank.RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → difference f A q = 0 →
        Surjective (fderiv ℝ (difference f A) q) :=
  (ae_regular_jets μ f hf hv hw).and (ae_regular_double_points μ f hf)


end NoExoticSixSphere.DoublePointPerturbation
