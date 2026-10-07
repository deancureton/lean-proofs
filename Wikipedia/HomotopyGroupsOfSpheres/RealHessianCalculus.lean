module

public import Wikipedia.HomotopyGroupsOfSpheres.RealCurveCalculus
public import Wikipedia.NoExoticSixSphere.SecondDerivativeAtCritical

@[expose] public section

/-! # The real Hessian with an explicit normed-space parameter -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

abbrev RealHessianForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def realHessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : RealHessianForm E := fderiv ℝ (fderiv ℝ f) x

end Wikipedia.HomotopyGroupsOfSpheres
