module

public import Wikipedia.SmoothSixDPoincare.MorseIndexThreeRelation
public import Wikipedia.SmoothSixDPoincare.MorseBandHomology

@[expose] public section

/-!
# The retained index-three class is the original transported attaching class

The native sphere parametrization sends the constructed standard top class
to the generator used in the actual relation. The original whole-sublevel
band map therefore carries its transported class to that same relation.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p q : M}
  (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

theorem indexThreeBoundary_generator
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    (d.indexThreeBoundaryEquiv hindex.out).symm 1 =
      singularHomologyMap
        (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 2).toHomeomorph.toHomotopyEquiv.toFun 2
            (unitSphereTopClass 1) := rfl

theorem indexThreeAttachingClass_parametrized
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    d.indexThreeAttachingClass hindex.out =
      singularHomologyMap
        (d.coreBoundaryMap.comp (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 2).toHomeomorph.toHomotopyEquiv.toFun) 2
            (unitSphereTopClass 1) := by
  rw [singularHomologyMap_comp]
  rfl


end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
