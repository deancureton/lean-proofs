module

public import Wikipedia.HopfProblem.SixthHurewiczSixSimplexBasic
public import Wikipedia.HopfProblem.FourthHurewiczFourSimplexSimplexSum

@[expose] public section

/-!
# The actual corrected six-simplex cycle

In degree six the constant simplex has the constant five-simplex as its
boundary.  Subtracting that same constant from the original based simplex
therefore gives the required cycle.  Its signed permutation-cell formula
is a specialization of the existing dimension-generic chain identity.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original six-simplex minus the actual constant six-simplex. -/
def basedSixSimplexChain (τ : BasedSixSimplex x) : Chains X 6 :=
  HigherHurewicz.correctedSimplexChain 6 x τ.val

@[simp] theorem basedSixSimplexChain_eq (τ : BasedSixSimplex x) :
    basedSixSimplexChain τ =
      simplexChain X 6 τ.val - simplexChain X 6 (ContinuousMap.const (Simplex 6) x) := rfl

theorem basedSixSimplexChain_boundary (τ : BasedSixSimplex x) :
    ((singularComplex X).d 6 5).hom (basedSixSimplexChain τ) = 0 :=
  HigherHurewicz.correctedSimplexChain_boundary 5 x τ.val (basedSixSimplex_face τ)


/-- The corrected cycle in the original unnormalized singular complex. -/
def basedSixSimplexCycle (τ : BasedSixSimplex x) :
    ModuleHomology.Cycle (singularComplex X) 6 :=
  HigherHurewicz.correctedSimplexCycle 5 x τ.val (basedSixSimplex_face τ)

@[simp] theorem basedSixSimplexCycle_val (τ : BasedSixSimplex x) :
    (basedSixSimplexCycle τ).1 = basedSixSimplexChain τ := rfl

@[simp] theorem basedSixSimplexCycle_constant (x : X) :
    basedSixSimplexCycle (constantBasedSixSimplex x) = 0 := by
  apply Subtype.ext
  exact sub_self _

/-- The signed 720-cell simplex chain is exactly the corrected six-simplex. -/
theorem basedSixSimplex_simplexChain_sum (τ : BasedSixSimplex x) :
    (∑ e : Equiv.Perm (Fin 6), HigherHurewicz.CubeTriangulation.cubeOrientation e •
      simplexChain X 6 ((basedSixSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex e))) = basedSixSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 4) τ

end Wikipedia.HopfProblem.SixthHurewicz
