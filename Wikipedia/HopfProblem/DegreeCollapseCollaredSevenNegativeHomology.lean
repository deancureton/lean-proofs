module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseTimeCollarNegativeHomology
public import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenNegativeCollar
public import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenUpperHomology

@[expose] public section

/-!
# The original complementary-half homology map in a cleared seven-state

The literal nonpositive half and the nonnegative half of the reversed time
are identified by the identity on ambient points. Mayer--Vietoris and the
proved positive-half acyclicity then give isomorphisms in degrees one
through five and surjectivity in degree six for the original inclusion.
The boundary's nonzero sixth homology is not assumed to vanish.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

def negativeHalfTimeHomeomorph : S.NegativeHalf ≃ₜ
    TimeCollar.NonnegativeHalf (fun p : S.Space ↦ -S.time p) where
  toFun p := ⟨p.val, neg_nonneg.mpr p.property⟩
  invFun p := ⟨p.val, neg_nonneg.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem negativeHalfTime_inclusion :
    (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)).comp
      S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun = S.negativeHalfInclusion := rfl

theorem negativeHalfInclusion_homology_factorization (k : ℕ) :
    singularHomologyMap S.negativeHalfInclusion k =
      (singularHomologyMap (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)) k).comp
        (singularHomologyMap S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun k) :=
  singularHomologyMap_comp S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun
    (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)) k



end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
