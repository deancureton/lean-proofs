module

public import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicGlobalPreimages
public import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTwelveInputs

@[expose] public section

/-!
# Exactly twelve preimages in the full parameter domain

Both angles range over `[0,π]`, and the remaining input ranges over the
actual complex unit five-sphere. Global exclusion identifies this preimage
set with the already counted midpoint fiber. This is a cardinality theorem;
local degree signs and a comparison with the marked generator remain separate.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def parameterTargetPreimage : Set (ℝ × ℝ × UnitSphere) :=
  {x | x.1 ∈ Set.Icc 0 Real.pi ∧ x.2.1 ∈ Set.Icc 0 Real.pi ∧
    firstColumnFormula x.1 x.2.1 (symmetricMap x.2.2) = targetColumn}

def midpointParameterEmbedding : UnitSphere ↪ ℝ × ℝ × UnitSphere where
  toFun z := (Real.pi / 2, Real.pi / 2, z)
  inj' := by
    intro z w h
    exact congrArg (fun x : ℝ × ℝ × UnitSphere ↦ x.2.2) h

theorem parameterTargetPreimage_eq_image :
    parameterTargetPreimage = midpointParameterEmbedding '' midpointTargetPreimage := by
  ext x
  constructor
  · rintro ⟨hs, ht, h⟩
    obtain ⟨hs', ht'⟩ := target_parameter_midpoint x.1 x.2.1 (symmetricMap x.2.2) hs ht h
    refine ⟨x.2.2, ?_, ?_⟩
    · change firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap x.2.2) = targetColumn
      simpa only [hs', ht'] using h
    · apply Prod.ext
      · exact hs'.symm
      · exact Prod.ext ht'.symm rfl
  · rintro ⟨z, hz, rfl⟩
    have hmid : Real.pi / 2 ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    exact ⟨hmid, hmid, hz⟩



end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
