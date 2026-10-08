module

public import Wikipedia.SmoothSixDPoincare.ShrunkFaceAttachmentRealization

@[expose] public section

/-!
# The shrunk whole-body change restricts to its recorded boundary map

This identity follows from the exact original exterior and new-face maps
and their exhaustive upper-level cover. It needs no extension hypothesis
and does not assert smoothness of the whole-body homeomorphism.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} (R : d.ShrunkSurgeryRealization s)

def upperBodyChange : {x : M // f x ≤ f p + d.radius ^ 2} ≃ₜ
    {x : M // f x ≤ f p + d.radius ^ 2} :=
  d.attachmentHomeomorph.symm.trans R.attachmentHomeomorph

open Classical in
theorem upperBodyChange_on_level (y : d.UpperLevel) :
    (R.upperBodyChange ⟨y.val, y.property.le⟩).val = (R.boundaryHomeomorph y).val := by
  have hy : y ∈ range d.surgery.newExterior ∪ range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hy with ⟨r, rfl⟩ | ⟨q, rfl⟩
  · have he : (⟨(d.surgery.newExterior r).val, (d.surgery.newExterior r).property.le⟩ :
        {x : M // f x ≤ f p + d.radius ^ 2}) =
        d.attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩ :=
      Subtype.ext (d.newExterior_eq r)
    change (R.attachmentHomeomorph (d.attachmentHomeomorph.symm _)).val = _
    rw [he, Homeomorph.symm_apply_apply]
    exact (R.newExterior_eq r).symm
  · have he : (⟨(d.surgery.newPiece q).val, (d.surgery.newPiece q).property.le⟩ :
        {x : M // f x ≤ f p + d.radius ^ 2}) =
        d.attachmentHomeomorph
          ⟨d.chart.normHandleMap d.radius d.radius_pos d.block
            (q.1, PuncturedHandle.sphereToBall q.2),
            Or.inr ⟨d.chart.handleBallCoordinates
              (q.1, PuncturedHandle.sphereToBall q.2), rfl⟩⟩ :=
      Subtype.ext (d.newPiece_eq q)
    change (R.attachmentHomeomorph (d.attachmentHomeomorph.symm _)).val = _
    rw [he, Homeomorph.symm_apply_apply]
    exact (R.newPiece_eq q).symm

theorem upperBodyChange_symm_on_level (y : d.UpperLevel) :
    (R.upperBodyChange.symm ⟨y.val, y.property.le⟩).val =
      (R.boundaryHomeomorph.symm y).val := by
  have he := R.upperBodyChange_on_level (R.boundaryHomeomorph.symm y)
  rw [Homeomorph.apply_symm_apply] at he
  have he' : R.upperBodyChange
      ⟨(R.boundaryHomeomorph.symm y).val, (R.boundaryHomeomorph.symm y).property.le⟩ =
        ⟨y.val, y.property.le⟩ := Subtype.ext he
  have hi := congrArg R.upperBodyChange.symm he'
  rw [Homeomorph.symm_apply_apply] at hi
  exact (congrArg Subtype.val hi).symm


variable [T2Space M] [CompactSpace M]

open Classical in
theorem faceQuotientRealization_eq_change (hf : Continuous f) :
    R.faceQuotientRealization hf = (d.faceAttachmentRealization hf).trans R.upperBodyChange := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization
