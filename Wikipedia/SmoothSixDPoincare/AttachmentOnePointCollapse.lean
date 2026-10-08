module

public import Wikipedia.SmoothSixDPoincare.DiskOnePointCollapse
public import Wikipedia.SmoothSixDPoincare.ClosedHandleCore
public import Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

@[expose] public section

/-!
# Collapse maps on actual cell and handle attachments

The old space is sent to infinity. On the full handle, retain the negative
disk coordinate and collapse its boundary. Exact attaching-face incidence
makes these maps agree and glue continuously. The same construction on a
core-cell attachment retains its original disk map.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped OnePoint

namespace Wikipedia.SmoothSixDPoincare

open MorseHandle

namespace ClosedHandleCore

variable {N P X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [TopologicalSpace X]
  (A : Set X) (h : C(UnitDisk N × UnitDisk P, X))
  (hA : IsClosed A) (hh : IsClosedEmbedding h)
  (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)

include hface in
theorem collapseMaps_agree (a : A) (z : UnitDisk N × UnitDisk P)
    (haz : oldInclusion A h a = handleInclusion A h z) :
    (∞ : OnePoint N) = DiskOnePointCollapse.collapse z.1 := by
  have heq : (a : X) = h z := congrArg Subtype.val haz
  have hz := (hface z).mp (heq ▸ a.property)
  exact (DiskOnePointCollapse.collapse_boundary z.1 hz).symm

def collapseMap : C(↥(A ∪ range h), OnePoint N) :=
  ClosedCover.mapOfClosedPieces (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A ∞) (DiskOnePointCollapse.collapse.comp ContinuousMap.fst)
    (collapseMaps_agree A h hface)

theorem collapseMap_old (a : A) :
    collapseMap A h hA hh hface (oldInclusion A h a) = ∞ :=
  ClosedCover.mapOfClosedPieces_left (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A ∞) (DiskOnePointCollapse.collapse.comp ContinuousMap.fst)
    (collapseMaps_agree A h hface) a

theorem collapseMap_handle (z : UnitDisk N × UnitDisk P) :
    collapseMap A h hA hh hface (handleInclusion A h z) = DiskOnePointCollapse.collapse z.1 :=
  ClosedCover.mapOfClosedPieces_right (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A ∞) (DiskOnePointCollapse.collapse.comp ContinuousMap.fst)
    (collapseMaps_agree A h hface) z

theorem collapseMap_infty_iff (x : ↥(A ∪ range h)) :
    collapseMap A h hA hh hface x = ∞ ↔ x.val ∈ A := by
  rcases x with ⟨x, hx | ⟨z, rfl⟩⟩
  · have heq := collapseMap_old A h hA hh hface ⟨x, hx⟩
    exact iff_of_true heq hx
  · change collapseMap A h hA hh hface (handleInclusion A h z) = ∞ ↔ h z ∈ A
    rw [collapseMap_handle, DiskOnePointCollapse.collapse_eq_infty_iff, hface]


end ClosedHandleCore

namespace EmbeddedCellAttachment

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

omit [NormedSpace ℝ N] in
theorem collapse_piece_cover : range (Subtype.val : D.old → X) ∪ range D.cell = univ := by
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using D.cover

theorem collapseMaps_agree (a : D.old) (z : UnitDisk N) (haz : (a : X) = D.cell z) :
    (∞ : OnePoint N) = DiskOnePointCollapse.collapse z :=
  (DiskOnePointCollapse.collapse_boundary z ((D.boundary z).mp (haz ▸ a.property))).symm

/-- The original old space is collapsed, and the original cell interior is left parametrized. -/
def collapseMap : C(X, OnePoint N) :=
  ClosedCover.mapOfClosedPieces Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old ∞)
    DiskOnePointCollapse.collapse D.collapseMaps_agree

theorem collapseMap_old (a : D.old) : D.collapseMap a = ∞ :=
  ClosedCover.mapOfClosedPieces_left Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old ∞)
    DiskOnePointCollapse.collapse D.collapseMaps_agree a

theorem collapseMap_cell (z : UnitDisk N) :
    D.collapseMap (D.cell z) = DiskOnePointCollapse.collapse z :=
  ClosedCover.mapOfClosedPieces_right Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old ∞)
    DiskOnePointCollapse.collapse D.collapseMaps_agree z

theorem collapseMap_infty_iff (x : X) : D.collapseMap x = ∞ ↔ x ∈ D.old := by
  have hx : x ∈ D.old ∪ range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · exact iff_of_true (D.collapseMap_old ⟨x, hx⟩) hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_infty_iff, D.boundary]

end EmbeddedCellAttachment

end Wikipedia.SmoothSixDPoincare
