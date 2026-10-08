module

public import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquaresHomotopy

@[expose] public section

/-!
# Passing between circle contractions and based loop contractions

The endpoint quotient of a closed path gives a genuine circle map. A
contraction of that circle map need not keep its marked point fixed;
the actual trajectory of that point supplies the conjugating path.
Conjugating a constant loop is nullhomotopic, so no based condition is
silently added to the unbased general-position theorem.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.OrbitPair

open TrianglePeriodFamily.BoundaryLoopSquares
open SpecialPeriods.EllipticAttachingMeridians

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]




/-- An unbased contraction of the genuine circle map contracts the original based loop. -/
theorem path_nullhomotopic_of_loopOnCircle_nullhomotopic {x c : X} (p : Path x x)
    (h : (loopOnCircle p).Homotopic (ContinuousMap.const LoopCircle c)) :
    p.Homotopic (Path.refl x) := by
  obtain ⟨H⟩ := h
  let S : LoopSquare p (Path.refl c) := {
    map := ⟨fun z => H (z.1, ((z.2 : ℝ) : LoopCircle)),
      H.continuous.comp (continuous_fst.prodMk
        ((AddCircle.continuous_mk' (1 : ℝ)).comp
          (continuous_subtype_val.comp continuous_snd)))⟩
    initial := fun t => (H.map_zero_left _).trans (loopOnCircle_unit p t)
    final := fun t => H.map_one_left _
    closed := fun t => by
      change H (t, ((0 : ℝ) : LoopCircle)) = H (t, ((1 : ℝ) : LoopCircle))
      have hc : ((1 : ℝ) : LoopCircle) = 0 := by
        simpa only [Int.cast_one] using loopCircle_int (1 : ℤ)
      rw [AddCircle.coe_zero, hc] }
  exact S.homotopic_conjugate.trans
    (((Path.Homotopic.refl S.tail).hcomp (Path.Homotopic.refl_trans S.tail.symm)).trans
      (Path.Homotopic.trans_symm S.tail))

end Wikipedia.HopfProblem.OrbitPair
