module

public import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerCell
public import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerPieces

@[expose] public section

/-!
# Whiskering equals the specified native path concatenation

The two arms start at the actual base point. The middle follows the first
cube coordinate, and reversing the final arm closes the loop. This file
compares that literal path with the already-constructed native one-loop.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- The arm on an actual endpoint facet, with the last coordinate growing linearly. -/
def whiskerArm (F : BasedCubicalCell (n + 2) x) (ε : I)
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → I) :
    Path x (F.val (Fin.cons ε u)) where
  toFun s := F.val (Fin.cons ε (Fin.snoc (Fin.init u) (s * u (Fin.last n))))
  continuous_toFun := by
    apply F.val.continuous.comp
    apply Continuous.finCons continuous_const
    apply Continuous.finSnoc continuous_const
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul continuous_const
  source' := by
    simpa only [zero_mul] using whiskerCorner_based F ε hε (Fin.init u)
  target' := by
    simp only [one_mul, Fin.snoc_init_self]

@[simp] theorem whiskerArm_apply (F : BasedCubicalCell (n + 2) x) (ε : I)
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → I) (s : I) :
    whiskerArm F ε hε u s =
      F.val (Fin.cons ε (Fin.snoc (Fin.init u) (s * u (Fin.last n)))) := rfl

/-- The middle path traverses exactly the original first cube coordinate. -/
def whiskerAcross (F : BasedCubicalCell (n + 2) x) (u : Fin (n + 1) → I) :
    Path (F.val (Fin.cons 0 u)) (F.val (Fin.cons 1 u)) where
  toFun s := F.val (Fin.cons s u)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

@[simp] theorem whiskerAcross_apply (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) (s : I) : whiskerAcross F u s = F.val (Fin.cons s u) := rfl

/-- The clamped-coordinate form of native path concatenation. -/
theorem whiskerConcat_apply {a b c : X} (p : Path a b) (q : Path b c) (s : I) :
    (p.trans q) s =
      if (s : ℝ) ≤ 1 / 2 then p (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)))
      else q (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)) := rfl


end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
