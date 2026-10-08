module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Literal facets of native cubes

A facet inserts one fixed coordinate, leaving all remaining coordinates
in their original natural order. The boundary lemmas retain those exact
coordinate witnesses.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

/-- The actual ordered facet map of a native cube. -/
def cubeFacet (n : ℕ) (i : Fin (n + 1)) (ε : I) :
    C(Fin n → I, Fin (n + 1) → I) where
  toFun u := Fin.insertNth (α := fun _ => I) i ε u
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous fun _ : Fin n → I => ε)
    · simpa only [Fin.insertNth_apply_succAbove] using
        (continuous_apply k : Continuous fun u : Fin n → I => u k)

@[simp] theorem cubeFacet_apply_self (n : ℕ) (i : Fin (n + 1)) (ε : I)
    (u : Fin n → I) : cubeFacet n i ε u i = ε :=
  Fin.insertNth_apply_same (α := fun _ => I) i ε u

@[simp] theorem cubeFacet_apply_succAbove (n : ℕ) (i : Fin (n + 1)) (ε : I)
    (u : Fin n → I) (j : Fin n) : cubeFacet n i ε u (i.succAbove j) = u j :=
  Fin.insertNth_apply_succAbove (α := fun _ => I) i ε u j

theorem cubeFacet_removeNth (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → I) :
    cubeFacet n i (u i) (Fin.removeNth i u) = u :=
  Fin.insertNth_self_removeNth i u


/-- An endpoint among the remaining coordinates is still an actual
boundary coordinate after insertion. -/
theorem cubeFacet_boundary_of_endpoint (n : ℕ) (i : Fin (n + 1)) (ε : I)
    (u : Fin n → I) (j : Fin n) (hj : u j = 0 ∨ u j = 1) :
    cubeFacet n i ε u ∈ Cube.boundary (Fin (n + 1)) := by
  refine ⟨i.succAbove j, ?_⟩
  simpa only [cubeFacet_apply_succAbove] using hj



/-- Inserting an endpoint into a boundary point exhibits two distinct
endpoint coordinates of the larger cube. -/
theorem cubeFacet_codimTwo (n : ℕ) (i : Fin (n + 1)) (ε : I)
    (hε : ε = 0 ∨ ε = 1) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
    ∃ a b : Fin (n + 1), a ≠ b ∧
      (cubeFacet n i ε u a = 0 ∨ cubeFacet n i ε u a = 1) ∧
      (cubeFacet n i ε u b = 0 ∨ cubeFacet n i ε u b = 1) := by
  obtain ⟨j, hj⟩ := hu
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, ?_, ?_⟩
  · simpa only [cubeFacet_apply_self] using hε
  · simpa only [cubeFacet_apply_succAbove] using hj

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
