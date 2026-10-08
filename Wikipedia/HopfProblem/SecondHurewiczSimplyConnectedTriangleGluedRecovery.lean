module

public import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleFaces
public import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionRecovery

@[expose] public section

/-!
# Native class recovery after coherent triangle normalization

The terminal glued square has exactly the original lower-positive and
upper-negative based triangles. The explicit diagonal-subdivision homotopy
therefore identifies its native second homotopy class with their difference.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact native second-homotopy class of the glued based triangles. -/
theorem basedTrianglesLoop_class (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : I, basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → I) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd



end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
