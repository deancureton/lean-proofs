module

public import Wikipedia.HopfProblem.FirstHurewiczSimplex

@[expose] public section

/-!
# Face identities for actual singular tetrahedra

The coface relation is transported through the actual topological simplex
functor. Its six low-dimensional instances identify each edge in the two
faces of a tetrahedron that contain it.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle

open CategoryTheory Simplicial FirstHurewicz

/-- The genuine topological face maps satisfy the coface composition identity. -/
theorem simplexFace_comp {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (simplexFace (n + 1) j.succ).comp (simplexFace n i) =
      (simplexFace (n + 1) i.castSucc).comp (simplexFace n j) := by
  apply ContinuousMap.ext
  intro x
  change stdSimplex.map (SimplexCategory.δ j.succ).toOrderHom
      (stdSimplex.map (SimplexCategory.δ i).toOrderHom x) =
    stdSimplex.map (SimplexCategory.δ i.castSucc).toOrderHom
      (stdSimplex.map (SimplexCategory.δ j).toOrderHom x)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hf := congrArg (fun f : ⦋n⦌ ⟶ ⦋n + 2⦌ => stdSimplex.map f.toOrderHom x)
    (SimplexCategory.δ_comp_δ h)
  simpa only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe] using hf

variable {X : Type*} [TopologicalSpace X]

/-- The corresponding faces of every actual continuous singular simplex agree. -/
theorem singularSimplex_face_face {n : ℕ} (σ : C(Simplex (n + 2), X))
    {i j : Fin (n + 2)} (h : i ≤ j) :
    (σ.comp (simplexFace (n + 1) j.succ)).comp (simplexFace n i) =
      (σ.comp (simplexFace (n + 1) i.castSucc)).comp (simplexFace n j) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(Simplex n, Simplex (n + 2)) => σ.comp f) (simplexFace_comp h)

/-- The edge `01`, viewed in faces `2` and `3`. -/
theorem tetrahedron_edge01 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 2)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 2) :=
  (singularSimplex_face_face σ (i := 2) (j := 2) (by decide)).symm

/-- The edge `02`, viewed in faces `1` and `3`. -/
theorem tetrahedron_edge02 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 1)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 1) :=
  (singularSimplex_face_face σ (i := 1) (j := 2) (by decide)).symm

/-- The edge `03`, viewed in faces `1` and `2`. -/
theorem tetrahedron_edge03 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 1)).comp (simplexFace 1 1) =
      (σ.comp (simplexFace 2 2)).comp (simplexFace 1 1) :=
  (singularSimplex_face_face σ (i := 1) (j := 1) (by decide)).symm

/-- The edge `12`, viewed in faces `0` and `3`. -/
theorem tetrahedron_edge12 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 0)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 0) :=
  (singularSimplex_face_face σ (i := 0) (j := 2) (by decide)).symm

/-- The edge `13`, viewed in faces `2` and `0`. -/
theorem tetrahedron_edge13 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 2)).comp (simplexFace 1 0) =
      (σ.comp (simplexFace 2 0)).comp (simplexFace 1 1) :=
  singularSimplex_face_face σ (i := 0) (j := 1) (by decide)

/-- The edge `23`, viewed in faces `0` and `1`. -/
theorem tetrahedron_edge23 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 0)).comp (simplexFace 1 0) =
      (σ.comp (simplexFace 2 1)).comp (simplexFace 1 0) :=
  (singularSimplex_face_face σ (i := 0) (j := 0) (by decide)).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle
