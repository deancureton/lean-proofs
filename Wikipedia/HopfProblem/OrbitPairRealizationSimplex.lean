module

public import Mathlib.AlgebraicTopology.SingularSet
public import Wikipedia.HopfProblem.FirstHurewiczSimplex
public import Wikipedia.HopfProblem.LegacySimplex

@[expose] public section

/-!
# Characteristic simplices in the actual geometric realization

The unit of the realization--singular-set adjunction supplies actual
continuous characteristic maps. Its naturality gives exact compatibility
with every simplicial operator, including the geometric face maps.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

def simplexMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) : C(Simplex m, Simplex n) :=
  ⟨stdSimplex.map f.toOrderHom, stdSimplex.continuous_map f.toOrderHom⟩

def characteristic (n : ℕ) (x : S _⦋n⦌) : C(Simplex n, SSet.toTop.obj S) :=
  (TopCat.toSSetObjEquiv (SSet.toTop.obj S) (Opposite.op ⦋n⦌)
    ((sSetTopAdj.unit.app S).app (Opposite.op ⦋n⦌) x)).comp
      ⟨legacySimplexHomeomorph, legacySimplexHomeomorph.continuous⟩

theorem characteristic_map (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (x : S _⦋n⦌) :
    characteristic S m (S.map f.op x) =
      (characteristic S n x).comp (simplexMap f) := by
  apply ContinuousMap.ext
  intro t
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app S).naturality f.op) x
  have ht := congrArg (fun y ↦ TopCat.toSSetObjEquiv (SSet.toTop.obj S)
    (Opposite.op ⦋m⦌) y (legacySimplexHomeomorph t)) h
  change _ = (TopCat.toSSetObjEquiv (SSet.toTop.obj S) (Opposite.op ⦋n⦌)
    ((sSetTopAdj.unit.app S).app (Opposite.op ⦋n⦌) x))
      (legacySimplexHomeomorph (stdSimplex.map f.toOrderHom t))
  rw [legacySimplexHomeomorph_map]
  exact ht

theorem characteristic_face (n : ℕ) (i : Fin (n + 2)) (x : S _⦋n + 1⦌) :
    characteristic S n (S.δ i x) =
      (characteristic S (n + 1) x).comp (simplexFace n i) :=
  characteristic_map S n (n + 1) (SimplexCategory.δ i) x

def vertex (x : S _⦋0⦌) : SSet.toTop.obj S :=
  characteristic S 0 x (stdSimplex.vertex (S := ℝ) (0 : Fin 1))

theorem characteristic_zero (x : S _⦋0⦌) :
    characteristic S 0 x = ContinuousMap.const (Simplex 0) (vertex S x) := by
  apply ContinuousMap.ext
  intro t
  change characteristic S 0 x t = characteristic S 0 x _
  rw [simplexZero_eq_vertex t]

theorem characteristic_constant (n : ℕ) (x : S _⦋0⦌) :
    characteristic S n (SSet.yonedaEquiv (SSet.const x : Δ[n] ⟶ S)) =
      ContinuousMap.const (Simplex n) (vertex S x) := by
  change characteristic S n (S.map (⦋n⦌.const ⦋0⦌ 0).op x) = _
  rw [characteristic_map, characteristic_zero]
  rfl

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
