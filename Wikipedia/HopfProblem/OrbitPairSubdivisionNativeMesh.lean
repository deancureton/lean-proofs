module

public import Wikipedia.HopfProblem.OrbitPairSubdivisionAffineMesh

@[expose] public section

/-!
# The mesh estimate for actual native subdivision simplices

Affine evaluation of a native barycentric characteristic simplex agrees
with affine evaluation of the uniform face means. Consequently every pair
of points in such a simplex satisfies the uniform diameter contraction
bound, for arbitrary affine vertex data in a real normed space.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz AffineCoordinates RealizationSimplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineMap {A : Type*} [Fintype A] (v : A → E) : C(stdSimplex ℝ A, E) where
  toFun := affineValue v
  continuous_toFun := by
    apply continuous_finsetSum
    intro i hi
    have h : Continuous (fun t : stdSimplex ℝ A ↦ t i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact h.smul continuous_const

theorem affineBarycentricMap_characteristic (n k : ℕ) (v : Fin (n + 1) → E)
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) (t : Simplex k) :
    affineValue v (barycentricMap n (characteristic (SimplexCategory.sd.obj ⦋n⦌) k x t)) =
      affineValue (fun j ↦ faceMean (fun i ↦ v i.down) (x.obj j).finset) t := by
  have h := AffineCoordinates.nerveInterpolation_characteristic
    (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (chainBarycentre n) k x t
  refine (congrArg (affineValue v) h).trans ?_
  refine (affineValue_weighted v (fun j ↦ chainBarycentre n (x.obj j)) t).trans ?_
  exact congrArg (fun a ↦ affineValue a t)
    (funext (fun j ↦ affineValue_chainBarycentre v (x.obj j)))


end Wikipedia.HopfProblem.OrbitPair.Subdivision
