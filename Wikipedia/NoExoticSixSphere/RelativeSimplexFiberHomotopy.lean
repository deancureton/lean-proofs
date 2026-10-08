module

public import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberPairHomotopy

@[expose] public section

/-!
# Boundary-fixed relative simplex homotopies preserve the actual fiber class

Apply the original homotopy to each barycentric cone path. The first
vertex stays fixed, so these are paths in the same inclusion fiber.
For a boundary point the whole cone lies in the simplex boundary, and
the lifted homotopy is literally stationary. The genuine relative prism
then proves equality of the resulting fiber-homology classes.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.RelativeSimplexFiberClass

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def liftedHomotopy (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 1))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (H : smp₀.val.HomotopyRel smp₁.val (simplexBoundary (n + 1))) :
    (liftedSimplex U a n smp₀ hv₀).HomotopyRel
      (liftedSimplex U a n smp₁ hv₁) (simplexBoundary n) := by
  have hU (r : I) (s : Simplex (n + 1)) (hs : s ∈ simplexBoundary (n + 1)) :
      H (r, s) ∈ U := by
    rw [H.eq_fst r hs]
    exact smp₀.property s hs
  have hv (r : I) : H (r, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val :=
    (H.eq_fst r (SimplexVertexCone.firstVertex_mem_boundary n)).trans hv₀
  refine {
    toHomotopy := liftedPairHomotopy U a n smp₀ smp₁ hv₀ hv₁ H.toHomotopy hU hv
    prop' := ?_ }
  intro r s hs
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (H.eq_fst r (simplexFace_mem_boundary n 0 s))
  · ext t
    exact H.eq_fst r (SimplexVertexCone.cone_boundary n t s hs)


end NoExoticSixSphere.RelativeSimplexFiberClass
