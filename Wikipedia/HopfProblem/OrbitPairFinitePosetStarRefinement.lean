module

public import Wikipedia.HopfProblem.OrbitPairFinitePosetCoordinateMesh
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

/-!
# Subdivision vertex stars refine every open cover

A native closed vertex star is the union of characteristic simplices
containing that vertex. Its points lie within one mesh bound of its
vertex, in the faithful coordinate embedding. Compactness and the
Lebesgue-number lemma now give open-cover refinement at all sufficiently
large subdivision stages.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder Topology Filter Metric

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex Subdivision

theorem characteristic_vertex (P : Type u) [PartialOrder P] [Fintype P] (k : ℕ)
    (x : (nerve P) _⦋k⦌) (i : Fin (k + 1)) :
    characteristic (nerve P) k x (stdSimplex.vertex i) =
      vertex (nerve P) (ComposableArrows.mk₀ (x.obj i)) := by
  classical
  apply coordinates_injective P
  exact (coordinates_characteristic P k x (stdSimplex.vertex i)).trans
    ((stdSimplex.map_vertex x.obj i).trans (coordinates_vertex P (x.obj i)).symm)

def nativeClosedStar (P : Type u) [PartialOrder P] (p : P) : Set (SSet.toTop.obj (nerve P)) :=
  {z | ∃ k : ℕ, ∃ x : (nerve P) _⦋k⦌, ∃ t : Simplex k, ∃ i : Fin (k + 1),
    x.obj i = p ∧ characteristic (nerve P) k x t = z}

theorem coordinate_dist_of_mem_closedStar (P : PartOrd.{u}) [Fintype P] (r : ℕ)
    (p : (iteratedChains r).obj P) (z : SSet.toTop.obj (nerve ((iteratedChains r).obj P)))
    (hz : z ∈ nativeClosedStar ((iteratedChains r).obj P) p) :
    dist (iteratedCoordinateMap P r z)
      (iteratedCoordinateMap P r
        (vertex (nerve ((iteratedChains r).obj P)) (ComposableArrows.mk₀ p))) ≤
          ((Fintype.card P : ℝ) / (Fintype.card P + 1)) ^ r := by
  classical
  letI : Fintype ((iteratedChains r).obj P) := Fintype.ofFinite _
  obtain ⟨k, x, t, i, hi, rfl⟩ := hz
  have he := (characteristic_vertex ((iteratedChains r).obj P) k x i).trans
    (congrArg (fun q ↦ vertex (nerve ((iteratedChains r).obj P)) (ComposableArrows.mk₀ q)) hi)
  have hd := congrArg (fun w ↦ dist (iteratedCoordinateMap P r
    (characteristic (nerve ((iteratedChains r).obj P)) k x t))
      (iteratedCoordinateMap P r w)) he
  exact hd.symm.le.trans (iteratedCoordinateMap_mesh P r k x t (stdSimplex.vertex i))


end Wikipedia.HopfProblem.OrbitPair.FinitePoset
