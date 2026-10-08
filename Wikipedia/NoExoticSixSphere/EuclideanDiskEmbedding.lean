module

public import Wikipedia.NoExoticSixSphere.CompactDiskEmbedding
public import Wikipedia.NoExoticSixSphere.StabilizedEmbedding

@[expose] public section

/-!
# Relative disk embeddings in actual Euclidean coordinates

The extra scalar and source coordinates are identified with a Euclidean
coordinate block. On the retained collar, this identification is exactly
the original zero-coordinate stabilization. A four-dimensional source needs
five added ambient coordinates.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskGraph

def scalarCoordinates : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ))).symm

def extraCoordinates (d : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin d)) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + d)) :=
  (scalarCoordinates.prodCongr
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := d)).symm

def coordinateEquiv (N d : ℕ) :
    (EuclideanSpace ℝ (Fin N) × (ℝ × EuclideanSpace ℝ (Fin d))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + (1 + d))) :=
  ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
    (extraCoordinates d)).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm

theorem coordinateEquiv_old (N d : ℕ) (y : EuclideanSpace ℝ (Fin N)) :
    coordinateEquiv N d (y, 0) = appendZeroMap N (1 + d) y := by
  change (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm
    (y, extraCoordinates d 0) =
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1 + d)).symm (y, 0)
  rw [map_zero]


end NoExoticSixSphere.DiskGraph
