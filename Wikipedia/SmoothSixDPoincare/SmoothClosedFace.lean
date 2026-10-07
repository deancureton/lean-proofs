module

public import Wikipedia.SmoothSixDPoincare.MorseHandleModel
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Diffeomorph

@[expose] public section

/-!
# A closed embedded face with its actual open smooth chart

The chart extends every point of the closed disk, including its boundary.
Postcomposition retains all coordinates and the closed embedding, so the
same data can be passed through consecutive native regular bands.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E H F H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']

structure SmoothClosedFace (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
    (X N Y : Type*) [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y] [ChartedSpace H' Y] where
  map : C(X × MorseHandle.UnitDisk N, Y)
  closedEmbedding : IsClosedEmbedding map
  chart : PartialDiffeomorph (I.prod 𝓘(ℝ, N)) J (X × N) Y ∞
  source : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ chart.source
  point : ∀ x (w : MorseHandle.UnitDisk N), chart (x, w.val) = map (x, w)

namespace SmoothClosedFace

variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {X N Y : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y] [ChartedSpace H' Y]
  (A : SmoothClosedFace I J X N Y)
  {G K Z : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K]
  {L : ModelWithCorners ℝ G K} [TopologicalSpace Z] [ChartedSpace K Z]

theorem smoothClosedFace_partialDiffeomorph_source (b : Diffeomorph J L Y Z ∞) :
    b.toPartialDiffeomorph.source = univ := by rfl

theorem smoothClosedFace_partialDiffeomorph_apply (b : Diffeomorph J L Y Z ∞) (y : Y) :
    b.toPartialDiffeomorph y = b y := by rfl

def postcompose (b : Diffeomorph J L Y Z ∞) : SmoothClosedFace I L X N Z where
  map := ⟨fun z => b (A.map z), b.toHomeomorph.continuous.comp A.map.continuous⟩
  closedEmbedding := b.toHomeomorph.isClosedEmbedding.comp A.closedEmbedding
  chart := A.chart.trans b.toPartialDiffeomorph
  source := fun z hz => ⟨A.source hz, by
    change A.chart z ∈ b.toPartialDiffeomorph.source
    rw [smoothClosedFace_partialDiffeomorph_source]
    trivial⟩
  point := fun x w => by
    change b.toPartialDiffeomorph (A.chart (x, w.val)) = b (A.map (x, w))
    rw [smoothClosedFace_partialDiffeomorph_apply, A.point]

theorem postcompose_map (b : Diffeomorph J L Y Z ∞) (z : X × MorseHandle.UnitDisk N) :
    (A.postcompose b).map z = b (A.map z) := rfl

end SmoothClosedFace

end Wikipedia.SmoothSixDPoincare
