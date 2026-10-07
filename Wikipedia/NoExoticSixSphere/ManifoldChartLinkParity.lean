module

public import Wikipedia.NoExoticSixSphere.ManifoldCoordinateChange
public import Wikipedia.NoExoticSixSphere.PartialDiffeomorphDifferential
public import Wikipedia.NoExoticSixSphere.InjectiveOperatorVaryingCoordinates

@[expose] public section

/-!
# Actual linking-sphere parity agrees in overlapping manifold charts

Both source and target chart pairs are valid throughout the supplied actual
four-ball. Their genuine transition derivatives and inverse derivatives give
continuous disk-extending coordinate changes. The actual chain rule then
identifies the two boundary operator maps, so their parities agree.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily Stiefel
open Wikipedia.HopfProblem.DegreeCollapse

def spatialInCharts {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (g : ℝ → Sphere 3 → M) (s : SourceChart) (c : TargetChart n M) (q : ℝ × Sphere 3) :
    Vector 3 →L[ℝ] Vector n :=
  fderiv ℝ (fun z ↦ c (g q.1 (s.symm z))) (s q.2)


end NoExoticSixSphere.SphereFamily
