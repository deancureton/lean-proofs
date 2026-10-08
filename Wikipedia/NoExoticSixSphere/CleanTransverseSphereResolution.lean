module

public import Wikipedia.NoExoticSixSphere.GloballyCleanSphereSheetChart
public import Wikipedia.NoExoticSixSphere.SphereGluedSelfTransversality
public import Wikipedia.NoExoticSixSphere.SphereResolutionPinchScaleHomotopy
public import Wikipedia.NoExoticSixSphere.SphereGluedDoublePointCount
public import Wikipedia.NoExoticSixSphere.NativeTransverseSpherePairFiniteness

@[expose] public section

/-!
# A constructed self-transverse immersed resolution at a clean common value

The globally clean chart, positive scale, smooth immersion, self-transversality,
whole-sphere pinch homotopy, and actual double-point parity formula are
constructed from the original input maps. Uniqueness of their fibers over
the chosen common value is explicit. The frame-sum formula is not asserted.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (F G : C(Sphere 3, M))


end NoExoticSixSphere.SphereSumNeck
