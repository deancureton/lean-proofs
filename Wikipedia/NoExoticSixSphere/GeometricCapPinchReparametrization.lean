module

public import Wikipedia.NoExoticSixSphere.GeometricSphereLinearReparametrization
public import Wikipedia.NoExoticSixSphere.SphereTailReflectionIsometry
public import Wikipedia.NoExoticSixSphere.SphereCapComparisonDiffeomorphism
public import Wikipedia.NoExoticSixSphere.SphereResolutionPinchScaleHomotopy

@[expose] public section

/-!
# The explicit cap-to-pinch input changes preserve geometric sphere parity

Positive scale is removed by a genuine based homotopy. At scale two the
northern change is the constructed ambient linear isometry, and the
southern change is its composition with the actual tail reflection.
The checked frame and double-point calculations prove parity preservation
for both inputs. This does not yet give the quadratic identity for their pinch.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereSumNeck

open GLOrthonormalization SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M]

theorem northPinchInput_two (F : C(Sphere 3, M)) :
    northPinchInput F 2 (by norm_num) = F.comp (sphereMap capComparisonLinearEquiv) := by
  apply ContinuousMap.ext
  intro x
  change F (capPinchComparison 2 (by norm_num) x) = F (sphereMap capComparisonLinearEquiv x)
  apply congrArg F
  apply Subtype.ext
  exact capPinchComparison_two_val x

theorem southPinchInput_two (G : C(Sphere 3, M)) :
    southPinchInput G 2 (by norm_num) =
      G.comp (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv)) := by
  apply ContinuousMap.ext
  intro x
  change G (capPinchComparison 2 (by norm_num) (tailReflection x)) =
    G (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv) x)
  apply congrArg G
  apply Subtype.ext
  rw [capPinchComparison_two_val]
  rfl

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)



end EuclideanEmbedding
end NoExoticSixSphere
