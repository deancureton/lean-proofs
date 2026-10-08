module

public import Wikipedia.NoExoticSixSphere.NormalDiskCombinedOperator
public import Wikipedia.NoExoticSixSphere.ImmersedDiskNormalObstruction

@[expose] public section

/-!
# Combined operators use the actual derivative of the immersed disk

The exact normal-disk extension criterion applies to the genuine differential
of the smooth disk. A homotopy of the combined boundary operators therefore
preserves its original normal-disk parity.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.ImmersedDisk

open GLOrthonormalization DiskBoundary

variable (r : ℕ) (f : Vector 4 → Vector (r + 9))
  (hf : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
  (hi : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ f x))
  (a : C(Sphere 3, Space (r + 9) (r + 2)))
  (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ)

def combinedMap : C(Sphere 3, Monomorphism.Space (r + 9) ((r + 2) + 4)) :=
  DiskNormal.combinedMap r (differential r f hf) (differential_injective r f hf hi) a ha

theorem combinedMap_value (s : Sphere 3) :
    (combinedMap r f hf hi a ha s).val = OperatorSum.operator (a s).val (fderiv ℝ f s.val) := rfl

theorem parity_zero_iff_combined_extension :
    parity r f hf hi a ha = 0 ↔ Extends (combinedMap r f hf hi a ha) :=
  DiskNormal.parity_zero_iff_combined_extension r (differential r f hf)
    (differential_injective r f hf hi) a ha


end NoExoticSixSphere.Stiefel.ImmersedDisk
