module

public import Wikipedia.NoExoticSixSphere.FamilyFlatteningRegular
public import Wikipedia.NoExoticSixSphere.FlatSmoothGerm

@[expose] public section

/-!
# A nondegenerate flat germ for an actual family

An invertible leading block and a regular zero of the original Schur
residual produce genuine time-preserving source coordinates and a smooth
representative of the flattened germ with nondegenerate vertical derivative.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne SymmetricDifference

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : T → E × ℝ → E × F}

def Data.forward (d : Data f) (q : E × (T × ℝ)) : (T × E) × ℝ :=
  flatOrder.symm (d.coord q)

omit [FiniteDimensional ℝ T] in
theorem Data.forward_mem_target (d : Data f) {q : E × (T × ℝ)}
    (hq : q ∈ d.coord.source) : d.forward q ∈ d.target := by
  change flatOrder (flatOrder.symm (d.coord q)) ∈ d.coord.target
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact d.coord.toOpenPartialHomeomorph.map_source hq

omit [FiniteDimensional ℝ T] in
theorem Data.inverse_forward (d : Data f) {q : E × (T × ℝ)}
    (hq : q ∈ d.coord.source) : d.inverse (d.forward q) = q := by
  change d.coord.symm (flatOrder (flatOrder.symm (d.coord q))) = q
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact d.coord.toOpenPartialHomeomorph.left_inv hq

omit [FiniteDimensional ℝ T] in
theorem Data.forward_apply (d : Data f) (q : E × (T × ℝ)) :
    d.forward q = ((q.2.1, head f q), q.2.2) := by
  unfold Data.forward
  rw [d.coord_apply]
  rfl


end NoExoticSixSphere.FamilyFlattening
