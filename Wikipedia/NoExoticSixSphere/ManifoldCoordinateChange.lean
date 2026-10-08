module

public import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

@[expose] public section

/-!
# The actual derivative formula under overlapping manifold charts

The change-of-coordinates identity holds as an equality of germs. Its
derivative therefore uses the actual source and target chart transitions,
without assuming a global equality outside the chart domains.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldCoordinates

open GLOrthonormalization

def transition {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Vector n) (Vector n) ∞ := c.symm.trans d

theorem mem_transition_source {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (x : M) (hc : x ∈ c.source) (hd : x ∈ d.source) :
    c x ∈ (transition c d).source := by
  have hleft : c.symm (c x) = x := c.left_inv hc
  change c x ∈ c.target ∧ c.symm (c x) ∈ d.source
  rw [hleft]
  exact ⟨c.map_source hc, hd⟩

theorem transition_apply {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (x : M) (hc : x ∈ c.source) : transition c d (c x) = d x := by
  have hleft : c.symm (c x) = x := c.left_inv hc
  change d (c.symm (c x)) = d x
  rw [hleft]


end NoExoticSixSphere.ManifoldCoordinates
