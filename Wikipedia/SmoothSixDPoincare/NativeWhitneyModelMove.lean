module

public import Wikipedia.SmoothSixDPoincare.WhitneyModelCancellation
public import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
public import Wikipedia.SmoothSixDPoincare.WhitneyBigon

@[expose] public section

/-!
# Supported smooth cancellation in a supplied Whitney model chart

The actual six-dimensional model motion extends to a smooth family of global
diffeomorphisms of the native manifold, fixed outside the chart. Its endpoint
separates the two actual modeled sheet images. The model chart and support
containment are explicit hypotheses of this intermediate result: constructing
such a chart from a native Whitney disk and the intersecting handles remains
a separate obligation.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞)

def nativeFirstSheet : Set M := Φ '' (range firstSheet ∩ Φ.source)

def nativeSecondSheet (h : ℝ) : Set M := Φ '' (range (secondSheet h) ∩ Φ.source)

omit [T2Space M] in
/-- The support-containment hypothesis includes the full joining segment, hence both corners. -/
theorem joiningSegment_mem_source (hK : tsupport cutoff ⊆ Φ.source)
    {s : ℝ} (hs : |s| ≤ 1) : firstSheet (s, 0) ∈ Φ.source := by
  apply hK
  apply subset_tsupport cutoff
  change cutoff (firstSheet (s, 0)) ≠ 0
  rw [cutoff_firstSheet_zero hs]
  norm_num

omit [T2Space M] in
/-- The support condition also contains the full small cornered bigon. -/
theorem bigon_mem_source (hK : tsupport cutoff ⊆ Φ.source)
    {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    bigonEmbedding p ∈ Φ.source := by
  apply hK
  apply subset_tsupport cutoff
  change cutoff (bigonEmbedding p) ≠ 0
  rw [cutoff_bigonEmbedding hh hsmall hp]
  norm_num

omit [T2Space M] in
/-- Inside the genuine chart, the original sheets have exactly the model intersections. -/
theorem native_first_eq_second_iff {h : ℝ} (hh : 0 < h) (p q : Sheet)
    (hp : firstSheet p ∈ Φ.source) (hq : secondSheet h q ∈ Φ.source) :
    Φ (firstSheet p) = Φ (secondSheet h q) ↔
      p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  constructor
  · intro heq
    exact (firstSheet_eq_secondSheet_iff hh p q).mp (Φ.toPartialEquiv.injOn hp hq heq)
  · intro heq
    exact congrArg Φ ((firstSheet_eq_secondSheet_iff hh p q).mpr heq)


end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
