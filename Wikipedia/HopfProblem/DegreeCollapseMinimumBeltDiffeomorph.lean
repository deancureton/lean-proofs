module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseIndexZeroBeltRegularity
public import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryBasins
public import Wikipedia.HopfProblem.DegreeCollapseNativeNoReturn
public import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
public import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
public import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints

@[expose] public section

/-!
# The actual first upper level is smoothly parametrized by the native belt

Every forward endpoint from the first upper level is the first critical
point, by the chronological ordering and its isolated window. The full
belt-basin theorem therefore makes the actual belt map surjective. Its
derivative is invertible at index zero, so it is a native diffeomorphism.
In dimension six this smoothly identifies the entire level with standard
S⁵, not just with a topological sphere or an abstract model level.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.belt_surjective_at_first
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (h : 0 < S.toSurgeryWindows.count) :
    Surjective (S.data (S.toSurgeryWindows.first h)).surgery.beltSphere := by
  let p := S.toSurgeryWindows.first h
  intro x
  obtain ⟨r, hr, q, hq, -, hlim, hheight⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x.val
  have hqlo : S.toSurgeryWindows.lower p ≤ f q :=
    (S.toSurgeryWindows.lower_lt_value p).le.trans
      (S.toSurgeryWindows.value_first_le h ⟨q, hq⟩)
  have hqhi : f q ≤ S.toSurgeryWindows.upper p := by
    have hh := (hheight ((S.data p).upper_regular x.val x.property)).1
    rw [x.property] at hh
    exact hh.le
  have hqp : q = p.val := S.isolated p q hq ⟨hqlo, hqhi⟩
  rw [hqp] at hlim
  exact (S.belt_basin_iff hf p x).mp hlim

def native_index_zero_beltDiffeomorph {p : M} (d : MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : Module.finrank ℝ d.chart.NegativeCoordinates = 0) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hsurj : Surjective d.surgery.beltSphere) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  have hlocal : IsLocalDiffeomorph (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞
      d.surgery.beltSphere := by
    intro v
    apply isLocalDiffeomorphAt_between_manifolds isOpen_univ (mem_univ v)
      (d.belt_smooth hf n).contMDiffOn
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
    let L := (LinearEquiv.ofBijective A.toLinearMap
      ⟨d.belt_derivative_injective hf n v,
        index_zero_belt_derivative_surjective d hf hzero n v⟩).toContinuousLinearEquiv
    exact ⟨L, by ext w; rfl⟩
  exact hlocal.diffeomorphOfBijective ⟨d.belt_isClosedEmbedding.injective, hsurj⟩


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
