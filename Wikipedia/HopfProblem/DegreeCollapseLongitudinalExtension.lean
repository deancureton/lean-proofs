module

public import Wikipedia.HopfProblem.DegreeCollapseLongitudinalDiffeomorph
public import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Extending a small transverse neighborhood to a global longitudinal diffeomorphism

A smooth displacement vanishing on the center axis and supported in a
compact scalar interval has zero longitudinal derivative on that axis.
Uniform compact control and a transverse cutoff preserve positive scalar
derivative. The resulting actual global diffeomorphism agrees with the
original displacement on a uniform tube and retains every zero germ.
-/

noncomputable section

open Set Filter Function Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

open Wikipedia.SmoothSixDPoincare

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- A displacement fixing the whole axis has zero scalar derivative there. -/
theorem scalar_derivative_zero_axis {v : ℝ × V → ℝ} (hv : ContDiff ℝ ∞ v)
    (haxis : ∀ s, v (s, 0) = 0) (s : ℝ) : fderiv ℝ v (s, 0) (1, 0) = 0 := by
  have he : (fun t : ℝ => v (t, 0)) = fun _ => 0 := funext haxis
  have hd := (scalar_derivative hv s 0).deriv
  rw [he, deriv_const] at hd
  exact hd.symm

omit [FiniteDimensional ℝ V] in
theorem scalar_derivative_zero_outside {v : ℝ × V → ℝ} (hv : ContDiff ℝ ∞ v)
    {K : Set ℝ} (hK : IsClosed K) (hfix : ∀ p, p.1 ∉ K → v p = 0)
    {p : ℝ × V} (hp : p.1 ∉ K) : fderiv ℝ v p (1, 0) = 0 := by
  have he : (fun t : ℝ => v (t, p.2)) =ᶠ[𝓝 p.1] fun _ => 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hp] with t ht
    exact hfix (t, p.2) ht
  rw [← (scalar_derivative hv p.1 p.2).deriv, he.deriv_eq, deriv_const]


end Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates
