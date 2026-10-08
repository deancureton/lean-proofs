module

public import Wikipedia.HopfProblem.OrbitPairSphereProjectedExponential

@[expose] public section

/-!
# Smooth short sphere segments to all sufficiently nearby endpoints

The constructed partial inverse supplies tangent vectors for every unit
endpoint in an actual open neighborhood of the basepoint. Projection
injectivity on the positive hemisphere proves exact endpoint recovery.
The logarithm and the resulting time-rescaled segments depend smoothly on
the endpoint, including the diagonal, where the segment is exactly constant.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential.LocalLogData

open NoExoticSixSphere GLOrthonormalization

variable {n : ℕ} {x : Vector n} {ε : ℝ} (d : LocalLogData x ε)

def domain : Set (Vector n) :=
  {y | projection x y ∈ d.chart.target ∧ 0 < inner ℝ x y}

theorem isOpen_domain : IsOpen d.domain := by
  have hc : Continuous (fun y : Vector n => inner ℝ x y) := continuous_const.inner continuous_id
  exact (d.chart.open_target.preimage (projection x).continuous).inter
    (isOpen_lt (continuous_const (y := (0 : ℝ))) hc)

theorem base_mem_domain (hx : ‖x‖ = 1) : x ∈ d.domain := by
  have ht := d.chart.map_source' d.zero_source
  have he : d.chart 0 = 0 := by rw [d.formula, projectedEndpoint_zero]
  rw [he] at ht
  exact ⟨by simpa only [projection_base] using ht,
    by rw [real_inner_self_eq_norm_sq, hx, one_pow]; exact zero_lt_one⟩

def log (y : Vector n) : Tangent x := d.chart.symm (projection x y)

theorem contDiffOn_log : ContDiffOn ℝ ∞ d.log d.domain :=
  d.chart.contMDiffOn_invFun.contDiffOn.comp (projection x).contDiff.contDiffOn
    (fun _ hy => hy.1)

theorem log_mem_source {y : Vector n} (hy : y ∈ d.domain) : d.log y ∈ d.chart.source :=
  d.chart.map_target' hy.1

theorem norm_log_lt {y : Vector n} (hy : y ∈ d.domain) : ‖d.log y‖ < ε :=
  d.source_small _ (d.log_mem_source hy)

theorem projectedEndpoint_log {y : Vector n} (hy : y ∈ d.domain) :
    projectedEndpoint x (d.log y) = projection x y := by
  have h := d.chart.right_inv' hy.1
  change d.chart (d.log y) = projection x y at h
  rwa [d.formula] at h

theorem curve_log (hx : ‖x‖ = 1) {y : Vector n} (hunit : ‖y‖ = 1)
    (hy : y ∈ d.domain) : curve x (d.log y) 1 = y :=
  projection_injective_positive hx (norm_curve hx _ _) hunit
    (d.source_positive _ (d.log_mem_source hy)).le hy.2.le (d.projectedEndpoint_log hy)

theorem log_curve {v : Tangent x} (hv : v ∈ d.chart.source) : d.log (curve x v 1) = v := by
  have he : d.chart v = projection x (curve x v 1) := congrFun d.formula v
  change d.chart.symm (projection x (curve x v 1)) = v
  rw [← he]
  exact d.chart.left_inv' hv

theorem log_base : d.log x = 0 := by
  have h := d.log_curve d.zero_source
  rwa [curve_zero_velocity] at h

def segmentTo (y : Vector n) (l u t : ℝ) : Vector n := segment x (d.log y) l u t


theorem segmentTo_start (y : Vector n) (l u : ℝ) : d.segmentTo y l u l = x :=
  segment_start x _ l u

theorem segmentTo_end (hx : ‖x‖ = 1) {y : Vector n} (hunit : ‖y‖ = 1)
    (hy : y ∈ d.domain) {l u : ℝ} (hlu : l ≠ u) : d.segmentTo y l u u = y := by
  rw [segmentTo, segment_end x _ hlu, d.curve_log hx hunit hy]

theorem segmentTo_base (l u t : ℝ) : d.segmentTo x l u t = x := by
  rw [segmentTo, d.log_base, segment, curve_zero_velocity]

theorem norm_segmentTo (hx : ‖x‖ = 1) (y : Vector n) (l u t : ℝ) :
    ‖d.segmentTo y l u t‖ = 1 := norm_segment hx _ l u t


theorem segmentTo_energy_le (hx : ‖x‖ = 1) (hε : ε ≤ Real.pi / 2)
    {γ : ℝ → Vector n} (hγ : ContDiff ℝ ∞ γ) (hunit : ∀ t, ‖γ t‖ = 1)
    {l u : ℝ} (hlu : l < u) (hl : γ l = x) (hu : γ u ∈ d.domain) :
    SpherePathEnergy.energy (d.segmentTo (γ u) l u) l u ≤ SpherePathEnergy.energy γ l u :=
  short_segment_energy_le hγ hunit hx (d.log (γ u)) ((d.norm_log_lt hu).le.trans hε)
    hlu hl (d.curve_log hx (hunit u) hu).symm

end Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential.LocalLogData
