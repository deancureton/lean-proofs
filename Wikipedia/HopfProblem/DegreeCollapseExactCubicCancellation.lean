module

public import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationSupport

@[expose] public section

/-!
# Supported cancellation starting from the exact cubic normal form

The initial function is the uncut cubic `C_{-a²}`. Only the change to the
function is cut off. Compact control of the transition and the exact two
initial critical points prove that the final function is regular everywhere.
This removes the cutoff from the normal-form placement required on a manifold.
-/

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {m : ℕ} (σ : Fin m → ℝ)

def cancelled (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ (-t) p + 2 * t * φ p * p.1

theorem contDiff_cancelled_family {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Function.uncurry (cancelled σ φ)) := by
  exact ((contDiff_cubic_family σ).comp (contDiff_fst.neg.prodMk contDiff_snd)).add
    (((contDiff_const.mul contDiff_fst).mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

theorem cancelled_zero (φ : Model m → ℝ) : cancelled σ φ 0 = cubic σ 0 := by
  funext p
  simp [cancelled]

theorem cancelled_germ_plateau {φ : Model m → ℝ} {U : Set (Model m)}
    (hU : IsOpen U) (hφU : EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [cancelled, cubic, hφU hq]
  ring

theorem cancelled_eq_off_support (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : cancelled σ φ t p = cubic σ (-t) p := by
  simp [cancelled, image_eq_zero_of_notMem_tsupport hp]

theorem cancelled_germ_off_support (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ (-t) := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact cancelled_eq_off_support σ φ t hq


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
