module

public import Wikipedia.NoExoticSixSphere.PartialFrames
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

/-!
# Ordinary derivative comparison from an exact closed-disk collar formula

The closed ball has unique within-derivatives, also at its boundary. Two
differentiable product maps agreeing on its outer collar therefore have the
same ordinary derivative there. No equality on an open ambient collar is
assumed or inferred from equality on the closed disk.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace NoExoticSixSphere

open GLOrthonormalization


theorem uniqueDiffOn_closedDiskProduct {d : ℕ} :
    UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1 ×ˢ (univ : Set (Vector d))) := by
  have hD : UniqueDiffOn ℝ (closedBall (0 : Vector 4) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : Vector 4) 1)
      ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))⟩
  exact hD.prod uniqueDiffOn_univ

theorem fderiv_eq_of_closedDisk_collar {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H G : Vector 4 × Vector d → F) (r : ℝ)
    (heq : ∀ y ∈ closedBall (0 : Vector 4) 1, r ≤ ‖y‖ → ∀ w : Vector d,
      H (y, w) = G (y, w))
    {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : r < ‖x‖) (v : Vector d)
    (hH : DifferentiableAt ℝ H (x, v)) (hG : DifferentiableAt ℝ G (x, v)) :
    fderiv ℝ H (x, v) = fderiv ℝ G (x, v) := by
  let S := closedBall (0 : Vector 4) 1 ×ˢ (univ : Set (Vector d))
  have hxS : (x, v) ∈ S := ⟨hx, mem_univ v⟩
  have hs : UniqueDiffWithinAt ℝ S (x, v) := uniqueDiffOn_closedDiskProduct _ hxS
  have hn : {p : Vector 4 × Vector d | r < ‖p.1‖} ∈ 𝓝 (x, v) :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).mem_nhds hxr
  have he : H =ᶠ[𝓝[S] (x, v)] G := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with p hp hpn
    exact heq p.1 hp.1 hpn.le p.2
  have hd : fderivWithin ℝ H S (x, v) = fderivWithin ℝ G S (x, v) :=
    he.fderivWithin_eq_of_mem hxS
  rw [fderivWithin_eq_fderiv hs hH, fderivWithin_eq_fderiv hs hG] at hd
  exact hd

end NoExoticSixSphere
