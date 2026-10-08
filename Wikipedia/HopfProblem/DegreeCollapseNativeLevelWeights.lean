module

public import Wikipedia.HopfProblem.DegreeCollapseNativeFlowCylinder
public import Wikipedia.HopfProblem.DegreeCollapseConvexHeightProfiles

@[expose] public section

/-!
# Smooth stationary weights from the actual native cylinder

Pulling a smooth function on the original regular level through the first
coordinate of the native inverse cylinder constructs an actual smooth
weight on the entire level basin. The complete flow law proves exact
stationarity at every real time, rather than assuming label invariance.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {Z H N E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
  [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def nativeCylinderWeight
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (θ : N → ℝ) (x : M) : ℝ := θ (A.symm x).1

theorem contMDiffOn_nativeCylinderWeight
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    {θ : N → ℝ} (hθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (nativeCylinderWeight A θ) A.target :=
  hθ.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn A.contMDiffOn_invFun)

theorem nativeCylinderWeight_mem_Icc
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    {θ : N → ℝ} (hθ : ∀ z, θ z ∈ Icc (0 : ℝ) 1) (x : M) :
    nativeCylinderWeight A θ x ∈ Icc (0 : ℝ) 1 := hθ _

theorem native_cylinder_flow_coordinates
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1)) {x : M} (hx : x ∈ A.target) (t : ℝ) :
    A.symm (F t x) = ((A.symm x).1, t + (A.symm x).2) := by
  have hright : A (A.symm x) = x := A.right_inv' hx
  have hexpr : F t x = A ((A.symm x).1, t + (A.symm x).2) := by
    calc
      F t x = F t (A (A.symm x)) := congrArg (F t) hright.symm
      _ = F (t + (A.symm x).2) (ι (A.symm x).1) := by
        rw [hformula, ← F.map_add]
      _ = A ((A.symm x).1, t + (A.symm x).2) :=
        (hformula ((A.symm x).1, t + (A.symm x).2)).symm
  rw [hexpr]
  exact A.left_inv' (by rw [hsource]; trivial)

theorem nativeCylinderWeight_flow
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1)) (θ : N → ℝ)
    {x : M} (hx : x ∈ A.target) (t : ℝ) :
    nativeCylinderWeight A θ (F t x) = nativeCylinderWeight A θ x := by
  unfold nativeCylinderWeight
  rw [native_cylinder_flow_coordinates A hsource F ι hformula hx t]



end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
