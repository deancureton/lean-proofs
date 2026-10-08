module

public import Wikipedia.NoExoticSixSphere.CollaredDiskFrameExtension
public import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
public import Wikipedia.NoExoticSixSphere.SphereAffineFrameDerivative
public import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity

@[expose] public section

/-!
# An actual framed immersed boundary disk forces zero geometric parity

The disk operator is the derivative of the supplied smooth map into the
original ambient space times a height line. The supplied frame is defined
over that disk, is transverse to its actual derivative, and restricts
exactly to the prescribed normal frame. Boundary equality gives the
tangential derivative identity by the native chain rule. Positive radial
height and the checked collar homotopy then extend the original twisted
sphere obstruction, proving zero sphere parity and quadratic value.

Existence of such a disk and frame is not asserted for arbitrary classes.
In particular this is not yet boundary-kernel vanishing or Arf detection.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization SphereThreeTangentFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N : ℕ} (F : Vector 4 → Vector N × ℝ)
  (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)

def diskDifferential : C(Disk (E := Vector 4), Vector 4 →L[ℝ] (Vector N × ℝ)) where
  toFun x := fderiv ℝ F x.val
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hF x.val x.property).continuousAt_fderiv (by simp)).comp
      continuous_subtype_val.continuousAt

def radialDerivativeMap : C(Sphere 3, Vector N × ℝ) where
  toFun s := fderiv ℝ F s.val s.val
  continuous_toFun := ((diskDifferential F hF).continuous.comp
    boundaryToDisk.continuous).clm_apply continuous_subtype_val

include hF in
theorem boundary_tangent_derivative (g : Sphere 3 → Vector N)
    (hg : ContMDiff (𝓡 3) (𝓡 N) ∞ g) (hb : ∀ s, F s.val = (g s, 0))
    (s : Sphere 3) (u : Vector 3) :
    fderiv ℝ F s.val (operator s.val u) = (framedDerivative g s u, 0) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere
  have h₀ := framedDerivative_outer_comp_at F (Subtype.val : Sphere 3 → Vector 4) s
    ((hF s.val (Metric.sphere_subset_closedBall s.property)).differentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))
  rw [framedDerivative_coe] at h₀
  have he : F ∘ (Subtype.val : Sphere 3 → Vector 4) =
      (ContinuousLinearMap.inl ℝ (Vector N) ℝ) ∘ g := funext hb
  rw [he] at h₀
  have h₁ := framedDerivative_outer_comp_at (ContinuousLinearMap.inl ℝ (Vector N) ℝ)
    g s (ContinuousLinearMap.inl ℝ (Vector N) ℝ).differentiableAt
    (hg.mdifferentiableAt (by simp))
  rw [ContinuousLinearMap.fderiv] at h₁
  exact congrArg (fun L : Vector 3 →L[ℝ] (Vector N × ℝ) ↦ L u) (h₀.symm.trans h₁)

end NoExoticSixSphere.CollaredDiskFrame

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereThreeTangentFrame CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)


end NoExoticSixSphere.EuclideanEmbedding
