module

public import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexCoordinates
public import Wikipedia.HomotopyGroupsOfSpheres.RealHessianCalculus

@[expose] public section

/-!
# Actual second variations and the constrained polygon Hessian

At a critical point, the second derivative along a reversible vertex curve
is the Hessian evaluated on its actual coordinate velocity. A linear family
of strictly negative variations therefore gives a negative subspace of the
same dimension; strict negativity itself proves injectivity after passage
to coordinates.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

def localHessian (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) : RealHessianForm (Model N m) :=
  realHessian (E := Model N m) (localEnergy a b τ v) 0

theorem secondDerivative_eq_localHessian (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) (W : ReversibleModel v) :
    deriv (deriv (fun s ↦ energy a b τ (vertexVariation v W s))) 0 =
      localHessian a b τ v (coordinateVelocity v W) (coordinateVelocity v W) := by
  let γ : ℝ → Model N m := fun s ↦ atVertices v (vertexVariation v W s)
  have hγzero : γ 0 = 0 := by simp only [γ, vertexVariation_zero, atVertices_self]
  have hf : ContDiffAt ℝ 2 (localEnergy a b τ v) (γ 0) := by
    rw [hγzero]
    exact (contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγ : ContDiffAt ℝ 2 γ 0 :=
    (contDiffAt_vertexVariation_coordinates v W).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : fderiv ℝ (localEnergy a b τ v) (γ 0) = 0 := by rwa [hγzero]
  have hsecond := NoExoticSixSphere.SecondDerivativeAtCritical.deriv_deriv_comp
    (E := Model N m) hf hγ hc
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), vertexVariation v W s ∈ (atVertices v).source := by
    have hcont : Tendsto (vertexVariation v W) (𝓝 0) (𝓝 v) := by
      have h := (contMDiff_vertexVariation v W).continuous.continuousAt (x := (0 : ℝ))
      change Tendsto (vertexVariation v W) (𝓝 0) (𝓝 (vertexVariation v W 0)) at h
      simpa only [vertexVariation_zero] using h
    exact hcont.eventually ((atVertices v).open_source.mem_nhds (mem_atVertices_source v))
  have heq : (fun s ↦ energy a b τ (vertexVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ localEnergy a b τ v (γ s)) := by
    filter_upwards [hmem] with s hs
    exact congrArg (energy a b τ) ((atVertices v).left_inv hs).symm
  rw [heq.deriv.deriv_eq, hsecond, hγzero]
  have ht := real_deriv_eq_of_hasDerivAt (E := Model N m)
    (hasDerivAt_vertexVariation_coordinates v W)
  exact congrArg₂ (fun X Y ↦ localHessian a b τ v X Y) ht ht


end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
