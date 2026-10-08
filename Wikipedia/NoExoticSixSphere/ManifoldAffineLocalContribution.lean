module

public import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities
public import Wikipedia.NoExoticSixSphere.LocalOperatorContribution
public import Wikipedia.NoExoticSixSphere.SphereChartBall

@[expose] public section

/-!
# Local parity-one balls for intrinsic singularities of the manifold family

The parameter ball is embedded in time times the original three-sphere.
It stays inside genuine source and target chart domains and contains exactly
the selected intrinsic singularity. Its linking-sphere operators are the actual
chart derivatives of the perturbed manifold family and have parity one.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily GenericLocalParity Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (p : Parameters e) (S : Set SourceChart) (C : Set (TargetChart 6 M))
  (hgen : GenericInCharts e r f hf S C p)

include hgen

theorem hasLocalContributionOn_chartJet (s : SourceChart) (hs : s ∈ S)
    (c : TargetChart 6 M) (hc : c ∈ C) (q : ℝ × Vector 3)
    (hq : (p, q) ∈ chartDomain e r f hf s c)
    (hJ : ¬ Injective (chartJet e r f s c (p, q))) :
    HasLocalContributionOn (fun z : ℝ × Vector 3 ↦ chartJet e r f s c (p, z))
      {z | (p, z) ∈ chartDomain e r f hf s c} q := by
  apply hasLocalContributionOn_of_regular_residual _
    ((chartDomain e r f hf s c).isOpen.preimage (continuous_const.prodMk continuous_id))
    ((contDiffOn_chartJet e r f hf s c).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz ↦ hz)) q hq
  exact (hgen.1 s hs c hc).residual_regular q hq hJ


end NoExoticSixSphere.ManifoldAffineSphereFamily
