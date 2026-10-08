module

public import Wikipedia.NoExoticSixSphere.LocalSphereCollapse
public import Wikipedia.NoExoticSixSphere.FiberPreservingSphereSmoothing

@[expose] public section

/-!
# A globally smooth sphere-collapse representative retaining the local fiber

Relative smoothing on the source sphere leaves the constructed collapse
unchanged near the embedded manifold and preserves its distinguished fiber
exactly. The representative is homotopic to the original continuous collapse.
No nullhomotopy or framed nullbordism is asserted.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere

namespace EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem exists_smoothSphereMap :
    ∃ g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)),
      ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g ∧
      d.sphereMap.Homotopic g ∧
      (∀ y, g y = sphereZero (e.ambientDimension - n) ↔ ∃ x, e.compactifiedEmbedding x = y) ∧
      ∀ x, (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
        =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap := by
  obtain ⟨g, hg, hhom, hfiber, V, hV, hcontains, heq⟩ :=
    exists_smoothSphereRepresentative_preserving_fiber (I := 𝓡 e.ambientDimension)
      (e.ambientDimension - n) d.sphereMap (sphereZero (e.ambientDimension - n))
      d.isOpen_sphereNeighborhood d.contMDiffOn_sphereMap d.zero_fiber_subset_sphereNeighborhood
  refine ⟨g, hg, hhom, fun y ↦ (hfiber y).trans (d.sphereMap_zero_iff y), ?_⟩
  intro x
  have hx : e.compactifiedEmbedding x ∈ V :=
    hcontains ((d.sphereMap_zero_iff _).mpr ⟨x, rfl⟩)
  filter_upwards [hV.mem_nhds hx] with y hy
  exact heq hy

end EuclideanEmbedding.FramedCollapseData


end NoExoticSixSphere
