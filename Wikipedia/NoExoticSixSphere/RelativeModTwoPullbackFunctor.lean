module

public import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
public import Wikipedia.NoExoticSixSphere.ModTwoDualFunctor

@[expose] public section

/-! # Functoriality of the original relative mod-two pair pullbacks -/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem pullbackMap_id (U : Set X) :
    pullbackMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U U from
      fun _ hx ↦ hx) = 𝟙 (complex U) := by
  unfold pullbackMap
  rw [RelativeCoefficients.mapChain_id, ModTwoDualComplex.map_id]

theorem pullbackMap_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) :
    pullbackMap (g.comp f) (hg.comp hf) = pullbackMap g hg ≫ pullbackMap f hf := by
  unfold pullbackMap
  rw [RelativeCoefficients.mapChain_comp, ModTwoDualComplex.map_comp]


theorem cohomologyPullback_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) (p : ℕ) :
    cohomologyPullback (g.comp f) (hg.comp hf) p =
      (cohomologyPullback f hf p).comp (cohomologyPullback g hg p) := by
  unfold cohomologyPullback
  rw [pullbackMap_comp, HomologicalComplex.homologyMap_comp]
  rfl


end NoExoticSixSphere.RelativeModTwoCochains
