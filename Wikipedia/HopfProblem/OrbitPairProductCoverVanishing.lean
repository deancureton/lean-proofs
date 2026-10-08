module

public import Wikipedia.HopfProblem.OrbitPairProductCoverHomology

@[expose] public section

/-!
# Vanishing from a product cover and an injective overlap projection

If both contractible pieces have zero homology in the desired degree,
and projection detects the preceding overlap group, the actual
Mayer--Vietoris sequence forces ambient homology to vanish.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.OrbitPair.ProductCover

open SingularMayerVietoris PeriodTorusHigherHomology

variable {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]

def overlapProjection (U V : Set Y) :
    C((piece (X := X) U ∩ piece V : Set (Y × X)), X) :=
  ⟨fun p => p.val.2, continuous_subtype_val.snd⟩

theorem left_homology_injective_of_overlap_projection (U V : Set Y) (n : ℕ)
    (hp : Function.Injective (singularHomologyMap (overlapProjection (X := X) U V) n)) :
    Function.Injective (leftHomologyMap (piece (X := X) U) (piece V) n) := by
  intro a b hab
  apply hp
  have he := congrArg
    (fun p : SingularHomology (piece (X := X) U) n × SingularHomology (piece V) n =>
      singularHomologyMap (projection U) n p.1) hab
  simp only [leftHomologyMap_apply] at he
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp] at he
  exact he


end Wikipedia.HopfProblem.OrbitPair.ProductCover
