module

public import Wikipedia.HopfProblem.OrbitPairSubdivisionDimensionPreservation

@[expose] public section

/-!
# Native subdivision and unions of subcomplexes

Subdivision sends a subcomplex to the range of its actual subdivided
inclusion. The checked preservation of monomorphisms and pushouts implies
that this operation preserves binary unions and intersections. In
particular, the subdivided union-attachment square is an actual pushout
and pullback, not a postulated gluing model.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

instance sd_preservesMonomorphisms : SSet.sd.{u}.PreservesMonomorphisms where
  preserves := by
    intro X Y f hf
    exact SubdivisionParameters.sd_map_mono f

instance dualSd_preservesMonomorphisms : dualSd.{u}.PreservesMonomorphisms where
  preserves := by
    intro X Y f hf
    exact SubdivisionParameters.dualSd_map_mono f

end Wikipedia.HopfProblem.OrbitPair.Subdivision

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex

variable (L : SSet.{u} ⥤ SSet.{u}) {X : SSet.{u}}

def image (A : X.Subcomplex) : (L.obj X).Subcomplex := SSet.Subcomplex.range (L.map A.ι)

theorem inclusion_factor {A B : X.Subcomplex} (h : A ≤ B) :
    L.map (SSet.Subcomplex.homOfLE h) ≫ L.map B.ι = L.map A.ι :=
  (L.map_comp _ _).symm.trans (congrArg L.map (SSet.Subcomplex.homOfLE_ι h))

theorem image_monotone : Monotone (image L (X := X)) := by
  intro A B h d z hz
  obtain ⟨a, rfl⟩ := hz
  exact ⟨(L.map (SSet.Subcomplex.homOfLE h)).app d a,
    congrArg (fun f ↦ f.app d a) (inclusion_factor L h)⟩


variable [PreservesColimitsOfShape WalkingSpan L]

theorem union_isPushout (A B : X.Subcomplex) :
    IsPushout (L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      (L.map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact sq.isPushout.map L


variable [L.PreservesMonomorphisms]

theorem union_isPullback (A B : X.Subcomplex) :
    IsPullback (L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      (L.map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  exact Types.isPullback_of_isPushout ((union_isPushout L A B).app d)
    (injective_of_mono ((L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).app d))


end Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex
