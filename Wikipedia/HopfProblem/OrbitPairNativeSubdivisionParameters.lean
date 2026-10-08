module

public import Wikipedia.HopfProblem.OrbitPairSubdivisionRelations

@[expose] public section

/-!
# Cell parameters for the two actual subdivision functors

The pointwise colimit and exact gluing statements are instantiated for
mathlib's `SSet.sd` and for the constructed dual subdivision. These are
statements about the actual functor values, with all Kan-extension
existence and universality requirements discharged.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

open Subdivision

variable (X : SSet.{u}) (k : ℕ)



theorem dual_projection_surjective :
    Function.Surjective (projection dualStandard.{u} dualSd dualSdIso.inv X k) :=
  projection_surjective dualStandard dualSd dualSdIso.inv X k

theorem dual_projection_eq_iff (a b : Parameters dualStandard.{u} X k) :
    projection dualStandard dualSd dualSdIso.inv X k a =
      projection dualStandard dualSd dualSdIso.inv X k b ↔
        Relation.EqvGen (Glue dualStandard X k) a b :=
  projection_eq_iff dualStandard dualSd dualSdIso.inv X k a b

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters
