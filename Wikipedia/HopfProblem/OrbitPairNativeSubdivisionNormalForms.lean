module

public import Wikipedia.HopfProblem.OrbitPairSubdivisionNormalForm

@[expose] public section

/-!
# Unique normal forms in the actual subdivision functors

These statements concern every simplicial degree of `SSet.sd.obj X` and
`dualSd.obj X`. The support laws, supporting faces, and left Kan extension
requirements are all discharged by the checked native constructions.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters

open Subdivision SubdivisionSupport

variable (X : SSet.{u}) (k : ℕ)


theorem dual_existsUnique_normal (z : (dualSd.obj X) _⦋k⦌) :
    ∃! p : {p : Parameters dualStandard.{u} X k // IsNormal (dualLaw k) X p},
      projection dualStandard dualSd dualSdIso.inv X k p.val = z :=
  existsUnique_normal (dualLaw k) (dualFace k) X dualSd dualSdIso.inv z


theorem dual_normal_injective {a b : Parameters dualStandard.{u} X k}
    (ha : IsNormal (dualLaw k) X a) (hb : IsNormal (dualLaw k) X b)
    (h : projection dualStandard dualSd dualSdIso.inv X k a =
      projection dualStandard dualSd dualSdIso.inv X k b) : a = b :=
  normal_injective (dualLaw k) (dualFace k) X dualSd dualSdIso.inv ha hb h

end Wikipedia.HopfProblem.OrbitPair.SubdivisionParameters
