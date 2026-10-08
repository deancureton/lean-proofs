module

public import Wikipedia.NoExoticSixSphere.JamesPairFiberThreeDescent
public import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberDetection

@[expose] public section

/-!
# The actual James inclusion fiber has trivial third homology and homotopy

All assumptions of the ending-path detection argument are discharged.
The original fourth relative homology is zero and surjects onto the
original third fiber homology. The actual third Hurewicz isomorphism
then annihilates native third homotopy at every point. The actual source
inclusion is surjective on fourth homotopy by the original fiber sequence.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected
attribute [local instance] fiberSimplyConnected fiberPiTwo

theorem fiberHomologyMap_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective (fiberHomologyMap n a) :=
  (normalizationData n a).fiberHomologyMap_surjective_three

theorem fiber_homologyThree_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (z : SingularHomology (SourceFiber (n + 2) a) 3) : z = 0 := by
  obtain ⟨c, rfl⟩ := fiberHomologyMap_surjective n a z
  exact fiberHomologyMap_apply_eq_zero n a c

theorem fiber_homologyThree_subsingleton (n : ℕ) (a : sourceImage (n + 2)) :
    Subsingleton (SingularHomology (SourceFiber (n + 2) a) 3) :=
  ⟨fun z w ↦ (fiber_homologyThree_eq_zero n a z).trans (fiber_homologyThree_eq_zero n a w).symm⟩

theorem fiber_piThree_subsingleton (n : ℕ) (a : sourceImage (n + 2))
    (p : SourceFiber (n + 2) a) : Subsingleton (π_ 3 (SourceFiber (n + 2) a) p) := by
  let := sourceFiber_simplyConnected n a
  let := PairNormalization.fiber_piTwo_subsingleton n a p
  let := fiber_homologyThree_subsingleton n a
  exact (ThirdHurewicz.hurewiczPi3Equiv p).injective.subsingleton




end NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization
