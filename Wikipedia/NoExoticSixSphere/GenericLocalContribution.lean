module

public import Wikipedia.NoExoticSixSphere.GenericOperatorLocalParity
public import Wikipedia.NoExoticSixSphere.ResidualLinkGeometry

@[expose] public section

/-!
# The actual embedded-ball contribution of a generic singularity

The local contribution uses the original operator family on an embedded ball
in its original parameter space. The ball is centered at the given singularity,
has no other singularities, and its original operator boundary has parity one.
-/

noncomputable section

open Set Function Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.GenericLocalParity

open GLOrthonormalization CorankOne CorankOneCoordinates OperatorRank Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def HasLocalContribution (D : X → Vector 3 →L[ℝ] Vector 6) (hD : Continuous D)
    (x : X) : Prop :=
  ∃ c : RankTwoCoordinates (Vector 3) (Vector 6),
  ∃ d : ResidualCoordinates.Data (inCoordinates c D), x ∈ d.coord.source ∧
  ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target,
    d.ballMap ε 0 = x ∧
    ContDiffOn ℝ ∞ (d.ballMap ε) (closedBall (0 : Vector 4) 1) ∧
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ d.ballMap ε z.val) ∧
    (∀ z ∈ closedBall (0 : Vector 4) 1, ¬ Injective (D (d.ballMap ε z)) ↔ z = 0) ∧
    Monomorphism.sphereParity 1 (originalLink c D d hD hε hball) = 1


end NoExoticSixSphere.GenericLocalParity
