module

public import Wikipedia.NoExoticSixSphere.RelativePairCapConnectingRepresentatives
public import Wikipedia.NoExoticSixSphere.RelativeCoefficientConnecting
public import Wikipedia.NoExoticSixSphere.RelativeModTwoPairConnectingCochains
public import Wikipedia.NoExoticSixSphere.ModTwoCapDegree

@[expose] public section

/-!
# Cap compatibility for the two original connecting maps of a pair

The actual cochain and chain connecting lifts reduce the square to the
proved cap boundary primitive. All inputs are arbitrary classes in the
original homology and cohomology groups; no manifold hypothesis or
fundamental-class compatibility is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem pair_connecting_cap (p q : ℕ) (a : ModTwoCapProduct.Cohomology U p)
    (F : (RelativeCoefficients.complex Coefficient U).homology (p + q + 1)) :
    capProductInDegree U (p := p + 1) (q := q) (n := p + q + 1) (by omega)
        (RelativeModTwoCochains.connecting U p a) F =
      modHomologyMap 2 (subtypeInclusion U) q
        (ModTwoCapProduct.capProduct U p q a
          (RelativeCoefficients.connecting Coefficient U (p + q) F)) := by
  obtain ⟨α, rfl⟩ :=
    SingularCohomologyFree.cocycleClass_surjective (ModTwoCapProduct.cochainComplex U) p a
  obtain ⟨z, rfl⟩ :=
    ModuleHomology.cycleClass_surjective (RelativeCoefficients.complex Coefficient U) (p + q + 1) F
  obtain ⟨β, γ, hβ, hγ, hδ⟩ := RelativeModTwoCochains.exists_pair_connecting_cochains U p α
  obtain ⟨c, hc, w, hw, hboundary⟩ :=
    RelativeCoefficients.exists_connecting_lift Coefficient U (p + q) z
  rw [hδ, capProductInDegree_cocycle_cycle, hboundary, ModTwoCapProduct.capProduct_cocycle_cycle,
    ModTwoCapProduct.modHomologyMap_cycleClass]
  exact pair_connecting_cap_representatives U p q α β γ hβ hγ z c hc w hw

theorem pair_connecting_capInDegree {p q n : ℕ} (h : p + q = n)
    (a : ModTwoCapProduct.Cohomology U p)
    (F : (RelativeCoefficients.complex Coefficient U).homology (n + 1)) :
    capProductInDegree U (p := p + 1) (q := q) (n := n + 1) (by omega)
        (RelativeModTwoCochains.connecting U p a) F =
      modHomologyMap 2 (subtypeInclusion U) q
        (ModTwoCapProduct.capProductInDegree U h a
          (RelativeCoefficients.connecting Coefficient U n F)) := by
  subst n
  exact pair_connecting_cap U p q a F


end NoExoticSixSphere.RelativeModTwoCap
