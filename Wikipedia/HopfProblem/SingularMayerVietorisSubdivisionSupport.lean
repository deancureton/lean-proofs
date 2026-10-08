module

public import Wikipedia.HopfProblem.SingularMayerVietorisSubdivision
public import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionHomotopy
public import Wikipedia.HopfProblem.SingularMayerVietorisRealizationSupport
public import Wikipedia.HopfProblem.SingularMayerVietorisMeshSubdivision

@[expose] public section

/-!
# Actual singular subdivision eventually lies in the small-chain subcomplex

Subdivision preserves the carrier of every singular simplex. Compactness
and the proved geometric mesh bound give a uniform subdivision stage for
the finite support of any actual singular chain. No excision or homology
equivalence is assumed in this chain-level result.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]




/-- The actual homotopy between a small chain and its subdivision is itself
small. This supplies the boundary-lifting half of the small-chain theorem. -/
theorem subdivisionHomotopy_mem_small (U V : Set X) (k n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    subdivisionHomotopy X k n c ∈ smallChainSubmodule U V (n + 1) := by
  apply singularLinearMap_mem_of_small U V n (subdivisionHomotopy X k n)
    (smallChainSubmodule U V (n + 1)) c hc
  intro σ hσ
  rw [subdivisionHomotopy_simplex]
  exact realizedChain_mem_small U V n (n + 1) σ hσ _


/-- A uniform stage works for every coefficient of an actual finite
singular chain. This is the chain-level smallness theorem used in excision. -/
theorem eventually_subdivision_mem_small (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (n : ℕ) (c : Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N, subdivision X k n c ∈ smallChainSubmodule U V n := by
  classical
  have hc : ∀ σ ∈ (chainsEquivFinsupp X n c).support, range σ ⊆ U ∪ V := by
    intro σ hσ
    rw [hcover]
    exact subset_univ _
  obtain ⟨N, hN⟩ := finite_family_formalSubdivision_eventually_small
    (chainsEquivFinsupp X n c).support hU hV hc
  refine ⟨N, ?_⟩
  intro k hk
  apply singularLinearMap_mem_of_support n (subdivision X k n) (smallChainSubmodule U V n) c
  intro σ hσ
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U V n n σ
  intro v hv
  exact hN k hk σ hσ (formalSimplex (stdVertices n)) v hv

end Wikipedia.HopfProblem.SingularMayerVietoris
