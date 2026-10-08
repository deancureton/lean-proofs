module

public import Wikipedia.NoExoticSixSphere.JamesPairFiberThreeDetection
public import Wikipedia.NoExoticSixSphere.NativeHurewiczFiniteDetection
public import Wikipedia.NoExoticSixSphere.RelativeNormalizationRecovery

@[expose] public section

/-!
# Higher connectivity of the actual James source-inclusion fiber

The general relative normalization and ending-path recovery turn lower
native fiber connectivity into homology vanishing in the next degree.
Induction using the already constructed Hurewicz equivalences proves
native vanishing through degree seven and homology vanishing in degrees
two through eight. Full homotopy comparison is not inferred.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.HigherFiberDetection

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected

theorem fiber_homology_subsingleton_of_pi (n d : ℕ)
    (hpi : ∀ k, 0 < k → k < d + 2 → ∀ a : sourceImage (n + 2),
      ∀ p : SourceFiber (n + 2) a, Subsingleton (π_ k (SourceFiber (n + 2) a) p))
    (a : sourceImage (n + 2)) :
    Subsingleton (SingularHomology (SourceFiber (n + 2) a) (d + 2)) := by
  let : Subsingleton (RelativeSingularHomology.Homology (sourceImage (n + 2)) (d + 3)) :=
    relative_homology_subsingleton (n + 2) (d + 3) (by omega)
  exact RelativeNormalization.fiber_homology_subsingleton_of_fiberConnectivity
    (sourceImage (n + 2)) a d hpi

theorem fiber_pi_le_seven (n : ℕ) : ∀ d, 0 < d → d ≤ 7 →
    ∀ a : sourceImage (n + 2), ∀ p : SourceFiber (n + 2) a,
      Subsingleton (π_ d (SourceFiber (n + 2) a) p) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hle a p
    let := sourceFiber_simplyConnected n a
    by_cases h1 : d = 1
    · subst d
      exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
    · have h2 : 2 ≤ d := by omega
      have hlow : ∀ k, 0 < k → k < d → ∀ b : sourceImage (n + 2),
          ∀ q : SourceFiber (n + 2) b, Subsingleton (π_ k (SourceFiber (n + 2) b) q) :=
        fun k hk hkd b q ↦ ih k hkd hk (by omega) b q
      let : Subsingleton (SingularHomology (SourceFiber (n + 2) a) d) := by
        have h := fiber_homology_subsingleton_of_pi n (d - 2)
          (fun k hk hkd b q ↦ hlow k hk (by omega) b q) a
        simpa only [Nat.sub_add_cancel h2] using h
      exact NativeHurewiczFiniteDetection.subsingleton d h2 hle p
        (fun k hk hkd ↦ hlow k (by omega) hkd a p)




end NoExoticSixSphere.JamesSphere.HigherFiberDetection
