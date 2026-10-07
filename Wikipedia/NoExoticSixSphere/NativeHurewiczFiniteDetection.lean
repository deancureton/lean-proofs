module

public import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso
public import Wikipedia.HopfProblem.ThirdHurewiczIso
public import Wikipedia.HopfProblem.FourthHurewiczIso
public import Wikipedia.HopfProblem.FifthHurewiczIso
public import Wikipedia.HopfProblem.SixthHurewiczIso
public import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Iso
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Vanishing detection using the constructed Hurewicz maps through degree seven

This packages the existing genuine Hurewicz equivalences in their proven
finite range. It makes no assertion about the unconstructed higher-degree
Hurewicz equivalences.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.NativeHurewiczFiniteDetection

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem subsingleton (d : ℕ) (hd : 2 ≤ d) (hle : d ≤ 7) (x : X)
    (hpi : ∀ k, 2 ≤ k → k < d → Subsingleton (π_ k X x))
    [Subsingleton (SingularHomology X d)] : Subsingleton (π_ d X x) := by
  interval_cases d
  · exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton
  · let := hpi 2 (by decide) (by decide)
    exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton
  · let := hpi 2 (by decide) (by decide)
    let := hpi 3 (by decide) (by decide)
    exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton
  · let := hpi 2 (by decide) (by decide)
    let := hpi 3 (by decide) (by decide)
    let := hpi 4 (by decide) (by decide)
    exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton
  · let := hpi 2 (by decide) (by decide)
    let := hpi 3 (by decide) (by decide)
    let := hpi 4 (by decide) (by decide)
    let := hpi 5 (by decide) (by decide)
    exact (SixthHurewicz.hurewiczPi6Equiv x).injective.subsingleton
  · let := hpi 2 (by decide) (by decide)
    let := hpi 3 (by decide) (by decide)
    let := hpi 4 (by decide) (by decide)
    let := hpi 5 (by decide) (by decide)
    let := hpi 6 (by decide) (by decide)
    let e := Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.hurewiczPi7Equiv x
    exact e.injective.subsingleton

end NoExoticSixSphere.NativeHurewiczFiniteDetection
