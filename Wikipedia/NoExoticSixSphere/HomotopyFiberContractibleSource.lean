module

public import Wikipedia.HopfProblem.OrbitPairHomotopyFiberExactSequence
public import Wikipedia.NoExoticSixSphere.ContractibleNativeHomotopy

@[expose] public section

/-!
# The original loop inclusion for a contractible fiber source

The checked native fiber sequence makes its boundary map bijective when
the source is contractible. Canceling the original cube-currying
equivalence proves bijectivity of the literal loop inclusion, at the
specified source point and in every positive degree.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberContractibleSource

open HomotopyFiber

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
  (f : C(X, Y)) (x : X)

theorem boundary_bijective (d : ℕ) [NeZero d] :
    Function.Bijective (boundaryHom d f x) := by
  let : Subsingleton (π_ d X x) := ContractibleNativeHomotopy.subsingleton d x
  let : Subsingleton (π_ (d + 1) X x) := ContractibleNativeHomotopy.subsingleton (d + 1) x
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← source_range_eq_boundary_ker d f x]
    apply MonoidHom.range_eq_bot_iff.mpr
    ext c
    exact (congrArg (HigherHomotopy.mapMonoidHom (N := Fin (d + 1)) f (y := x) rfl)
      (Subsingleton.elim c 1)).trans (map_one _)
  · intro c
    apply (projection_eq_const_iff_exists_boundary_class d f x c).mp
    exact @Subsingleton.elim (π_ d X x) inferInstance _ _


end NoExoticSixSphere.HomotopyFiberContractibleSource
