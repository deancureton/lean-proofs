module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseRoundedTraceRetraction
public import Wikipedia.NoExoticSixSphere.RoundedTraceTopEnd
public import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

@[expose] public section

/-!
# Rounding preserves the actual attachment homotopy type and original-end kernel

The inclusion of the unrounded attachment has the constructed retraction
as a genuine homotopy inverse. Its homology isomorphism is the map of that
literal inclusion. The original-end inclusions commute exactly, so their
actual homology kernels agree before and after rounding.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def retraction : C(ambientSet A, UnroundedTrace.ambientSet A) :=
  ⟨fun x ↦ ⟨(deformation A (1, x)).val, deformation_one_mem A x⟩,
    (continuous_subtype_val.comp ((deformation A).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

theorem retraction_comp_oldInclusion :
    (retraction A).comp (oldInclusion A) = ContinuousMap.id (UnroundedTrace.ambientSet A) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun z : ambientSet A ↦ z.val) (deformation_fixed A 1 x)

def deformationHomotopy : (ContinuousMap.id (ambientSet A)).Homotopy
    ((oldInclusion A).comp (retraction A)) where
  toContinuousMap := deformation A
  map_zero_left := deformation_zero A
  map_one_left := fun _ ↦ rfl

def unroundedHomotopyEquiv : UnroundedTrace.ambientSet A ≃ₕ ambientSet A where
  toFun := oldInclusion A
  invFun := retraction A
  left_inv := by rw [retraction_comp_oldInclusion]
  right_inv := ⟨(deformationHomotopy A).symm⟩

theorem oldInclusion_homology_bijective (n : ℕ) :
    Bijective (singularHomologyMap (oldInclusion A) n) :=
  (homotopyEquivHomologyEquiv (unroundedHomotopyEquiv A) n).bijective

def oldTopMap : C(M, UnroundedTrace.ambientSet A) :=
  ⟨fun m ↦ ⟨e.heightCylinder (m, UnroundedTrace.height A),
      Or.inl ⟨(m, ⟨UnroundedTrace.height A, (UnroundedTrace.height_pos A).le, le_rfl⟩), rfl⟩⟩,
    (e.continuous_heightCylinder.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

theorem oldInclusion_comp_oldTopMap : (oldInclusion A).comp (oldTopMap A) = topMap A := rfl


end Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)


end Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction
