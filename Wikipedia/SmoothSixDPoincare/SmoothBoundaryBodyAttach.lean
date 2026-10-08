module

public import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv
public import Wikipedia.SmoothSixDPoincare.FramedSurgeryBaseChangeBody

@[expose] public section

/-!
# Extend an exact smooth boundary/body equivalence by a matching whole handle

The extension retains the old body map, every whole-handle coordinate,
and the exact commuting boundary map. Both new native smooth atlases can
be constructed from the original smooth boundary manifolds.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv

open PuncturedHandle FramedSurgery

variable {E F G H X X' Y Y' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace H X]
  [TopologicalSpace X'] [T2Space X'] [CompactSpace X'] [ChartedSpace H X']
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
  {i : C(X, Y)} {i' : C(X', Y')}
  (e : SmoothBoundaryBodyEquiv (J := J) i i')
  (hi : IsClosedEmbedding i) (hi' : IsClosedEmbedding i')
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (A' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X')
  (hface : ∀ z, e.boundary (A.map z) = A'.map z)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData A' n)

def attach :
    letI := P.charted
    letI := Q.charted
    SmoothBoundaryBodyEquiv (J := J) (boundaryBodyMap A i n hi) (boundaryBodyMap A' i' n hi') := by
  let _ := P.charted
  let _ := Q.charted
  exact {
    body := baseChangeBody A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point
    boundary := baseChangeDiffeomorph A A' n e.boundary hface P Q
    boundary_point := fun z =>
      (baseChangeDiffeomorph_bodyMap A A' i i' e.body hi hi' n
        e.boundary hface e.boundary_point P Q z).symm }

theorem attach_body :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body =
      baseChangeBody A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point := rfl

theorem attach_old (y : Y) :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body (FaceAttachment.oldMap (bodyFaceMap A i) y) =
      FaceAttachment.oldMap (bodyFaceMap A' i') (e.body y) := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBody_old A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point y

theorem attach_handle (k : WholeHandle E F) :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body (FaceAttachment.handleMap (bodyFaceMap A i) k) =
      FaceAttachment.handleMap (bodyFaceMap A' i') k := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBody_handle A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point k

theorem attach_boundary_toHomeomorph :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).boundary.toHomeomorph =
      baseChangeBoundary A A' n e.boundary.toHomeomorph hface := rfl



end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv
