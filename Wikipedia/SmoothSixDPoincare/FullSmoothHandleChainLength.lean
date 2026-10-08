module

public import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

@[expose] public section

/-! # Rewrite a full chain's length without changing any geometric data -/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {dimension : ℕ}
  {U V : SmoothBoundaryBody J} {k l : ℕ}

def castLength (c : FullSmoothHandleChain J dimension U V k) (h : k = l) :
    FullSmoothHandleChain J dimension U V l := h ▸ c

theorem castLength_sourceMap (c : FullSmoothHandleChain J dimension U V k) (h : k = l) :
    (c.castLength h).sourceMap = c.sourceMap := by subst l; rfl

theorem castLength_indices (c : FullSmoothHandleChain J dimension U V k) (h : k = l) :
    (c.castLength h).indices = c.indices := by subst l; rfl

def castLengthPieces (c : FullSmoothHandleChain J dimension U V k) (h : k = l) :
    c.pieces ≃ₜ (c.castLength h).pieces := by subst l; exact Homeomorph.refl _


end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
