module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.SphereSumGluingImmersion

@[expose] public section

/-! # Native pair transversality through two actual local source diffeomorphisms -/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem surjective_coprod_swap (A B : Vector 3 →L[ℝ] Vector 6)
    (h : Surjective (A.coprod B)) : Surjective (B.coprod A) := by
  intro w
  obtain ⟨p, hp⟩ := h w
  refine ⟨(p.2, p.1), ?_⟩
  change B p.2 + A p.1 = w
  rw [add_comm]
  exact hp

theorem surjective_coprod_comp_both (A B : Vector 3 →L[ℝ] Vector 6)
    (S T : Vector 3 →L[ℝ] Vector 3) (hS : Surjective S) (hT : Surjective T)
    (h : Surjective (A.coprod B)) : Surjective ((A.comp S).coprod (B.comp T)) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  obtain ⟨x, hx⟩ := hS u
  obtain ⟨y, hy⟩ := hT v
  refine ⟨(x, y), ?_⟩
  change A (S x) + B (T y) = w
  rw [hx, hy]
  exact huv


end NoExoticSixSphere.SphereSumNeck
