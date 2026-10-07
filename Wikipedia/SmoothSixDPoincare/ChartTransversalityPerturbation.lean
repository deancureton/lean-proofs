module

public import Wikipedia.SmoothSixDPoincare.ManifoldSheetTranslations
public import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
public import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

@[expose] public section

/-!
# Transverse perturbation on a genuine chart plateau

A compactly supported chart translation is smooth on the original manifold.
One small parameter makes it transverse to the second sheet at every point
where the cutoff is locally one. No transversality is assumed there.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {D Z G F H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace K N]

/-- A locally constant translation does not change the native derivative into a vector space. -/
theorem mfderiv_eq_of_translation_germ {u v : X → F} {a : F} {x : X}
    (hu : MDifferentiableAt I 𝓘(ℝ, F) u x)
    (hevent : v =ᶠ[𝓝 x] fun z => u z + a) :
    (mfderiv I 𝓘(ℝ, F) v x : D →L[ℝ] F) = mfderiv I 𝓘(ℝ, F) u x := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) u x
  let C : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun _ : X => a) x
  have hC : C = 0 := mfderiv_const
  have hh := mfderiv_add hu
    (show MDifferentiableAt I 𝓘(ℝ, F) (fun _ : X => a) x from mdifferentiableAt_const)
  change (mfderiv I 𝓘(ℝ, F) (fun z => u z + a) x : D →L[ℝ] F) = A + C at hh
  rw [hC] at hh
  exact hevent.mfderiv_eq.trans (hh.trans (add_zero A))

/-- Transversality in a genuine smooth target chart implies native transversality. -/
theorem transverse_of_chart
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ c.source)
    (ht : Surjective ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
      (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F))) :
    Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod
      (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have heq : (C.comp A).coprod (C.comp B) = C.comp (A.coprod B) := by
    apply ContinuousLinearMap.ext
    intro v
    change C (A v.1) + C (B v.2) = C (A v.1 + B v.2)
    exact (C.map_add _ _).symm
  rw [hA, hB] at ht
  change Surjective ((C.comp A).coprod (C.comp B)) at ht
  rw [heq] at ht
  have hC : Injective C := (PartialChart.bijective_mfderiv c hx).injective
  change Surjective (A.coprod B)
  intro w
  obtain ⟨v, hv⟩ := ht (C w)
  exact ⟨v, hC hv⟩

/-- Native transversality is preserved by the actual target chart. -/
theorem transverse_in_chart
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ c.source)
    (ht : Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod
      (mfderiv I' J g y : Z →L[ℝ] G))) :
    Surjective ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
      (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  rw [hA, hB]
  change Surjective ((C.comp A).coprod (C.comp B))
  have hC : Surjective C := (PartialChart.bijective_mfderiv c hx).surjective
  change Surjective (A.coprod B) at ht
  intro w
  obtain ⟨z, hz⟩ := hC w
  obtain ⟨v, hv⟩ := ht z
  refine ⟨v, ?_⟩
  change C (A v.1) + C (B v.2) = w
  rw [← C.map_add]
  exact (congrArg C hv).trans hz

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F]
  [I.Boundaryless] [I'.Boundaryless]
  [IsManifold I ∞ X] [IsManifold I' ∞ Y] [LindelofSpace (X × Y)]


end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
