module

public import Wikipedia.HopfProblem.CuspCircleOrbitLocalAlgebra
public import Mathlib.Analysis.Complex.Circle

@[expose] public section

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.HopfDirect

open Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

def action (u : Circle) (z : ℂ × ℂ) : ℂ × ℂ :=
  unitNormalAction (Circle.toUnits u) z

theorem action_injective {z : ℂ × ℂ} (hz : z ≠ 0) :
    Function.Injective (fun u : Circle ↦ action u z) := by
  intro u v h
  by_cases hz₂ : z.2 = 0
  · have hz₁ : z.1 ≠ 0 := by
      intro h₁
      exact hz (Prod.ext h₁ hz₂)
    have he : (u : ℂ)⁻¹ * z.1 = (v : ℂ)⁻¹ * z.1 := congrArg Prod.fst h
    exact Subtype.ext (inv_injective (mul_right_cancel₀ hz₁ he))
  · have he : (u : ℂ) * z.2 = (v : ℂ) * z.2 := congrArg Prod.snd h
    exact Subtype.ext (mul_right_cancel₀ hz₂ he)

theorem map_eq_iff (z w : ℂ × ℂ) :
    hopfMap z = hopfMap w ↔ ∃ u : Circle, action u w = z := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := (hopfMap_eq_iff w z).mp h.symm
    refine ⟨⟨u, mem_sphere_zero_iff_norm.mpr hu⟩, ?_⟩
    exact he
  · rintro ⟨u, rfl⟩
    exact hopfMap_unitNormalAction (Circle.toUnits u) (Circle.norm_coe u) w

abbrev Total := {z : ℂ × ℂ // Complex.normSq z.1 + Complex.normSq z.2 = 1}

abbrev Base := {y : ℂ × ℝ // Complex.normSq y.1 + y.2 ^ 2 = 1}

def sphereMap : C(Total, Base) where
  toFun z := ⟨hopfMap z, by rw [hopfMap_radius_squared, z.property, one_pow]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact hopfMap_continuous.comp continuous_subtype_val

def sphereAction (u : Circle) (z : Total) : Total :=
  ⟨action u z, by
    simpa [action, unitNormalAction, Complex.normSq_eq_norm_sq, norm_mul, norm_inv,
      Circle.norm_coe] using z.property⟩

theorem total_ne_zero (z : Total) : (z : ℂ × ℂ) ≠ 0 := by
  intro h
  have hz := z.property
  simp [h] at hz

theorem sphereAction_injective (z : Total) : Function.Injective (fun u ↦ sphereAction u z) := by
  intro u v h
  exact action_injective (total_ne_zero z) (congrArg Subtype.val h)

theorem sphereMap_sphereAction (u : Circle) (z : Total) :
    sphereMap (sphereAction u z) = sphereMap z :=
  Subtype.ext (hopfMap_unitNormalAction (Circle.toUnits u) (Circle.norm_coe u) z)

theorem sphereMap_eq_iff (z w : Total) :
    sphereMap z = sphereMap w ↔ ∃ u : Circle, sphereAction u w = z := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (map_eq_iff z w).mp (congrArg Subtype.val h)
    exact ⟨u, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    exact sphereMap_sphereAction u w

theorem continuous_sphereAction : Continuous (fun p : Circle × Total ↦ sphereAction p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Circle × Total ↦
    (((p.1⁻¹ : Circle) : ℂ) * p.2.val.1, (p.1 : ℂ) * p.2.val.2))
  fun_prop

def fiberHomeomorph (z : Total) : Circle ≃ₜ {w : Total // sphereMap w = sphereMap z} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun u ↦ ⟨sphereAction u z, sphereMap_sphereAction u z⟩) (by
      constructor
      · intro u v h
        exact sphereAction_injective z (congrArg Subtype.val h)
      · intro w
        obtain ⟨u, hu⟩ := (sphereMap_eq_iff w.val z).mp w.property
        exact ⟨u, Subtype.ext hu⟩))
    ((continuous_sphereAction.comp (continuous_id.prodMk continuous_const)).subtype_mk _)

instance : MulAction Circle Total where
  smul := sphereAction
  one_smul z := by
    change sphereAction 1 z = z
    apply Subtype.ext
    apply Prod.ext <;> simp [sphereAction, action, unitNormalAction]
  mul_smul u v z := by
    change sphereAction (u * v) z = sphereAction u (sphereAction v z)
    apply Subtype.ext
    apply Prod.ext <;> simp [sphereAction, action, unitNormalAction, mul_assoc, mul_left_comm]

instance : ContinuousSMul Circle Total := ⟨continuous_sphereAction⟩

@[simp] theorem fiberHomeomorph_apply (z : Total) (u : Circle) :
    (fiberHomeomorph z u).val = u • z := rfl

@[simp] theorem fiberHomeomorph_one (z : Total) : fiberHomeomorph z 1 = ⟨z, rfl⟩ := by
  apply Subtype.ext
  exact one_smul Circle z

end Wikipedia.HomotopyGroupsOfSpheres.HopfDirect
