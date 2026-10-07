module

public import Wikipedia.HomotopyGroupsOfSpheres.HopfLifting
public import Wikipedia.HomotopyGroupsOfSpheres.HopfFiber
public import Wikipedia.HomotopyGroupsOfSpheres.CubeBoundary

@[expose] public section

/-!
# Based lifts of three-cubes through the Hopf map

A contraction of the cube supplies an unrestricted lift. On the boundary
the lift lies in the circle fiber. Extend this circle-valued boundary
correction over the cube and use the circle action to make the lift based.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfDirect
open HopfProblem.SecondHurewicz

/-- Every based three-cube on the Hopf base has an actual based lift. -/
theorem hopf_based_cube_lift (v : Total)
    (p : GenLoop (Fin 3) Base (sphereMap v)) :
    ∃ q : GenLoop (Fin 3) Total v,
      mapGenLoop sphereMap v q = p := by
  let H : C(I × (Fin 3 → I), Base) :=
    ⟨fun tu => p (fun i => tu.1 * tu.2 i), by fun_prop⟩
  have hp₀ : p.val 0 = sphereMap v := p.property 0 ⟨0, Or.inl rfl⟩
  obtain ⟨L, _, hLp, _⟩ := hopf_exists_homotopy_lift H
    (ContinuousMap.const _ v) (fun u => by simpa [H, Pi.zero_def] using hp₀.symm)
  let F : C(Fin 3 → I, Total) :=
    L.comp ⟨fun u => (1, u), continuous_const.prodMk continuous_id⟩
  have hF (u : Fin 3 → I) : sphereMap (F u) = p u := by
    simpa [F, H] using hLp 1 u
  let e := hopfFiberHomeomorph v
  let g₀ : C(Cube.boundary (Fin 3),
      {w : Total // sphereMap w = sphereMap v}) := {
    toFun u := ⟨F u.val, (hF u.val).trans (p.property u.val u.property)⟩
    continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk _ }
  let g : C(Cube.boundary (Fin 3), Circle) := (e.symm : C(_, _)).comp g₀
  obtain ⟨G, hG⟩ := cubeBoundary_circle_extension g
  have hcorrection (u : Fin 3 → I) (hu : u ∈ Cube.boundary (Fin 3)) :
      G u • v = F u := by
    rw [hG ⟨u, hu⟩]
    exact congrArg Subtype.val (e.apply_symm_apply (g₀ ⟨u, hu⟩))
  let q : GenLoop (Fin 3) Total v :=
    ⟨⟨fun u => (G u)⁻¹ • F u, by fun_prop⟩, fun u hu => by
      change (G u)⁻¹ • F u = v
      rw [← hcorrection u hu, inv_smul_smul]⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (sphereMap_sphereAction (G u)⁻¹ (F u)).trans (hF u)

/-- Surjectivity of the induced map on the actual third homotopy group. -/
theorem hopf_pi3_surjective (v : Total) :
    Function.Surjective (map (N := Fin 3) sphereMap v) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq⟩ := hopf_based_cube_lift v p
    refine ⟨⟦q⟧, ?_⟩
    change (⟦mapGenLoop sphereMap v q⟧ : π_ 3 Base (sphereMap v)) = ⟦p⟧
    rw [hq]

end Wikipedia.HomotopyGroupsOfSpheres
