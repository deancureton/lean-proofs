module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.HigherCubeCircleExtension
public import Wikipedia.HomotopyGroupsOfSpheres.HopfInjectivity

@[expose] public section

/-!
# The original Hopf projection induces all higher native isomorphisms

The existing compact homotopy lifts retain every stationary parameter.
The exact higher-cube circle extension makes those lifts based. A lifted
nullhomotopy ends in the actual circle fiber, whose native higher groups
vanish. Thus the ORIGINAL Hopf sphere map induces native isomorphisms in
all degrees at least three, not just its previously checked third group.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HomotopyGroupsOfSpheres
open Wikipedia.HomotopyGroupsOfSpheres.HopfDirect
open Wikipedia.HopfProblem.SecondHurewicz

namespace NoExoticSixSphere.HigherHopf

theorem based_cube_lift (n : ℕ) (v : Total)
    (p : GenLoop (Fin (n + 3)) (Base) (sphereMap v)) :
    ∃ q : GenLoop (Fin (n + 3)) (Total) v,
      mapGenLoop (sphereMap) v q = p := by
  let H : C(I × (Fin (n + 3) → I), Base) :=
    ⟨fun tu ↦ p (fun i ↦ tu.1 * tu.2 i), by fun_prop⟩
  have hp₀ : p.val 0 = sphereMap v := p.property 0 ⟨0, Or.inl rfl⟩
  obtain ⟨L, _, hLp, _⟩ := hopf_exists_homotopy_lift H
    (ContinuousMap.const _ v) (fun u ↦ by simpa [H, Pi.zero_def] using hp₀.symm)
  let F : C(Fin (n + 3) → I, Total) :=
    L.comp ⟨fun u ↦ (1, u), continuous_const.prodMk continuous_id⟩
  have hF (u : Fin (n + 3) → I) : sphereMap (F u) = p u := by
    simpa [F, H] using hLp 1 u
  let e := hopfFiberHomeomorph v
  let g₀ : C(Cube.boundary (Fin (n + 3)),
      {w : Total // sphereMap w = sphereMap v}) := {
    toFun u := ⟨F u.val, (hF u.val).trans (p.property u.val u.property)⟩
    continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk _ }
  let g : C(Cube.boundary (Fin (n + 3)), Circle) := (e.symm : C(_, _)).comp g₀
  obtain ⟨G, hG⟩ := boundary_circle_extension n g
  have hcorrection (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) :
      G u • v = F u := by
    rw [hG ⟨u, hu⟩]
    exact congrArg Subtype.val (e.apply_symm_apply (g₀ ⟨u, hu⟩))
  let q : GenLoop (Fin (n + 3)) (Total) v :=
    ⟨⟨fun u ↦ (G u)⁻¹ • F u, by fun_prop⟩, fun u hu ↦ by
      change (G u)⁻¹ • F u = v
      rw [← hcorrection u hu, inv_smul_smul]⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (sphereMap_sphereAction (G u)⁻¹ (F u)).trans (hF u)

theorem pi_surjective (n : ℕ) (v : Total) :
    Function.Surjective (map (N := Fin (n + 3)) (sphereMap) v) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq⟩ := based_cube_lift n v p
    refine ⟨⟦q⟧, ?_⟩
    change (⟦mapGenLoop (sphereMap) v q⟧ :
      π_ (n + 3) (Base) (sphereMap v)) = ⟦p⟧
    rw [hq]

theorem fiber_cube_nullhomotopic (n : ℕ) (v : Total)
    (q : GenLoop (Fin (n + 3)) (Total) v)
    (hq : ∀ u, sphereMap (q u) = sphereMap v) :
    GenLoop.Homotopic q GenLoop.const := by
  let e := hopfFiberHomeomorph v
  let F : C(Fin (n + 3) → I, {w : Total // sphereMap w = sphereMap v}) :=
    ⟨fun u ↦ ⟨q u, hq u⟩, q.val.continuous.subtype_mk _⟩
  have he₁ : e.symm ⟨v, rfl⟩ = 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hopfFiberHomeomorph_one v).symm
  let g : GenLoop (Fin (n + 3)) Circle 1 :=
    ⟨(e.symm : C(_, _)).comp F, fun u hu ↦ by
      change e.symm (F u) = 1
      have hF : F u = ⟨v, rfl⟩ := Subtype.ext (q.property u hu)
      rw [hF, he₁]⟩
  let k : C(Circle, Total) := ⟨fun u ↦ u • v, by fun_prop⟩
  have h := (circle_genLoop_nullhomotopic (n + 1) 1 g).comp_continuousMap k
  have hk : k.comp g.val = q.val := by
    apply ContinuousMap.ext
    intro u
    exact congrArg Subtype.val (e.apply_symm_apply (F u))
  have hk₁ : k.comp (GenLoop.const : GenLoop (Fin (n + 3)) Circle 1).val =
      (GenLoop.const : GenLoop (Fin (n + 3)) (Total) v).val := by
    apply ContinuousMap.ext
    intro u
    exact one_smul Circle v
  change (k.comp g.val).HomotopicRel
    (k.comp (GenLoop.const : GenLoop (Fin (n + 3)) Circle 1).val)
      (Cube.boundary (Fin (n + 3))) at h
  rwa [hk, hk₁] at h

theorem nullhomotopic_of_projection (n : ℕ) (v : Total)
    (p : GenLoop (Fin (n + 3)) (Total) v)
    (h : GenLoop.Homotopic (mapGenLoop (sphereMap) v p) GenLoop.const) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨H⟩ := h
  obtain ⟨L, hL₀, hLp, hLfix⟩ := hopf_exists_homotopy_lift H.toContinuousMap p.val
    (fun u ↦ (H.map_zero_left u).symm)
  have hstationary (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) (t : I) :
      H (t, u) = H (0, u) := (H.eq_fst t hu).trans (H.eq_fst 0 hu).symm
  have hboundary (t : I) (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) :
      L (t, u) = v := (hLfix u (hstationary u hu) t).trans (p.property u hu)
  let q : GenLoop (Fin (n + 3)) (Total) v :=
    ⟨L.comp ⟨fun u ↦ (1, u), continuous_const.prodMk continuous_id⟩, hboundary 1⟩
  have hpq : GenLoop.Homotopic p q := ⟨{
    toContinuousMap := L
    map_zero_left := hL₀
    map_one_left := fun _ ↦ rfl
    prop' := fun t u hu ↦ hLfix u (hstationary u hu) t }⟩
  apply hpq.trans
  apply fiber_cube_nullhomotopic n v q
  intro u
  exact (hLp 1 u).trans (H.map_one_left u)

theorem pi_injective (n : ℕ) (v : Total) :
    Function.Injective (map (N := Fin (n + 3)) (sphereMap) v) := by
  apply (injective_iff_map_eq_one (map (N := Fin (n + 3)) (sphereMap) v)).mpr
  intro a ha
  induction a using Quotient.inductionOn with
  | h p =>
    exact Quotient.sound
      (nullhomotopic_of_projection n v p (Quotient.exact ha))

def piMulEquiv (n : ℕ) (v : Total) :
    π_ (n + 3) (Total) v ≃*
      π_ (n + 3) (Base) (sphereMap v) :=
  MulEquiv.ofBijective (map (N := Fin (n + 3)) (sphereMap) v)
    ⟨pi_injective n v, pi_surjective n v⟩

theorem piMulEquiv_apply (n : ℕ) (v : Total) (c : π_ (n + 3) (Total) v) :
    piMulEquiv n v c =
      map (N := Fin (n + 3)) (sphereMap) v c := rfl

theorem piMulEquiv_zero (v : Total) :
    piMulEquiv 0 v = hopfPi3MulEquiv v := by
  apply MulEquiv.ext
  intro c
  rfl

end NoExoticSixSphere.HigherHopf
