module

public import Wikipedia.NoExoticSixSphere.OrthogonalLogarithm
public import Wikipedia.NoExoticSixSphere.OrthogonalMetric
public import Wikipedia.NoExoticSixSphere.CompactParameter

@[expose] public section

/-!
# Uniform logarithmic increments in compact orthogonal homotopies

Every compactly parametrized path admits a finite subdivision whose increments
all lie in the verified local logarithm domain. This makes the increments
continuous skew-adjoint families; it does not choose logarithms globally.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform OrthogonalMetric

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- A single finite subdivision controls all increments in a prescribed identity neighborhood. -/
theorem exists_incrementSubdivision [CompactSpace X] (H : C(I × X, OrthogonalOperators n))
    (U : Set (OrthogonalOperators n)) (hU : U ∈ nhds (1 : OrthogonalOperators n)) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        (H (t i, x))⁻¹ * H (u, x) ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  let U (s : I) : Set I := {t | ∀ x, dist (H (t, x)) (H (s, x)) < δ / 2}
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    have hs : Continuous (fun p : I × X ↦ H (s, p.2)) :=
      H.continuous.comp (continuous_const.prodMk continuous_snd)
    exact isOpen_forall_compact (isOpen_lt (H.continuous.dist hs) continuous_const)
  have hcover : univ ⊆ ⋃ s, U s := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    intro x
    simpa only [dist_self] using half_pos hδ
  obtain ⟨t, ht0, hmono, hend, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU hcover
  refine ⟨t, ht0, hmono, hend, ?_⟩
  intro i u hu x
  apply hball
  rw [Metric.mem_ball, dist_left_increment]
  obtain ⟨s, hs⟩ := hsub i
  have hu' := hs hu x
  have ht' := hs ⟨le_rfl, hmono i.le_succ⟩ x
  have htri := dist_triangle (H (u, x)) (H (s, x)) (H (t i, x))
  rw [dist_comm (H (s, x)) (H (t i, x))] at htri
  linarith

/-- The same finite logarithmic subdivision works for every member of a compact path family. -/
theorem exists_logarithmSubdivision [CompactSpace X] (H : C(I × X, OrthogonalOperators n)) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        (H (t i, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source :=
  exists_incrementSubdivision H (logarithmChart n).source
    ((logarithmChart n).open_source.mem_nhds (one_mem_logarithmChart_source n))

/-- A logarithmic increment is continuous when its values lie in the logarithm chart. -/
noncomputable def logarithmicIncrement (H : C(I × X, OrthogonalOperators n)) (s t : I)
    (h : ∀ x, (H (s, x))⁻¹ * H (t, x) ∈ (logarithmChart n).source) :
    C(X, SkewOperators n) where
  toFun x := logarithmChart n ((H (s, x))⁻¹ * H (t, x))
  continuous_toFun := (logarithmChart n).contMDiffOn_toFun.continuousOn.comp_continuous
    ((H.continuous.comp (continuous_const.prodMk continuous_id)).inv.mul
      (H.continuous.comp (continuous_const.prodMk continuous_id))) h

theorem exp_logarithmicIncrement (H : C(I × X, OrthogonalOperators n)) (s t : I)
    (h : ∀ x, (H (s, x))⁻¹ * H (t, x) ∈ (logarithmChart n).source) (x : X) :
    exp (logarithmicIncrement H s t h x) = (H (s, x))⁻¹ * H (t, x) :=
  exp_logarithmChart _ (h x)

theorem logarithmicIncrement_eq_zero (H : C(I × X, OrthogonalOperators n)) (s t : I)
    (h : ∀ x, (H (s, x))⁻¹ * H (t, x) ∈ (logarithmChart n).source) (x : X)
    (hx : H (s, x) = H (t, x)) : logarithmicIncrement H s t h x = 0 := by
  change logarithmChart n ((H (s, x))⁻¹ * H (t, x)) = 0
  rw [hx, inv_mul_cancel, logarithmChart_one]


end NoExoticSixSphere.OrthogonalExponential
