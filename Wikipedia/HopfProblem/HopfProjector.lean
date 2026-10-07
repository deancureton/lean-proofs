module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import Wikipedia.HopfProblem.CuspCircleOrbitLocalAlgebra
public import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

@[expose] public section

noncomputable section

namespace Wikipedia.HopfProblem.HopfProjector

open Complex
open scoped ComplexConjugate

def project (y : ℂ × ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (((1 + y.2 : ℝ) : ℂ) * v.1 + y.1 * conj v.2,
    y.1 * conj v.1 + ((1 - y.2 : ℝ) : ℂ) * v.2)

theorem project_eigen_left (y : ℂ × ℝ) (hy : normSq y.1 + y.2 ^ 2 = 1)
    (v : ℂ × ℂ) :
    ((1 - y.2 : ℝ) : ℂ) * (project y v).1 = y.1 * conj (project y v).2 := by
  have hy' : y.1 * conj y.1 = (1 : ℂ) - (y.2 : ℂ) ^ 2 := by
    rw [mul_conj]
    exact_mod_cast (show normSq y.1 = 1 - y.2 ^ 2 by linarith)
  simp only [project, map_add, map_sub, map_one, map_mul, conj_ofReal, conj_conj, ofReal_sub, ofReal_one,
    ofReal_add]
  calc
    _ = ((1 : ℂ) - (y.2 : ℂ) ^ 2) * v.1 + (1 - y.2) * y.1 * conj v.2 := by ring
    _ = _ := by rw [← hy']; ring

theorem project_eigen_right (y : ℂ × ℝ) (hy : normSq y.1 + y.2 ^ 2 = 1)
    (v : ℂ × ℂ) :
    y.1 * conj (project y v).1 = ((1 + y.2 : ℝ) : ℂ) * (project y v).2 := by
  have hy' : y.1 * conj y.1 = (1 : ℂ) - (y.2 : ℂ) ^ 2 := by
    rw [mul_conj]
    exact_mod_cast (show normSq y.1 = 1 - y.2 ^ 2 by linarith)
  simp only [project, map_add, map_sub, map_one, map_mul, conj_ofReal, conj_conj, ofReal_sub, ofReal_one,
    ofReal_add]
  rw [mul_add, ← mul_assoc y.1 (conj y.1), hy']
  ring

theorem eigen_hopf {a b c : ℂ} {t : ℝ}
    (hl : ((1 - t : ℝ) : ℂ) * a = c * conj b)
    (hr : c * conj a = ((1 + t : ℝ) : ℂ) * b) :
    2 * a * b = c * (normSq a + normSq b : ℝ) ∧
      normSq a - normSq b = t * (normSq a + normSq b) := by
  constructor
  · have ha := congrArg (fun z : ℂ ↦ a * z) hr
    have hb := congrArg (fun z : ℂ ↦ b * z) hl
    simp only [ofReal_add, ofReal_sub, ofReal_one] at ha hb
    have hna := mul_conj a
    have hnb := mul_conj b
    push_cast
    linear_combination -ha + hb + c * hna + c * hnb
  · have ha := congrArg (fun z : ℂ ↦ conj a * z) hl
    have hb := congrArg (fun z : ℂ ↦ conj b * z) hr
    have hna := mul_conj a
    have hnb := mul_conj b
    have he : ((normSq a - normSq b : ℝ) : ℂ) =
        (t : ℂ) * (normSq a + normSq b : ℝ) := by
      push_cast
      simp only [ofReal_add, ofReal_sub, ofReal_one] at ha hb
      linear_combination ha + hb - (1 - (t : ℂ)) * hna + (1 + (t : ℂ)) * hnb
    exact_mod_cast he

open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

abbrev Total := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}
abbrev Base := {y : ℂ × ℝ // normSq y.1 + y.2 ^ 2 = 1}

def hopf : C(Total, Base) where
  toFun v := ⟨hopfMap v.val, by rw [hopfMap_radius_squared, v.property]; norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact hopfMap_continuous.comp continuous_subtype_val

theorem project_zero_implies_antipodal (y : Base) (v : Total)
    (hz : project y.val v.val = 0) : (hopf v).val = -y.val := by
  have ha := congrArg Prod.fst hz
  have hb := congrArg Prod.snd hz
  change ((1 + y.val.2 : ℝ) : ℂ) * v.val.1 + y.val.1 * conj v.val.2 = 0 at ha
  change y.val.1 * conj v.val.1 + ((1 - y.val.2 : ℝ) : ℂ) * v.val.2 = 0 at hb
  have hl : ((1 - -y.val.2 : ℝ) : ℂ) * v.val.1 = -y.val.1 * conj v.val.2 := by
    push_cast at ha ⊢
    linear_combination ha
  have hr : -y.val.1 * conj v.val.1 = ((1 + -y.val.2 : ℝ) : ℂ) * v.val.2 := by
    push_cast at hb ⊢
    linear_combination -hb
  have he := eigen_hopf hl hr
  rw [v.property, ofReal_one, mul_one, mul_one] at he
  exact Prod.ext he.1 he.2

theorem project_self (v : Total) : project (hopf v).val v.val = (2 : ℝ) • v.val := by
  have hv : (normSq v.val.1 : ℂ) + normSq v.val.2 = 1 := by exact_mod_cast v.property
  have ha := mul_conj v.val.1
  have hb := mul_conj v.val.2
  apply Prod.ext
  · change ((1 + (normSq v.val.1 - normSq v.val.2) : ℝ) : ℂ) * v.val.1 +
      (2 * v.val.1 * v.val.2) * conj v.val.2 = (2 : ℝ) • v.val.1
    simp only [real_smul, ofReal_ofNat]
    push_cast
    linear_combination v.val.1 * hv + 2 * v.val.1 * hb
  · change (2 * v.val.1 * v.val.2) * conj v.val.1 +
      ((1 - (normSq v.val.1 - normSq v.val.2) : ℝ) : ℂ) * v.val.2 = (2 : ℝ) • v.val.2
    simp only [real_smul, ofReal_ofNat]
    push_cast
    linear_combination v.val.2 * hv + 2 * v.val.2 * ha

def size (v : ℂ × ℂ) : ℝ := normSq v.1 + normSq v.2

def normalize (v : ℂ × ℂ) : ℂ × ℂ := (Real.sqrt (size v))⁻¹ • v

theorem size_pos {v : ℂ × ℂ} (hv : v ≠ 0) : 0 < size v := by
  have ha := normSq_nonneg v.1
  have hb := normSq_nonneg v.2
  have hn : size v ≠ 0 := by
    intro he
    apply hv
    apply Prod.ext
    · exact normSq_eq_zero.mp (by dsimp [size] at he; linarith)
    · exact normSq_eq_zero.mp (by dsimp [size] at he; linarith)
  exact lt_of_le_of_ne (add_nonneg ha hb) hn.symm

theorem normalize_size {v : ℂ × ℂ} (hv : v ≠ 0) : size (normalize v) = 1 := by
  have hp := size_pos hv
  have hs := Real.sq_sqrt hp.le
  have hs0 : Real.sqrt (size v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, size, Prod.smul_fst, Prod.smul_snd, real_smul, normSq_mul,
    normSq_ofReal]
  rw [← mul_add]
  change (Real.sqrt (size v))⁻¹ * (Real.sqrt (size v))⁻¹ * size v = 1
  rw [← pow_two, inv_pow, hs, inv_mul_cancel₀ hp.ne']

theorem normalize_hopf (y : Base) (v : ℂ × ℂ) (hv : project y.val v ≠ 0) :
    hopfMap (normalize (project y.val v)) = y.val := by
  let q := project y.val v
  have he := eigen_hopf (project_eigen_left y.val y.property v)
    (project_eigen_right y.val y.property v)
  have hn := normalize_size hv
  have hs : (Real.sqrt (size q))⁻¹ ^ 2 * size q = 1 := by
    have hsq := Real.sq_sqrt (size_pos hv).le
    rw [inv_pow, hsq, inv_mul_cancel₀ (size_pos hv).ne']
  apply Prod.ext
  · change 2 * ((Real.sqrt (size q))⁻¹ • q.1) * ((Real.sqrt (size q))⁻¹ • q.2) = y.val.1
    simp only [real_smul]
    calc
      _ = (((Real.sqrt (size q))⁻¹ : ℝ) : ℂ) ^ 2 * (2 * q.1 * q.2) := by ring
      _ = _ := by
        rw [he.1]
        change _ = y.val.1
        have hs' : (((Real.sqrt (size q))⁻¹ : ℝ) : ℂ) ^ 2 * (size q : ℂ) = 1 := by
          exact_mod_cast hs
        change (((Real.sqrt (size q))⁻¹ : ℝ) : ℂ) ^ 2 * (y.val.1 * (size q : ℂ)) = y.val.1
        linear_combination y.val.1 * hs'
  · change normSq ((Real.sqrt (size q))⁻¹ • q.1) -
      normSq ((Real.sqrt (size q))⁻¹ • q.2) = y.val.2
    simp only [real_smul, normSq_mul, normSq_ofReal]
    rw [← mul_sub, he.2]
    rw [← pow_two]
    change (Real.sqrt (size q))⁻¹ ^ 2 * (y.val.2 * size q) = y.val.2
    linear_combination y.val.2 * hs

theorem normalize_project_self (v : Total) : normalize (project (hopf v).val v.val) = v.val := by
  rw [project_self]
  have hs : size ((2 : ℝ) • v.val) = 4 := by
    simp only [size, Prod.smul_fst, Prod.smul_snd, real_smul, normSq_mul, normSq_ofReal]
    nlinarith [v.property]
  simp only [normalize, hs, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num [Real.sqrt_eq_iff_mul_self_eq_of_pos, smul_smul]

def transportDomain : TopologicalSpace.Opens (Base × Base) :=
  ⟨{p | p.1.val ≠ -p.2.val}, isOpen_ne_fun (by fun_prop) (by fun_prop)⟩

theorem transportDomain_diagonal (y : Base) : (y, y) ∈ transportDomain := by
  intro he
  have hc := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  change y.val.1 = -y.val.1 at hc
  change y.val.2 = -y.val.2 at ht
  have hc0 : y.val.1 = 0 := by linear_combination hc / 2
  have ht0 : y.val.2 = 0 := by linarith
  have hy := y.property
  simp [hc0, ht0] at hy

abbrev TransportInput := {z : Total × Base // (hopf z.1, z.2) ∈ transportDomain}

theorem project_ne_zero (z : TransportInput) : project z.val.2.val z.val.1.val ≠ 0 :=
  fun h ↦ z.property (project_zero_implies_antipodal z.val.2 z.val.1 h)

def transport (z : TransportInput) : Total :=
  ⟨normalize (project z.val.2.val z.val.1.val), normalize_size (project_ne_zero z)⟩

theorem continuous_transport : Continuous transport := by
  apply Continuous.subtype_mk
  have hq : Continuous (fun z : TransportInput ↦ project z.val.2.val z.val.1.val) := by
    unfold project
    fun_prop
  have hs : Continuous (fun z : TransportInput ↦ size (project z.val.2.val z.val.1.val)) := by
    unfold size
    fun_prop
  exact ((hs.sqrt).inv₀ (fun z ↦ (Real.sqrt_pos.mpr (size_pos (project_ne_zero z))).ne')).smul hq

def localTransport : OrbitPair.LocalTransport hopf where
  domain := transportDomain
  diagonal := transportDomain_diagonal
  transport := ⟨transport, continuous_transport⟩
  project z := Subtype.ext (normalize_hopf z.val.2 z.val.1.val (project_ne_zero z))
  self v := Subtype.ext (normalize_project_self v)

open scoped unitInterval

theorem exists_lift_stationary {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Base)) (a₀ : C(X, Total)) (ha₀ : ∀ x, hopf (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, Total), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, hopf (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  localTransport.exists_lift_stationary H a₀ ha₀

end Wikipedia.HopfProblem.HopfProjector
