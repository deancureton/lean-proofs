module

public import Wikipedia.NoExoticSixSphere.ArfPlanes
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite orthogonal sums in the Arf calculation

The Gauss sum of a finite family of independent quadratic planes factors
into the plane Gauss sums. This gives the usual sum of pairwise products
whenever actual symplectic coordinates are provided.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → F₂) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, Fintype (V i)]
    (q : ∀ i, V i → F₂) :
    gaussSum (fun x : ∀ i, V i ↦ ∑ i, q i (x i)) = ∏ i, gaussSum (q i) := by
  classical
  simp only [gaussSum, sign_sum]
  exact (Fintype.prod_sum (fun i x ↦ sign (q i x))).symm



variable {V : Type*} [AddCommGroup V] [Module F₂ V]


theorem quadratic_plane_formula (q : QuadraticForm F₂ (F₂ × F₂))
    (hcross : q.polarBilin (1, 0) (0, 1) = 1) (p : F₂ × F₂) :
    q p = plane (q (1, 0)) (q (0, 1)) p := by
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
  have hc : QuadraticMap.polar q (1, 0) (0, 1) = 1 := hcross
  conv_lhs => rw [hp, QuadraticMap.map_add q, q.map_smul, q.map_smul,
    q.polar_smul_left, q.polar_smul_right, hc]
  simp only [plane_apply, smul_eq_mul]
  ring

end NoExoticSixSphere.Arf
