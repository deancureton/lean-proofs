module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Subpath

@[expose] public section

/-!
# Simple connectivity from an open cover

A space covered by simply connected open sets is simply connected if the sets
contain a common point and their pairwise intersections are path connected.
The proof uses actual endpoint-preserving path homotopies, not a presentation
of the fundamental group taken as an additional hypothesis.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem

namespace SimplyConnectedCover

variable {X : Type*} [TopologicalSpace X]

/-- Paths lying in a simply connected subspace are homotopic in the ambient space. -/
theorem homotopic_of_mem {s : Set X} (hs : IsSimplyConnected s)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    Path.Homotopic p q := by
  let : SimplyConnectedSpace s := hs
  have hx : x ∈ s := by simpa using hp 0
  have hy : y ∈ s := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let q' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have h := (SimplyConnectedSpace.paths_homotopic p' q').map
    (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap s X)
  have hp' : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq' : q'.map continuous_subtype_val = q := by ext t; rfl
  exact hp' ▸ hq' ▸ h

/-- Concatenating two paths that lie in a set stays in that set. -/
theorem trans_mem {s : Set X} {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) : ∀ t, p.trans q t ∈ s := by
  apply range_subset_iff.mp
  rw [Path.trans_range]
  exact union_subset (range_subset_iff.mpr hp) (range_subset_iff.mpr hq)

/-- The path from the common point chosen inside a particular member of the cover. -/
def chartPath {ι : Type*} (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i))
    (o : X) (ho : ∀ i, o ∈ U i) (i : ι) (x : X) (hx : x ∈ U i) : Path o x :=
  ((hs i).isPathConnected.joinedIn o (ho i) x hx).somePath

theorem chartPath_mem {ι : Type*} (U : ι → Set X) (hs : ∀ i, IsSimplyConnected (U i))
    (o : X) (ho : ∀ i, o ∈ U i) (i : ι) (x : X) (hx : x ∈ U i) (t : I) :
    chartPath U hs o ho i x hx t ∈ U i :=
  JoinedIn.somePath_mem _ t

/-- The choice of cover member does not affect the ambient homotopy class. -/
theorem chartPath_homotopic {ι : Type*} (U : ι → Set X)
    (hs : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j))
    (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    Path.Homotopic (chartPath U hs o ho i x hi) (chartPath U hs o ho j x hj) := by
  let h := (hinter i j).joinedIn o ⟨ho i, ho j⟩ x ⟨hi, hj⟩
  exact (homotopic_of_mem (hs i) _ h.somePath
    (chartPath_mem U hs o ho i x hi) (fun t => (h.somePath_mem t).1)).trans
    (homotopic_of_mem (hs j) h.somePath _
      (fun t => (h.somePath_mem t).2) (chartPath_mem U hs o ho j x hj))

open Path.Homotopic.Quotient

/-- Transport commutes with composition of path classes. -/
theorem quotient_cast_trans {o x y o' x' y' : X}
    (p : Path.Homotopic.Quotient o x) (q : Path.Homotopic.Quotient x y)
    (ho : o' = o) (hx : x' = x) (hy : y' = y) :
    (p.trans q).cast ho hy = (p.cast ho hx).trans (q.cast hx hy) := by
  cases ho
  cases hx
  cases hy
  simp

theorem quotient_cast_section {o : X} (F : ∀ z, Path.Homotopic.Quotient o z)
    {x y : X} (h : x = y) : (F y).cast rfl h = F x := by
  cases h
  simp

/-- Remove the harmless endpoint transports introduced by a full subpath. -/
theorem section_subpath_zero_one {o x y : X}
    (F : ∀ z, Path.Homotopic.Quotient o z) (p : Path x y)
    (h : trans (F (p 0)) (mk (p.subpath 0 1)) = F (p 1)) :
    trans (F x) (mk p) = F y := by
  have hp : (mk (p.subpath 0 1)).cast p.source.symm p.target.symm = mk p := by
    rw [← mk_cast, Path.subpath_zero_one]
    rfl
  have h' := congrArg (fun q : Path.Homotopic.Quotient o (p 1) =>
    q.cast rfl p.target.symm) h
  rw [quotient_cast_trans _ _ rfl p.source.symm p.target.symm,
    quotient_cast_section F p.source.symm, hp,
    quotient_cast_section F p.target.symm] at h'
  exact h'

/-- A homotopy-class section that is compatible with paths in each open cover
member is compatible with every path. -/
theorem section_trans_of_open_cover {ι : Type*} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (o : X) (F : ∀ x, Path.Homotopic.Quotient o x)
    (hF : ∀ i {x y : X} (p : Path x y), (∀ t, p t ∈ U i) →
      trans (F x) (mk p) = F y)
    {x y : X} (p : Path x y) : trans (F x) (mk p) = F y := by
  have hpre : univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← preimage_iUnion, hcover, preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hopen i).preimage p.continuous) hpre
  have hwalk : ∀ k : ℕ,
      trans (F (p 0)) (mk (p.subpath 0 (t k))) = F (p (t k)) := by
    intro k
    induction k with
    | zero => rw [ht0, Path.subpath_self, mk_refl, trans_refl]
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : ∀ s, p.subpath (t k) (t (k + 1)) s ∈ U i := by
        apply range_subset_iff.mp
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact image_subset_iff.mpr hi
      have hconcat : trans (mk (p.subpath 0 (t k)))
          (mk (p.subpath (t k) (t (k + 1)))) = mk (p.subpath 0 (t (k + 1))) := by
        rw [← mk_trans, eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      calc
        trans (F (p 0)) (mk (p.subpath 0 (t (k + 1)))) =
            trans (trans (F (p 0)) (mk (p.subpath 0 (t k))))
              (mk (p.subpath (t k) (t (k + 1)))) := by
                rw [trans_assoc, hconcat]
        _ = trans (F (p (t k))) (mk (p.subpath (t k) (t (k + 1)))) := by rw [ih]
        _ = F (p (t (k + 1))) := hF i _ hmem
  have h := hwalk n
  rw [hn n le_rfl] at h
  exact section_subpath_zero_one F p h

end SimplyConnectedCover


end Wikipedia.HopfProblem
