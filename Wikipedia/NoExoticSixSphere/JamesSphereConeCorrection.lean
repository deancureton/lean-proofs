module

public import Wikipedia.NoExoticSixSphere.JamesSphereConeExcision
public import Wikipedia.NoExoticSixSphere.PuncturedCellDeformationSupport

@[expose] public section

/-!
# Correcting a face without hitting the other chosen cell point

On the doubly punctured cone model, the first-cell deformation takes a
point into the cone disk while staying away from the chosen cone point.
It fixes points already in that disk. The second-cell deformation keeps
the cone image invariant and ends there on the original one-letter
subspace of the James stage. These actual continuous families supply
the supported bottom correction in the relative excision argument.
-/

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

theorem secondPoint_not_firstCell (n : ℕ) (q : ConeCoordinates n) (hq : ‖q‖ < 1) :
    cone n (PuncturedCellAttachment.point q hq) ∉ Set.range (firstCell n) := by
  rintro ⟨d, hd⟩
  exact PushoutOutsideAttachment.ne_other_of_notMem_range (isPushout n)
    (PuncturedCellAttachment.point_not_boundary q hq) (Cell.closedPresentation n 2 d) hd.symm

variable (n : ℕ) (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
  (q : ConeCoordinates n) (hq : ‖q‖ < 1)

abbrev DoublePunctured := {z : Space n //
  z ∈ firstPunctured n p hp ∧ z ∈ secondPunctured n q hq}

def toFirstPunctured : C(DoublePunctured n p hp q hq, firstPunctured n p hp) :=
  ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def toSecondPunctured : C(DoublePunctured n p hp q hq, secondPunctured n q hq) :=
  ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

variable (hn : 0 < n)

theorem firstDeformation_avoids_second (t : I) (x : DoublePunctured n p hp q hq) :
    (firstPunctureDeformation n hn p hp (t, toFirstPunctured n p hp q hq x)).val ≠
      cone n (PuncturedCellAttachment.point q hq) :=
  PuncturedCellAttachment.deformation_avoids_of_not_mem_cell (first_isPushout n hn) p hp
    (cone n (PuncturedCellAttachment.point q hq)) (secondPoint_not_firstCell n q hq)
    t (toFirstPunctured n p hp q hq x) x.property.2

def firstCorrection : C(I × DoublePunctured n p hp q hq, secondPunctured n q hq) :=
  ⟨fun z ↦ ⟨(firstPunctureDeformation n hn p hp
      (z.1, toFirstPunctured n p hp q hq z.2)).val,
    firstDeformation_avoids_second n p hp q hq hn z.1 z.2⟩,
    (continuous_subtype_val.comp ((firstPunctureDeformation n hn p hp).continuous.comp
      (continuous_fst.prodMk ((toFirstPunctured n p hp q hq).continuous.comp
        continuous_snd)))).subtype_mk _⟩




omit p hp q hq hn in
theorem secondDeformation_mem_cone (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    (t : I) (x : secondPunctured n q hq) (hx : x.val ∈ Set.range (cone n)) :
    (secondPunctureDeformation n q hq (t, x)).val ∈ Set.range (cone n) :=
  PuncturedCellAttachment.deformation_cell_mem (isPushout n) q hq t x hx

omit p hp q hq hn in
theorem secondRetraction_mem_lower (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    (x : secondPunctured n q hq) (hx : x.val ∈ Set.range (cone n)) :
    secondPunctureRetraction n q hq x ∈ StageAttachment.lower n 1 := by
  have hm := secondDeformation_mem_cone n q hq 1 x hx
  have he := congrArg (fun y : secondPunctured n q hq ↦ y.val)
    ((secondPunctureDeformation n q hq).map_one_left x)
  change (secondPunctureDeformation n q hq (1, x)).val =
    base n (secondPunctureRetraction n q hq x) at he
  rw [he] at hm
  exact (base_mem_cone_iff n _).mp hm

end NoExoticSixSphere.JamesSphere.SecondStageCone
