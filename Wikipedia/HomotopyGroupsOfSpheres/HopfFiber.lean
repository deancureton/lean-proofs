module

public import Wikipedia.HomotopyGroupsOfSpheres.HopfDirectAction

@[expose] public section

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfDirect

theorem hopf_smul_injective (v : Total) :
    Function.Injective (fun u : Circle ↦ u • v) := sphereAction_injective v

theorem hopf_eq_iff (v w : Total) :
    sphereMap v = sphereMap w ↔ ∃ u : Circle, u • w = v := sphereMap_eq_iff v w

def hopfFiberHomeomorph (v : Total) :
    Circle ≃ₜ {w : Total // sphereMap w = sphereMap v} := fiberHomeomorph v

@[simp] theorem hopfFiberHomeomorph_apply (v : Total) (u : Circle) :
    (hopfFiberHomeomorph v u).val = u • v := rfl

@[simp] theorem hopfFiberHomeomorph_one (v : Total) :
    hopfFiberHomeomorph v 1 = ⟨v, rfl⟩ := fiberHomeomorph_one v

end Wikipedia.HomotopyGroupsOfSpheres
