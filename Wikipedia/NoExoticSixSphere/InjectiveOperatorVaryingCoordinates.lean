module

public import Wikipedia.NoExoticSixSphere.InjectiveOperatorLinearCoordinates

@[expose] public section

/-!
# Coordinate changes extending over the four-ball preserve operator parity

A continuously varying homeomorphism of the injective-operator space, with
continuous inverse, transports extensions over the actual disk in both
directions. In particular this applies to linear coordinate changes that
extend over the disk. Arbitrary sphere-dependent changes are not covered.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization Topology
open Wikipedia.HopfProblem.DegreeCollapse

theorem sphereParity_diskCoordinates (r : ℕ)
    (H : DiskCylinder.Disk (E := Vector 4) →
      (Space (3 + (r + 2)) (r + 2) ≃ₜ Space (3 + (r + 2)) (r + 2)))
    (hH : Continuous (fun q : DiskCylinder.Disk (E := Vector 4) ×
      Space (3 + (r + 2)) (r + 2) ↦ H q.1 q.2))
    (hHinv : Continuous (fun q : DiskCylinder.Disk (E := Vector 4) ×
      Space (3 + (r + 2)) (r + 2) ↦ (H q.1).symm q.2))
    (f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2)))
    (hfg : ∀ s, g s = H (DiskCylinder.boundaryToDisk s) (f s)) :
    sphereParity r g = sphereParity r f := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereParity_zero_iff_extension, sphereParity_zero_iff_extension]
  constructor
  · rintro ⟨G, hG⟩
    refine ⟨⟨fun x ↦ (H x).symm (G x),
      hHinv.comp (continuous_id.prodMk G.continuous)⟩, ?_⟩
    intro s
    change (H (DiskCylinder.boundaryToDisk s)).symm (G (DiskCylinder.boundaryToDisk s)) = f s
    rw [hG, hfg]
    exact (H (DiskCylinder.boundaryToDisk s)).symm_apply_apply (f s)
  · rintro ⟨F, hF⟩
    refine ⟨⟨fun x ↦ H x (F x), hH.comp (continuous_id.prodMk F.continuous)⟩, ?_⟩
    intro s
    change H (DiskCylinder.boundaryToDisk s) (F (DiskCylinder.boundaryToDisk s)) = g s
    rw [hF, hfg]


end NoExoticSixSphere.Stiefel.Monomorphism
