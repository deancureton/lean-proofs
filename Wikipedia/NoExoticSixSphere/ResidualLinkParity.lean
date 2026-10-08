module

public import Wikipedia.NoExoticSixSphere.ResidualLinkHomotopy
public import Wikipedia.NoExoticSixSphere.ResidualModelCoordinates

@[expose] public section

/-!
# Parity one for the actual local residual-coordinate operator link

The actual link is homotopic through injective operators to its constant
leading-block model. A fixed general linear source change identifies that
model exactly with the checked unit cusp frame. Thus the original operator
link has parity one, and cannot extend through injective operators over a ball.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization

theorem sphereParity_inclusion (r : ℕ)
    (f : C(Sphere 3, Stiefel.Space (3 + (r + 2)) (r + 2))) :
    sphereParity r ((inclusion (3 + (r + 2)) (r + 2)).comp f) =
      sphereThirdObstruction r f := by
  unfold sphereParity
  apply congrArg (sphereThirdObstruction r)
  apply ContinuousMap.ext
  intro q
  exact normalize_inclusion (f q)

end NoExoticSixSphere.Stiefel.Monomorphism

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne CorankOneEuclidean Stiefel
open Wikipedia.HopfProblem.DegreeCollapse

theorem constantModel_parity (a : Vector 2 ≃L[ℝ] Vector 2) {ε : ℝ} (hε : 0 < ε) :
    Monomorphism.sphereParity 1 (constantModel a hε) = 1 := by
  have he := Monomorphism.sphereParity_linearCoordinates 1
    (ContinuousLinearEquiv.refl ℝ (Vector 6)) (normalizingSource a ε hε.ne')
    (constantModel a hε)
  rw [constantModel_change a hε, Monomorphism.sphereParity_inclusion] at he
  exact he.symm.trans WhitneyCusp.simpleFrame_parity

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {D : X → BlockMap (Vector 2) (Vector 4)}

theorem Data.center_parity (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (d.centerOperators hε hball) = 1 := by
  obtain ⟨a, ha⟩ := d.leading_center hε hball
  have he : d.centerOperators hε hball = constantModel a hε := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change CorankOneEuclidean.toEuclidean
      (diagonal (leading (D (d.coord.symm 0))) (scaledParameter ε q)) =
      CorankOneEuclidean.toEuclidean (diagonal a.toContinuousLinearMap (scaledParameter ε q))
    rw [← ha]
  rw [he]
  exact constantModel_parity a hε

theorem Data.link_parity (d : Data D) (hD : Continuous D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    Monomorphism.sphereParity 1 (d.linkOperators hD hε hball) = 1 :=
  (d.link_parity_eq_center hD hε hball).trans (d.center_parity hε hball)



end NoExoticSixSphere.ResidualCoordinates
