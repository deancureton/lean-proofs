module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.RegularSphereFiberTargetChange
public import Wikipedia.NoExoticSixSphere.RegularFiberStableSphereArfObstruction

@[expose] public section

/-!
# Different regular values do not prevent the original Arf obstruction

Align only the right map by a target diffeomorphism homotopic to the
identity. Its genuine native fiber is unchanged up to the constructed
point-preserving diffeomorphism. The original left map and its original
Arf invariant are not changed at all. The common-value theorem then
applies to the actual finite suspended homotopy.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSphereFiber

open SphereMapSuspension

variable {m n : ℕ} (f g : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hg : ContMDiff (𝓡 m) (𝓡 n) ∞ g)
  (b c : Sphere n)
  (hregf : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (hregg : ∀ x, g x = c → Surjective (mfderiv (𝓡 m) (𝓡 n) g x))
  (hd : m = n + 6) (hn : 0 < n) (a : Sphere m)
  [SimplyConnectedSpace {x : Sphere m // f x = b}]
  (x : {x : Sphere m // f x = b}) [Subsingleton (π_ 2 {x : Sphere m // f x = b} x)]

include hg hregg hn

theorem geometricArf_eq_zero_of_suspended_homotopy_sixSphere_at
    (hX : {x : Sphere m // g x = c} ≃ₜ Sphere 6) (j : ℕ)
    (hH : (iterate f j).Homotopic (iterate g j)) :
    letI := regularFiberAtlas f hf b hregf 6 (by simpa using hd);
    letI := regularFiber_isManifold f hf b hregf 6 _;
    letI := fiber_compact f b;
    ∀ r : (embedding f hf b hregf 6 hd).TubularRetraction,
      GeometricArf.invariant (embedding f hf b hregf 6 hd) (frame f hf b hregf 6 hd a) r x = 0 := by
  let := regularFiberAtlas g hg c hregg 6 (by simpa using hd)
  obtain ⟨G, hG, hregG, HG, D, _⟩ := exists_regular_value_alignment g hg c b hregg hn 6 hd
  let := regularFiberAtlas G hG b hregG 6 (by simpa using hd)
  exact geometricArf_eq_zero_of_suspended_homotopy_sixSphere
    f G hf hG b hregf hregG hd a x (D.symm.toHomeomorph.trans hX) j
    (hH.trans (iterate_homotopic HG j))


end NoExoticSixSphere.RegularSphereFiber
