module

public import Wikipedia.NoExoticSixSphere.StableCollapseChoiceIndependence
public import Wikipedia.NoExoticSixSphere.StableSixSphereCollapseRepresentative
public import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

@[expose] public section

/-!
# The actual canonical tube collapse of a regular sphere-map fiber

The chosen tube is the original canonical framed tube of the stereographic
embedding, with the frame induced by the original regular equations. Its
collapse is now compared to the original sphere map at every finite
suspension stage. The normal-coordinate comparison constructs the homotopy;
it is not an extra premise about the chosen tube.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n))
  (hf : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x))
  (a : Sphere (n + k)) (ha : f a = -b)
  [Nonempty {x : Sphere (n + k) // f x = b}]

def tubeCollapseData :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (embedding f hf b hreg a ha).FramedCollapseData (frame f hf b hreg a ha) := by
  letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  letI := regularFiber_isManifold f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  letI := RegularSphereFiber.fiber_compact f b
  exact (embedding f hf b hreg a ha).framedCollapseData (frame f hf b hreg a ha)


end NoExoticSixSphere.StereographicFiber

namespace NoExoticSixSphere.StableSixSphereMaps


end NoExoticSixSphere.StableSixSphereMaps
