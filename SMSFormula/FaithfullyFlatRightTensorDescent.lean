import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import SMSFormula.PrincipalLocalizationAmbientBaseChange

/-!
# Faithfully flat descent in the right-tensor orientation

Mathlib reflects bijectivity through faithful flatness using the left tensor
product.  This file transports that theorem through the tensor commutativity
equivalences to the right-tensor base-change map used by the Spin invariant
quotient.
-/

noncomputable section

open TensorProduct

universe u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Algebra.TensorProduct

variable {R K A B : Type u} [CommRing R] [CommRing K] [Algebra R K]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Module.FaithfullyFlat R K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If a right-tensor scalar extension is bijective, then the original
algebra homomorphism is bijective, provided the scalar extension is faithfully
flat. -/
theorem bijective_of_mapRightAlgHom (f : A →ₐ[R] B)
    (h : Function.Bijective (mapRightAlgHom (K := K) f)) :
    Function.Bijective f := by
  let eA := Algebra.TensorProduct.commRight R K A
  let eB := Algebra.TensorProduct.commRight R K B
  have hmap_eq_lTensor :
      (Algebra.TensorProduct.map (AlgHom.id K K) f).toLinearMap =
        f.toLinearMap.lTensor K := by
    ext k a
    simp [LinearMap.lTensor_tmul]
  have hmap : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id K K) f) := by
    have hconj : Function.Bijective
        (fun x : K ⊗[R] A =>
          eB.symm (mapRightAlgHom (K := K) f (eA x))) :=
      eB.symm.bijective.comp (h.comp eA.bijective)
    simpa [mapRightAlgHom, eA, eB] using hconj
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    R K f.toLinearMap).mp
  rw [← hmap_eq_lTensor]
  exact hmap

end Algebra.TensorProduct
