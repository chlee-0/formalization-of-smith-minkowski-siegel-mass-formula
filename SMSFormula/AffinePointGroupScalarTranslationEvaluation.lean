import SMSFormula.AffinePointGroupScalarTranslation
import SMSFormula.FiniteTypeAlgClosedPointLift

/-!
# Evaluating scalar-extended affine-group translations

The canonical point of a right tensor scalar extension evaluates coordinate
left translation by `p` at `q` as the point product `p * q`.  This is the
coordinate identity needed to show that translates of one principal patch
contain prescribed algebraically closed points.
-/

noncomputable section

open TensorProduct

namespace AffinePointGroupData

variable {R A K : Type} [CommRing R] [CommRing A] [CommRing K]
  [Algebra R A] [Algebra R K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Evaluation of the right-tensor translation by `p` at the right-tensor
point induced by `q` is the right-tensor point induced by `p * q`. -/
theorem rightTensorPoint_comp_rightTensorLeftTranslationAlgHom
    (G : AffinePointGroupData R A) (p q : A →ₐ[R] K) :
    letI := G.pointGroup K
    (Algebra.TensorProduct.rightTensorPoint q).comp
          (G.rightTensorLeftTranslationAlgHom p) =
        Algebra.TensorProduct.rightTensorPoint (p * q) := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  let e : A ⊗[R] K →ₐ[R] K :=
    (Algebra.TensorProduct.rightTensorPoint q).restrictScalars R
  have hconst : e.comp (G.rightTensorConstantPoint p) = p := by
    apply AlgHom.ext
    intro a
    simp [e, rightTensorConstantPoint, G.map_apply]
  have huniv : e.comp rightTensorUniversalPoint = q := by
    apply AlgHom.ext
    intro a
    simp [e, rightTensorUniversalPoint]
  have hmap := map_mul (G.map e)
    (G.rightTensorConstantPoint p)
    (rightTensorUniversalPoint : A →ₐ[R] A ⊗[R] K)
  simp only [G.map_apply] at hmap
  change e.comp (G.rightTensorConstantPoint p * rightTensorUniversalPoint) =
      e.comp (G.rightTensorConstantPoint p) * e.comp rightTensorUniversalPoint at hmap
  rw [hconst, huniv] at hmap
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a k =>
      rw [AlgHom.comp_apply, G.rightTensorLeftTranslationAlgHom_tmul,
        map_mul, Algebra.TensorProduct.rightTensorPoint_tmul]
      have ha := DFunLike.congr_fun hmap a
      change e (G.rightTensorLeftTranslatedPoint p a) = (p * q) a at ha
      change e (G.rightTensorLeftTranslatedPoint p a) *
          e (Algebra.TensorProduct.includeRight k) = (p * q) a * k
      rw [ha]
      simp [e]

/-- Translation by `q * p⁻¹` carries the point `p` to `q`; contravariantly,
evaluating the inverse-transformed coordinate at `q` recovers evaluation at
`p`. -/
theorem rightTensorPoint_leftTranslationAlgEquiv_symm_apply
    (G : AffinePointGroupData R A) (p q : A →ₐ[R] K) (d : A ⊗[R] K) :
    letI := G.pointGroup K
    Algebra.TensorProduct.rightTensorPoint q
        ((G.rightTensorLeftTranslationAlgEquiv (q * p⁻¹)).symm d) =
      Algebra.TensorProduct.rightTensorPoint p d := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  let g : A →ₐ[R] K := q * p⁻¹
  have h := DFunLike.congr_fun
    (G.rightTensorPoint_comp_rightTensorLeftTranslationAlgHom
      (G.pointInv g) q) d
  change Algebra.TensorProduct.rightTensorPoint q
      ((G.rightTensorLeftTranslationAlgEquiv g).symm d) =
    Algebra.TensorProduct.rightTensorPoint (g⁻¹ * q) d at h
  calc
    Algebra.TensorProduct.rightTensorPoint q
        ((G.rightTensorLeftTranslationAlgEquiv (q * p⁻¹)).symm d) =
      Algebra.TensorProduct.rightTensorPoint (g⁻¹ * q) d := h
    _ = Algebra.TensorProduct.rightTensorPoint p d := by simp [g]

end AffinePointGroupData
