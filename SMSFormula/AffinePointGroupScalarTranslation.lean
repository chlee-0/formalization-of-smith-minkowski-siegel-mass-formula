import SMSFormula.AffinePointGroupHopf

/-!
# Scalar-extended translations from affine-point group data

For natural group structures on `Hom_R(A,-)`, a `K`-valued point acts by
left translation on the right scalar extension `A tensor_R K`.  This file
constructs the contravariant coordinate algebra homomorphism by extending
the translated universal point and proves that translation by the inverse
point is its inverse.

The construction is generic and uses only the group-valued functor data.  It
does not identify or transport any particular principal-open subscheme.
-/

noncomputable section

open TensorProduct

namespace AffinePointGroupData

variable {R A K : Type} [CommRing R] [CommRing A] [CommRing K]
  [Algebra R A] [Algebra R K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The constant `A`-point of `A tensor_R K` induced by a `K`-point. -/
def rightTensorConstantPoint (G : AffinePointGroupData R A)
    (p : A →ₐ[R] K) : A →ₐ[R] A ⊗[R] K :=
  G.map (Algebra.TensorProduct.includeRight : K →ₐ[R] A ⊗[R] K) p

/-- The universal `A`-point of the right scalar extension. -/
def rightTensorUniversalPoint : A →ₐ[R] A ⊗[R] K :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := K)

/-- Inverse of a point in the group supplied by the affine-point data. -/
def pointInv (G : AffinePointGroupData R A) (p : A →ₐ[R] K) : A →ₐ[R] K := by
  letI := G.pointGroup K
  exact p⁻¹

@[simp]
theorem pointInv_inv (G : AffinePointGroupData R A) (p : A →ₐ[R] K) :
    G.pointInv (G.pointInv p) = p := by
  letI := G.pointGroup K
  simp [pointInv]

/-- The universal point after left multiplication by a constant point. -/
def rightTensorLeftTranslatedPoint (G : AffinePointGroupData R A)
    (p : A →ₐ[R] K) : A →ₐ[R] A ⊗[R] K := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  exact G.rightTensorConstantPoint p * rightTensorUniversalPoint

/-- Pullback by left translation on the right scalar extension. -/
def rightTensorLeftTranslationAlgHom (G : AffinePointGroupData R A)
    (p : A →ₐ[R] K) : A ⊗[R] K →ₐ[K] A ⊗[R] K := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  let t : A ⊗[R] K →ₐ[R] A ⊗[R] K := Algebra.TensorProduct.lift
    (G.rightTensorLeftTranslatedPoint p)
    (Algebra.TensorProduct.includeRight : K →ₐ[R] A ⊗[R] K)
    (fun _ _ => Commute.all _ _)
  exact
    { toRingHom := t.toRingHom
      commutes' := by
        intro k
        change t (Algebra.TensorProduct.includeRight k) =
          Algebra.TensorProduct.includeRight k
        simp [t] }

@[simp]
theorem rightTensorLeftTranslationAlgHom_tmul
    (G : AffinePointGroupData R A) (p : A →ₐ[R] K) (a : A) (k : K) :
    G.rightTensorLeftTranslationAlgHom p (a ⊗ₜ[R] k) =
      G.rightTensorLeftTranslatedPoint p a *
        (Algebra.TensorProduct.includeRight k : A ⊗[R] K) := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  simp [rightTensorLeftTranslationAlgHom]

@[simp]
theorem rightTensorLeftTranslationAlgHom_includeRight
    (G : AffinePointGroupData R A) (p : A →ₐ[R] K) (k : K) :
    G.rightTensorLeftTranslationAlgHom p
        (Algebra.TensorProduct.includeRight k : A ⊗[R] K) =
      Algebra.TensorProduct.includeRight k := by
  simpa only [Algebra.TensorProduct.includeRight_apply, map_one, one_mul] using
    G.rightTensorLeftTranslationAlgHom_tmul p (1 : A) k

theorem rightTensorLeftTranslation_restrict_comp_constant
    (G : AffinePointGroupData R A) (p q : A →ₐ[R] K) :
    ((G.rightTensorLeftTranslationAlgHom p).restrictScalars R).comp
        (G.rightTensorConstantPoint q) =
      G.rightTensorConstantPoint q := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  apply AlgHom.ext
  intro a
  simp only [rightTensorConstantPoint, G.map_apply, AlgHom.comp_apply]
  exact G.rightTensorLeftTranslationAlgHom_includeRight p (q a)

theorem rightTensorLeftTranslation_restrict_comp_universal
    (G : AffinePointGroupData R A) (p : A →ₐ[R] K) :
    ((G.rightTensorLeftTranslationAlgHom p).restrictScalars R).comp
        rightTensorUniversalPoint =
      G.rightTensorLeftTranslatedPoint p := by
  apply AlgHom.ext
  intro a
  calc
    G.rightTensorLeftTranslationAlgHom p
        (rightTensorUniversalPoint a) =
      G.rightTensorLeftTranslationAlgHom p (a ⊗ₜ[R] (1 : K)) := by rfl
    _ = G.rightTensorLeftTranslatedPoint p a *
        Algebra.TensorProduct.includeRight (1 : K) :=
      G.rightTensorLeftTranslationAlgHom_tmul p a 1
    _ = G.rightTensorLeftTranslatedPoint p a := by rw [map_one, mul_one]

theorem rightTensorLeftTranslationAlgHom_comp_inv
    (G : AffinePointGroupData R A) (p : A →ₐ[R] K) :
    (G.rightTensorLeftTranslationAlgHom p).comp
        (rightTensorLeftTranslationAlgHom G (G.pointInv p)) =
      AlgHom.id K (A ⊗[R] K) := by
  letI := G.pointGroup K
  letI := G.pointGroup (A ⊗[R] K)
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a k =>
      rw [AlgHom.comp_apply,
        G.rightTensorLeftTranslationAlgHom_tmul,
        map_mul,
        G.rightTensorLeftTranslationAlgHom_includeRight]
      change G.rightTensorLeftTranslationAlgHom p
        (G.rightTensorLeftTranslatedPoint (G.pointInv p) a) *
          Algebra.TensorProduct.includeRight k = a ⊗ₜ[R] k
      have hmap := map_mul
        (G.map ((G.rightTensorLeftTranslationAlgHom p).restrictScalars R))
        (G.rightTensorConstantPoint (G.pointInv p))
        (rightTensorUniversalPoint : A →ₐ[R] A ⊗[R] K)
      simp only [G.map_apply] at hmap
      rw [G.rightTensorLeftTranslation_restrict_comp_constant,
        G.rightTensorLeftTranslation_restrict_comp_universal] at hmap
      have hmapa := DFunLike.congr_fun hmap a
      change G.rightTensorLeftTranslationAlgHom p
          (G.rightTensorLeftTranslatedPoint (G.pointInv p) a) =
        (G.rightTensorConstantPoint (G.pointInv p) *
          G.rightTensorLeftTranslatedPoint p) a at hmapa
      rw [hmapa]
      have hc := map_mul
        (G.map (Algebra.TensorProduct.includeRight : K →ₐ[R] A ⊗[R] K))
        (G.pointInv p) p
      change G.rightTensorConstantPoint (G.pointInv p * p) =
        G.rightTensorConstantPoint (G.pointInv p) *
          G.rightTensorConstantPoint p at hc
      change (G.rightTensorConstantPoint (G.pointInv p) *
          (G.rightTensorConstantPoint p *
            (rightTensorUniversalPoint : A →ₐ[R] A ⊗[R] K))) a *
          Algebra.TensorProduct.includeRight k = a ⊗ₜ[R] k
      rw [← mul_assoc]
      rw [← hc]
      change (G.rightTensorConstantPoint (p⁻¹ * p) *
          (rightTensorUniversalPoint : A →ₐ[R] A ⊗[R] K)) a *
          Algebra.TensorProduct.includeRight k = a ⊗ₜ[R] k
      simp [rightTensorConstantPoint, rightTensorUniversalPoint]

theorem rightTensorLeftTranslationAlgHom_inv_comp
    (G : AffinePointGroupData R A) (p : A →ₐ[R] K) :
    (rightTensorLeftTranslationAlgHom G (G.pointInv p)).comp
        (G.rightTensorLeftTranslationAlgHom p) =
      AlgHom.id K (A ⊗[R] K) := by
  simpa only [G.pointInv_inv] using
    G.rightTensorLeftTranslationAlgHom_comp_inv (G.pointInv p)

/-- Left translation is an algebra automorphism of the scalar-extended
coordinate ring. -/
def rightTensorLeftTranslationAlgEquiv (G : AffinePointGroupData R A)
    (p : A →ₐ[R] K) : A ⊗[R] K ≃ₐ[K] A ⊗[R] K :=
  AlgEquiv.ofAlgHom
    (G.rightTensorLeftTranslationAlgHom p)
    (G.rightTensorLeftTranslationAlgHom (G.pointInv p))
    (G.rightTensorLeftTranslationAlgHom_comp_inv p)
    (G.rightTensorLeftTranslationAlgHom_inv_comp p)

end AffinePointGroupData
