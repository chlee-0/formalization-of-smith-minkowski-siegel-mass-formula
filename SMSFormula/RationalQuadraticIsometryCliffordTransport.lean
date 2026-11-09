import SMSFormula.RationalQuadraticSpaceAnisotropicPresentationTopology

/-!
# Clifford transport along rational quadratic isometries

A rational quadratic isometry between two native matrix presentations induces
an equivalence between their coordinate Clifford algebras after every
commutative rational base change.  This file constructs that equivalence on
the literal tensor-product coordinate carriers and proves its exact formulas
on pure tensors and Clifford generators.  It also proves compatibility with
the coordinate grade involution and reverse anti-involution.

This is the algebraic prerequisite for transporting intrinsic `GSpin` points
between presentations.  No group, topology, Haar measure, shell measure, or
orbit kernel is transported here.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

section Clifford

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The coordinate Clifford-algebra homomorphism obtained by applying the
rational Clifford isometry in the second tensor factor. -/
def rationalIsometryCliffordBaseChangeAlgHom :
    U.cliffordCoordinateBaseChangeAlgebra A →ₐ[A]
      V.cliffordCoordinateBaseChangeAlgebra A :=
  Algebra.TensorProduct.map (AlgHom.id A A)
    (CliffordAlgebra.equivOfIsometry e).toAlgHom

@[simp]
theorem rationalIsometryCliffordBaseChangeAlgHom_tmul
    (a : A) (z : CliffordAlgebra U.quadraticForm) :
    rationalIsometryCliffordBaseChangeAlgHom U V e A (a ⊗ₜ[ℚ] z) =
      a ⊗ₜ[ℚ] CliffordAlgebra.equivOfIsometry e z := by
  simp [rationalIsometryCliffordBaseChangeAlgHom]

/-- The inverse tensor-factor homomorphism induced by the inverse rational
quadratic isometry. -/
def rationalIsometryCliffordBaseChangeInvAlgHom :
    V.cliffordCoordinateBaseChangeAlgebra A →ₐ[A]
      U.cliffordCoordinateBaseChangeAlgebra A :=
  rationalIsometryCliffordBaseChangeAlgHom V U e.symm A

private theorem rationalIsometryCliffordBaseChange_leftInverse :
    Function.LeftInverse
      (rationalIsometryCliffordBaseChangeInvAlgHom U V e A)
      (rationalIsometryCliffordBaseChangeAlgHom U V e A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      rw [rationalIsometryCliffordBaseChangeAlgHom_tmul]
      change rationalIsometryCliffordBaseChangeAlgHom V U e.symm A
        (a ⊗ₜ[ℚ] CliffordAlgebra.equivOfIsometry e z) = _
      rw [rationalIsometryCliffordBaseChangeAlgHom_tmul]
      congr 1
      rw [← CliffordAlgebra.equivOfIsometry_symm]
      exact (CliffordAlgebra.equivOfIsometry e).symm_apply_apply z

private theorem rationalIsometryCliffordBaseChange_rightInverse :
    Function.RightInverse
      (rationalIsometryCliffordBaseChangeInvAlgHom U V e A)
      (rationalIsometryCliffordBaseChangeAlgHom U V e A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      change rationalIsometryCliffordBaseChangeAlgHom U V e A
        (rationalIsometryCliffordBaseChangeAlgHom V U e.symm A
          (a ⊗ₜ[ℚ] z)) = _
      rw [rationalIsometryCliffordBaseChangeAlgHom_tmul,
        rationalIsometryCliffordBaseChangeAlgHom_tmul]
      congr 1
      rw [← CliffordAlgebra.equivOfIsometry_symm]
      exact (CliffordAlgebra.equivOfIsometry e).apply_symm_apply z

/-- The literal coordinate Clifford-algebra equivalence induced by a rational
quadratic isometry after base change. -/
def rationalIsometryCliffordBaseChangeAlgEquiv :
    U.cliffordCoordinateBaseChangeAlgebra A ≃ₐ[A]
      V.cliffordCoordinateBaseChangeAlgebra A :=
  AlgEquiv.ofBijective
    (rationalIsometryCliffordBaseChangeAlgHom U V e A)
    ⟨(rationalIsometryCliffordBaseChange_leftInverse U V e A).injective,
      (rationalIsometryCliffordBaseChange_rightInverse U V e A).surjective⟩

@[simp]
theorem rationalIsometryCliffordBaseChangeAlgEquiv_apply
    (z : U.cliffordCoordinateBaseChangeAlgebra A) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A z =
      rationalIsometryCliffordBaseChangeAlgHom U V e A z :=
  rfl

@[simp]
theorem rationalIsometryCliffordBaseChangeAlgEquiv_symm_apply
    (z : V.cliffordCoordinateBaseChangeAlgebra A) :
    (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).symm z =
      rationalIsometryCliffordBaseChangeInvAlgHom U V e A z := by
  apply (rationalIsometryCliffordBaseChangeAlgEquiv U V e A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (rationalIsometryCliffordBaseChange_rightInverse U V e A z).symm

@[simp]
theorem rationalIsometryCliffordBaseChangeAlgEquiv_tmul
    (a : A) (z : CliffordAlgebra U.quadraticForm) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A (a ⊗ₜ[ℚ] z) =
      a ⊗ₜ[ℚ] CliffordAlgebra.equivOfIsometry e z := by
  exact rationalIsometryCliffordBaseChangeAlgHom_tmul U V e A a z

/-- On a rational Clifford generator, coordinate transport is literally the
generator attached to the isometric rational vector. -/
@[simp]
theorem rationalIsometryCliffordBaseChangeAlgEquiv_tmul_ι
    (a : A) (v : Fin r → ℚ) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (a ⊗ₜ[ℚ] CliffordAlgebra.ι U.quadraticForm v) =
      a ⊗ₜ[ℚ] CliffordAlgebra.ι V.quadraticForm (e v) := by
  rw [rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
    CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  rfl

private theorem equivOfIsometry_involute
    (z : CliffordAlgebra U.quadraticForm) :
    CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.involute z) =
      CliffordAlgebra.involute (CliffordAlgebra.equivOfIsometry e z) := by
  induction z using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι v =>
      rw [CliffordAlgebra.involute_ι, map_neg,
        CliffordAlgebra.equivOfIsometry_apply,
        CliffordAlgebra.map_apply_ι, CliffordAlgebra.involute_ι]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem equivOfIsometry_reverse
    (z : CliffordAlgebra U.quadraticForm) :
    CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.reverse z) =
      CliffordAlgebra.reverse (CliffordAlgebra.equivOfIsometry e z) := by
  induction z using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι v =>
      rw [CliffordAlgebra.reverse_ι,
        CliffordAlgebra.equivOfIsometry_apply,
        CliffordAlgebra.map_apply_ι, CliffordAlgebra.reverse_ι]
  | mul x y hx hy =>
      rw [CliffordAlgebra.reverse.map_mul, map_mul, hx, hy]
      rw [map_mul, CliffordAlgebra.reverse.map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coordinate Clifford transport commutes with the grade involution. -/
theorem rationalIsometryCliffordBaseChangeAlgEquiv_involute
    (z : U.cliffordCoordinateBaseChangeAlgebra A) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (U.cliffordCoordinateBaseChangeInvolute A z) =
      V.cliffordCoordinateBaseChangeInvolute A
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      rw [U.cliffordCoordinateBaseChangeInvolute_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        V.cliffordCoordinateBaseChangeInvolute_tmul,
        equivOfIsometry_involute]

/-- Coordinate Clifford transport commutes with the reverse
anti-involution. -/
theorem rationalIsometryCliffordBaseChangeAlgEquiv_reverse
    (z : U.cliffordCoordinateBaseChangeAlgebra A) :
    rationalIsometryCliffordBaseChangeAlgEquiv U V e A
        (U.cliffordCoordinateBaseChangeReverse A z) =
      V.cliffordCoordinateBaseChangeReverse A
        (rationalIsometryCliffordBaseChangeAlgEquiv U V e A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      rw [U.cliffordCoordinateBaseChangeReverse_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        rationalIsometryCliffordBaseChangeAlgEquiv_tmul,
        V.cliffordCoordinateBaseChangeReverse_tmul,
        equivOfIsometry_reverse]

end Clifford

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The Clifford coordinate equivalence attached to a supplied anisotropic
block presentation. -/
abbrev blockToAmbientCliffordBaseChangeAlgEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :=
  rationalIsometryCliffordBaseChangeAlgEquiv (P.blockSpace hx) V
    (P.blockToAmbientIsometryEquiv hx) A

/-- The pure Clifford generator of the block last-coordinate line maps
literally to the pure generator of the ambient rational vector `x`. -/
@[simp]
theorem blockToAmbientCliffordBaseChangeAlgEquiv_lastCoordinate
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
        ((1 : A) ⊗ₜ[ℚ] CliffordAlgebra.ι
          (P.blockSpace hx).quadraticForm
          (lastCoordinateVector : Fin (m + 1) → ℚ)) =
      (1 : A) ⊗ₜ[ℚ] CliffordAlgebra.ι
        V.quadraticForm x := by
  rw [rationalIsometryCliffordBaseChangeAlgEquiv_tmul_ι,
    P.blockToAmbientIsometryEquiv_lastCoordinateVector hx]

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix
