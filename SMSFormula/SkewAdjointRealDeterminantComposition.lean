import SMSFormula.RationalPadicNormProductFormula
import SMSFormula.SkewAdjointCongruenceNormalization
import SMSFormula.SpecialOrthogonalRealDiagonalScaling
import SMSFormula.SpecialOrthogonalRealIdentityElementaryBasis

/-!
# Composition of the skew-adjoint tangent determinants

The rational congruence and positive-diagonal real scaling determinants are
defined using independently fixed bases.  This file compares their product
with the rational fixed/form-elementary determinant by inserting the
form-adapted elementary bases between the fixed bases.

The two resulting residual determinants are kept explicit.  In
particular, no congruence determinant, diagonal multiplier, reindexing, or
sign is replaced by one.  No local norm product, adelic measure,
reference Haar measure, or Tamagawa theorem is used here.
-/

noncomputable section

set_option maxRecDepth 2000

open scoped Matrix
open PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

private theorem basis_det_reindex_both
    {K ι ι' M : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    [AddCommGroup M] [Module K M]
    (b b' : Module.Basis ι K M) (e : ι ≃ ι') :
    (b.reindex e).det (b'.reindex e) = b.det b' := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix :
      (b.reindex e).toMatrix (b'.reindex e) =
        Matrix.reindex e e (b.toMatrix b') := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Matrix.reindex_apply]
  rw [hmatrix, Matrix.det_reindex_self]

private theorem basis_det_map_both
    {K ι M M' : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M']
    (b b' : Module.Basis ι K M) (e : M ≃ₗ[K] M') :
    (b.map e).det (b'.map e) = b.det b' := by
  rw [Module.Basis.det_map]
  congr 1
  ext i
  simp

/-- The form-adapted rational finite basis after direct scalar extension to
the real skew-adjoint tangent space. -/
def skewAdjointFormElementaryRealFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))) :=
  skewAdjointScalarExtensionBasis (K := ℝ) F
    (skewAdjointFormElementaryRationalFinBasis F hF hdet)

/-- The real form-adapted basis vectors are the scalar extensions of the
rational, `StrictUpperPair`-reindexed elementary vectors. -/
@[simp]
theorem coe_skewAdjointFormElementaryRealFinBasis_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (i : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    (skewAdjointFormElementaryRealFinBasis F hF hdet i :
        Matrix (Fin n) (Fin n) ℝ) =
      ((skewAdjointFormElementaryRationalFinBasis F hF hdet i :
          skewAdjointMatricesLieSubalgebra F) :
        Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ) := by
  exact coe_skewAdjointScalarExtensionBasis_apply F
    (skewAdjointFormElementaryRationalFinBasis F hF hdet) i

/-- Scalar extension preserves the signed fixed/form-elementary determinant
for every symmetric nonsingular rational form. -/
theorem skewAdjointFixedRealBasis_det_formElementary
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointScalarExtensionFinBasis (K := ℝ) F).det
        (skewAdjointFormElementaryRealFinBasis F hF hdet) =
      (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ) := by
  have h := skewAdjointScalarExtensionBasis_det_apply
    (K := ℝ) F (skewAdjointFinBasis F)
    (skewAdjointFormElementaryRationalFinBasis F hF hdet)
  have hv :
      (fun j => skewAdjointScalarExtensionEquiv (K := ℝ) F
        (1 ⊗ₜ[ℚ]
          skewAdjointFormElementaryRationalFinBasis F hF hdet j)) =
        skewAdjointFormElementaryRealFinBasis F hF hdet := by
    funext j
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionEquiv_tmul,
      coe_skewAdjointFormElementaryRealFinBasis_apply]
    simp
  rw [hv] at h
  simpa only [skewAdjointScalarExtensionFinBasis,
    skewAdjointFixedFormElementaryDetScalar] using h

/-- The source form-elementary real basis, with the same
`Fin.castOrderIso` reindexing used by the real determinant of a
linear equivalence. -/
def skewAdjointRealLinearEquivSourceFormElementaryBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F')))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointFormElementaryRealFinBasis F hF hdet).reindex
    (Fin.castOrderIso
      (finrank_skewAdjoint_eq_of_real_linearEquiv F F' e))

/-- The form-adapted rational basis, transported by rational congruence and
reindexed to the target fixed-basis index. -/
def skewAdjointCongruenceTransportedFormElementaryFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (skewAdjointCongruenceForm F W))))
      ℚ
      (skewAdjointMatricesLieSubalgebra
        (skewAdjointCongruenceForm F W)) :=
  ((skewAdjointFormElementaryRationalFinBasis F hF hdet).map
      (skewAdjointCongruenceLinearEquiv F W)).reindex
    (Fin.castOrderIso (finrank_skewAdjointCongruenceForm F W))

/-- The residual determinant of rational congruence when both tangent spaces
are written in their form-adapted elementary bases. -/
def skewAdjointCongruenceFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) : ℚ :=
  (skewAdjointFormElementaryRationalFinBasis
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).det
    (skewAdjointCongruenceTransportedFormElementaryFinBasis
      F hF hdet W)

/-- The rational congruence determinant, the source fixed/form-elementary
determinant, the target fixed/form-elementary determinant, and the literal
elementary-coordinate residual satisfy the exact signed composition law. -/
theorem skewAdjointCongruenceDetScalar_mul_fixedFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    skewAdjointCongruenceDetScalar F W *
        skewAdjointFixedFormElementaryDetScalar F hF hdet =
      skewAdjointFixedFormElementaryDetScalar
          (skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) *
        skewAdjointCongruenceFormElementaryDetScalar F hF hdet W := by
  let A := skewAdjointFinBasis (skewAdjointCongruenceForm F W)
  let B := skewAdjointCongruenceTransportedFinBasis F W
  let C := skewAdjointCongruenceTransportedFormElementaryFinBasis F hF hdet W
  let D := skewAdjointFormElementaryRationalFinBasis
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  have hABC := Module.Basis.det_mul_det A B C
  have hADC := Module.Basis.det_mul_det A D C
  have hBC : B.det C =
      skewAdjointFixedFormElementaryDetScalar F hF hdet := by
    dsimp only [B, C, skewAdjointCongruenceTransportedFinBasis,
      skewAdjointCongruenceTransportedFormElementaryFinBasis]
    rw [basis_det_reindex_both]
    rw [Module.Basis.det_map]
    change (skewAdjointFinBasis F).det _ = _
    rw [skewAdjointFixedFormElementaryDetScalar]
    congr 1
    funext i
    simp
  calc
    skewAdjointCongruenceDetScalar F W *
        skewAdjointFixedFormElementaryDetScalar F hF hdet =
      A.det B * B.det C := by
        rw [hBC]
        rfl
    _ = A.det C := hABC
    _ = A.det D * D.det C := hADC.symm
    _ = skewAdjointFixedFormElementaryDetScalar
          (skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) *
        skewAdjointCongruenceFormElementaryDetScalar F hF hdet W := rfl

/-- The source form-elementary real basis transported by rational congruence,
with exactly the `Fin.castOrderIso` used in the real determinant. -/
def skewAdjointRealCongruenceTransportedFormElementaryFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (skewAdjointCongruenceForm F W))))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        ((skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointRealLinearEquivSourceFormElementaryBasis
      F hF hdet (skewAdjointCongruenceForm F W)
      (skewAdjointRealCongruenceContinuousLinearEquiv F W)).map
    (skewAdjointRealCongruenceContinuousLinearEquiv F W).toLinearEquiv

/-- The elementary-coordinate residual of the real
rational-congruence tangent equivalence. -/
def skewAdjointRealCongruenceFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) : ℝ :=
  (skewAdjointFormElementaryRealFinBasis
      (skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).det
    (skewAdjointRealCongruenceTransportedFormElementaryFinBasis
      F hF hdet W)

/-- The real congruence determinant satisfies the exact signed
fixed/form-elementary composition law, independently of any attempt to
evaluate its elementary-coordinate residual. -/
theorem
    skewAdjointRealCongruenceDetScalar_mul_fixedFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ) :
    skewAdjointRealCongruenceDetScalar F W *
        (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ) =
      (skewAdjointFixedFormElementaryDetScalar
          (skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) : ℝ) *
        skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W := by
  let e := skewAdjointRealCongruenceContinuousLinearEquiv F W
  let A := skewAdjointScalarExtensionFinBasis (K := ℝ)
    (skewAdjointCongruenceForm F W)
  let B := (skewAdjointRealLinearEquivSourceBasis
    F (skewAdjointCongruenceForm F W) e).map e.toLinearEquiv
  let C := skewAdjointRealCongruenceTransportedFormElementaryFinBasis
    F hF hdet W
  let D := skewAdjointFormElementaryRealFinBasis
    (skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  have hABC := Module.Basis.det_mul_det A B C
  have hADC := Module.Basis.det_mul_det A D C
  have hBC : B.det C =
      (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ) := by
    rw [show B.det C =
        ((skewAdjointRealLinearEquivSourceBasis
          F (skewAdjointCongruenceForm F W) e).map e.toLinearEquiv).det
          ((skewAdjointRealLinearEquivSourceFormElementaryBasis
            F hF hdet (skewAdjointCongruenceForm F W) e).map
              e.toLinearEquiv) by rfl]
    rw [basis_det_map_both]
    rw [show
        (skewAdjointRealLinearEquivSourceBasis
          F (skewAdjointCongruenceForm F W) e).det
            (skewAdjointRealLinearEquivSourceFormElementaryBasis
              F hF hdet (skewAdjointCongruenceForm F W) e) =
          (skewAdjointScalarExtensionFinBasis (K := ℝ) F).det
            (skewAdjointFormElementaryRealFinBasis F hF hdet) by
      exact basis_det_reindex_both _ _ _]
    exact skewAdjointFixedRealBasis_det_formElementary F hF hdet
  calc
    skewAdjointRealCongruenceDetScalar F W *
        (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ) =
      A.det B * B.det C := by
        rw [hBC]
        rfl
    _ = A.det C := hABC
    _ = A.det D * D.det C := hADC.symm
    _ = (skewAdjointFixedFormElementaryDetScalar
          (skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) : ℝ) *
        skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W := by
      rw [show A.det D =
          (skewAdjointFixedFormElementaryDetScalar
            (skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) : ℝ) by
        exact skewAdjointFixedRealBasis_det_formElementary _ _ _]
      rfl

/-- The positive-diagonal source elementary basis after square-root scaling,
still indexed by the identity-form fixed tangent dimension. -/
def positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointRealLinearEquivSourceFormElementaryBasis
      (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
      (positiveDiagonalForm_det_ne_zero d hd) 1
      (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd)).map
    (positiveDiagonalSkewAdjointContinuousLinearEquiv d hd).toLinearEquiv

/-- The residual determinant of square-root scaling in the literal
form-elementary and identity-elementary real bases. -/
def positiveDiagonalSkewAdjointFormElementaryDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) : ℝ :=
  (identitySpecialOrthogonalElementaryRealFinBasis n).det
    (positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis d hd)

/-- The square-root-scaling determinant composes exactly with the
diagonal fixed/form-elementary determinant.  The target fixed/elementary
determinant and the elementary-coordinate residual occur with their
signed orientations. -/
theorem positiveDiagonalSkewAdjointDetScalar_mul_fixedFormElementaryDetScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSkewAdjointDetScalar d hd *
        (skewAdjointFixedFormElementaryDetScalar
          (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd) : ℝ) =
      (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
        positiveDiagonalSkewAdjointFormElementaryDetScalar d hd := by
  let e := positiveDiagonalSkewAdjointContinuousLinearEquiv d hd
  let A := skewAdjointScalarExtensionFinBasis (K := ℝ)
    (1 : Matrix (Fin n) (Fin n) ℚ)
  let B := (skewAdjointRealLinearEquivSourceBasis
    (Matrix.diagonal d) 1 e).map e.toLinearEquiv
  let C :=
    positiveDiagonalSkewAdjointTransportedFormElementaryRealFinBasis d hd
  let D := identitySpecialOrthogonalElementaryRealFinBasis n
  have hABC := Module.Basis.det_mul_det A B C
  have hADC := Module.Basis.det_mul_det A D C
  have hBC : B.det C =
      (skewAdjointFixedFormElementaryDetScalar
        (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) : ℝ) := by
    rw [show B.det C =
        ((skewAdjointRealLinearEquivSourceBasis
          (Matrix.diagonal d) 1 e).map e.toLinearEquiv).det
          ((skewAdjointRealLinearEquivSourceFormElementaryBasis
            (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd) 1 e).map
              e.toLinearEquiv) by rfl]
    rw [basis_det_map_both]
    rw [show
        (skewAdjointRealLinearEquivSourceBasis
          (Matrix.diagonal d) 1 e).det
            (skewAdjointRealLinearEquivSourceFormElementaryBasis
              (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
              (positiveDiagonalForm_det_ne_zero d hd) 1 e) =
          (skewAdjointScalarExtensionFinBasis (K := ℝ)
            (Matrix.diagonal d)).det
            (skewAdjointFormElementaryRealFinBasis
              (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
              (positiveDiagonalForm_det_ne_zero d hd)) by
      exact basis_det_reindex_both _ _ _]
    exact skewAdjointFixedRealBasis_det_formElementary
      (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
      (positiveDiagonalForm_det_ne_zero d hd)
  calc
    positiveDiagonalSkewAdjointDetScalar d hd *
        (skewAdjointFixedFormElementaryDetScalar
          (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd) : ℝ) =
      A.det B * B.det C := by
        rw [hBC]
        rfl
    _ = A.det C := hABC
    _ = A.det D * D.det C := hADC.symm
    _ = (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
        positiveDiagonalSkewAdjointFormElementaryDetScalar d hd := by
      rw [show A.det D =
          (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) by
        exact identitySpecialOrthogonalFixedRealBasis_det_elementary n]
      rfl

/-- After a positive rational diagonalization, the three tangent
determinants satisfy one exact signed composition identity.  The right-hand
side keeps both elementary-coordinate determinants: rational
congruence from the original form to the diagonal form, and square-root
scaling from the diagonal form to the identity form. -/
theorem skewAdjointRealCongruence_positiveDiagonal_signed_det_composition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    skewAdjointRealCongruenceDetScalar F W *
        (positiveDiagonalSkewAdjointDetScalar d hd *
          (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)) =
      (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
        (skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W *
          positiveDiagonalSkewAdjointFormElementaryDetScalar d hd) := by
  have hcong :=
    skewAdjointRealCongruenceDetScalar_mul_fixedFormElementaryDetScalar
      F hF hdet W
  have hcong' :
      skewAdjointRealCongruenceDetScalar F W *
          (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ) =
        (skewAdjointFixedFormElementaryDetScalar
            (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd) : ℝ) *
          skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W := by
    simpa only [hdiag] using hcong
  have hscale :=
    positiveDiagonalSkewAdjointDetScalar_mul_fixedFormElementaryDetScalar
      d hd
  calc
    skewAdjointRealCongruenceDetScalar F W *
        (positiveDiagonalSkewAdjointDetScalar d hd *
          (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)) =
      positiveDiagonalSkewAdjointDetScalar d hd *
        (skewAdjointRealCongruenceDetScalar F W *
          (skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)) := by
            ring
    _ = positiveDiagonalSkewAdjointDetScalar d hd *
        ((skewAdjointFixedFormElementaryDetScalar
            (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd) : ℝ) *
          skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W) := by
            rw [hcong']
    _ = (positiveDiagonalSkewAdjointDetScalar d hd *
          (skewAdjointFixedFormElementaryDetScalar
            (Matrix.diagonal d) (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd) : ℝ)) *
        skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W := by
            ring
    _ = ((identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
          positiveDiagonalSkewAdjointFormElementaryDetScalar d hd) *
        skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W := by
            rw [hscale]
    _ = (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) *
        (skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W *
          positiveDiagonalSkewAdjointFormElementaryDetScalar d hd) := by
            ring

/-- Absolute values remove only the signed orientation from the exact
three-stage determinant composition.  Both nontrivial elementary-coordinate
residuals remain literal. -/
theorem skewAdjointRealCongruence_positiveDiagonal_abs_det_composition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    |skewAdjointRealCongruenceDetScalar F W| *
        (|positiveDiagonalSkewAdjointDetScalar d hd| *
          |(skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)|) =
      |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
        (|skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W| *
          |positiveDiagonalSkewAdjointFormElementaryDetScalar d hd|) := by
  simpa only [abs_mul] using congrArg abs
    (skewAdjointRealCongruence_positiveDiagonal_signed_det_composition
      F hF hdet W d hd hdiag)

end Matrix
