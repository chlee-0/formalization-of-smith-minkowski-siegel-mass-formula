import SMSFormula.SkewAdjointRealCongruenceElementaryResidual

/-!
# Assembly of the evaluated real skew-adjoint determinant residuals

This module substitutes the directly evaluated rational-congruence and
positive-diagonal elementary residuals into the three-stage real
tangent determinant composition.  The determinant equation for a positive
rational diagonalization then removes the auxiliary congruence matrix from
the residual product.

No p-adic product formula, adelic quotient source, reference Haar measure, or
Tamagawa value is used here.
-/

noncomputable section

open scoped Matrix
open PositiveDefiniteIntegralLattice

namespace Matrix

variable {n : ℕ}

/-- Substituting both evaluated elementary residuals into the absolute
three-stage determinant composition leaves their literal closed products. -/
theorem skewAdjointRealCongruence_positiveDiagonal_abs_det_composition_evaluated
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    |skewAdjointRealCongruenceDetScalar F W| *
        (|positiveDiagonalSkewAdjointDetScalar d hd| *
          |(skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)|) =
      |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
        (|(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| ^ (n - 1) *
          (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) ^ (n - 1)) := by
  calc
    _ = |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
        (|skewAdjointRealCongruenceFormElementaryDetScalar F hF hdet W| *
          |positiveDiagonalSkewAdjointFormElementaryDetScalar d hd|) :=
      skewAdjointRealCongruence_positiveDiagonal_abs_det_composition
        F hF hdet W d hd hdiag
    _ = _ := by
      rw [abs_skewAdjointRealCongruenceFormElementaryDetScalar,
        abs_positiveDiagonalSkewAdjointFormElementaryDetScalar_closed]

/-- The determinant of a rational congruence diagonalization is the product
of the diagonal entries. -/
theorem skewAdjointCongruenceForm_det_eq_diagonal_prod
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    (W : Matrix (Fin n) (Fin n) ℚ).det ^ 2 * F.det = ∏ i, d i := by
  have h := congrArg Matrix.det hdiag
  rw [skewAdjointCongruenceForm, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal] at h
  nlinarith

/-- After scalar extension and absolute values, the positive diagonal product
is `|det W|² |det F|`. -/
theorem real_prod_diagonal_eq_abs_det_sq_mul_abs_det
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    (∏ i : Fin n, (d i : ℝ)) =
      |(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| ^ 2 *
        |((F.det : ℚ) : ℝ)| := by
  have hrat := skewAdjointCongruenceForm_det_eq_diagonal_prod F W d hdiag
  have hreal :
      ((((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ) ^ 2 *
          ((F.det : ℚ) : ℝ)) = ∏ i : Fin n, (d i : ℝ) := by
    exact_mod_cast hrat
  have habs := congrArg abs hreal
  rw [abs_mul, abs_pow, Finset.abs_prod] at habs
  have hprodabs : (∏ i : Fin n, |(d i : ℝ)|) = ∏ i : Fin n, (d i : ℝ) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [abs_of_pos]
    exact_mod_cast hd i
  rw [hprodabs] at habs
  exact habs.symm

/-- Taking square roots of the positive diagonal determinant equation gives
the exact product of the diagonal square roots. -/
theorem prod_sqrt_diagonal_eq_abs_det_mul_sqrt_abs_det
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    (∏ i : Fin n, Real.sqrt (d i : ℝ)) =
      |(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| *
        Real.sqrt |((F.det : ℚ) : ℝ)| := by
  have hdet := real_prod_diagonal_eq_abs_det_sq_mul_abs_det
    F W d hd hdiag
  have hsqrt := congrArg Real.sqrt hdet
  have hleft :
      Real.sqrt (∏ i : Fin n, (d i : ℝ)) =
        ∏ i : Fin n, Real.sqrt (d i : ℝ) := by
    exact Real.sqrt_prod Finset.univ (by
      intro i hi
      exact le_of_lt (by exact_mod_cast hd i))
  rw [hleft, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs] at hsqrt
  exact hsqrt

/-- The inverse-square-root product is the inverse of the product appearing in
the positive diagonal determinant equation. -/
theorem prod_inv_sqrt_diagonal_eq_inv_abs_det_mul_sqrt_abs_det
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) =
      (|(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| *
        Real.sqrt |((F.det : ℚ) : ℝ)|)⁻¹ := by
  rw [Finset.prod_inv_distrib,
    prod_sqrt_diagonal_eq_abs_det_mul_sqrt_abs_det F W d hd hdiag]

/-- The congruence determinant power cancels from the combined residual
product.  Only the original form determinant remains. -/
theorem abs_det_pow_mul_prod_inv_sqrt_pow
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    |(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)| ^ (n - 1) *
        (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) ^ (n - 1) =
      (Real.sqrt |((F.det : ℚ) : ℝ)|)⁻¹ ^ (n - 1) := by
  let a : ℝ := |(((W : Matrix (Fin n) (Fin n) ℚ).det : ℚ) : ℝ)|
  let b : ℝ := Real.sqrt |((F.det : ℚ) : ℝ)|
  have hWrat : (W : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 :=
    Units.ne_zero (Matrix.GeneralLinearGroup.det W)
  have ha : a ≠ 0 := by
    simp only [a, abs_ne_zero]
    exact_mod_cast hWrat
  have hFreal : ((F.det : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hdet
  have hb : b ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr hFreal))
  have hinv : (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) = (a * b)⁻¹ := by
    exact prod_inv_sqrt_diagonal_eq_inv_abs_det_mul_sqrt_abs_det
      F W d hd hdiag
  have hcancel : a * (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) = b⁻¹ := by
    rw [hinv]
    field_simp
  change a ^ (n - 1) *
      (∏ i : Fin n, (Real.sqrt (d i : ℝ))⁻¹) ^ (n - 1) =
    b⁻¹ ^ (n - 1)
  rw [← mul_pow, hcancel]

/-- Fully assembling the two residual evaluations removes the auxiliary
diagonalization matrix and leaves the original form determinant only. -/
theorem skewAdjointRealCongruence_positiveDiagonal_abs_det_composition_closed
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (W : GL (Fin n) ℚ)
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (hdiag : skewAdjointCongruenceForm F W = Matrix.diagonal d) :
    |skewAdjointRealCongruenceDetScalar F W| *
        (|positiveDiagonalSkewAdjointDetScalar d hd| *
          |(skewAdjointFixedFormElementaryDetScalar F hF hdet : ℝ)|) =
      |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
        (Real.sqrt |((F.det : ℚ) : ℝ)|)⁻¹ ^ (n - 1) := by
  rw [skewAdjointRealCongruence_positiveDiagonal_abs_det_composition_evaluated
      F hF hdet W d hd hdiag,
    abs_det_pow_mul_prod_inv_sqrt_pow F hdet W d hd hdiag]

end Matrix
