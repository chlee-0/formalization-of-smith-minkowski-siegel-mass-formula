import SMSFormula.PadicCayleyTargetChartCoordinateComparison
import SMSFormula.SkewSymmetricMatrixBasis

/-!
# Explicit Jacobian density on the p-adic Cayley target chart

The Jacobian density transported to the exact special-orthogonal inverse
domain is rewritten in target coordinates. The inverse Cayley denominator is
`(g + 1)⁻¹ * 2`, so its determinant norm is
`‖det (g + 1)‖₊⁻¹ * ‖2‖₊ ^ n`. For a symmetric nonsingular form, the
skew-adjoint rank is `n.choose 2`; this closes the target density as

`‖2‖₊ ^ (n.choose 2) * ‖det (g + 1)‖₊⁻¹ ^ (n - 1)`.

The odd-prime and dyadic specializations respectively remove the scalar and
retain `(2⁻¹) ^ (n.choose 2)`.

This file stays on the exact Cayley chart subtypes. It does not extend a
measure to the full group, prove invariance, or glue charts.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTargetJacobianFormulaGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetJacobianFormulaGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- In target coordinates, the source denominator is the inverse target
denominator times the scalar matrix `2`. -/
theorem one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    1 -
        ((((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
            F p hF).symm g).1 :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
      (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) :
        Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        padicCayleyTwoMatrix (ι := Fin n) p := by
  let gm : Matrix (Fin n) (Fin n) ℚ_[p] := g.1
  have hg : gm ∈ padicCayleyInverseDomain p := g.2
  change 1 - padicCayleyInverseMatrix p gm =
    (gm + 1)⁻¹ * padicCayleyTwoMatrix p
  exact one_sub_padicCayleyInverseMatrix p gm hg

/-- The determinant of the inverse-coordinate source denominator. -/
theorem det_one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    Matrix.det
        (1 -
          ((((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
              F p hF).symm g).1 :
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
            Matrix (Fin n) (Fin n) ℚ_[p])) =
      (Matrix.det
        (((g.1 : specialOrthogonalMatrixSet
            (F.map (algebraMap ℚ ℚ_[p]))) :
          Matrix (Fin n) (Fin n) ℚ_[p]) + 1))⁻¹ *
        (2 : ℚ_[p]) ^ n := by
  rw [one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm,
    Matrix.det_mul, Matrix.det_nonsing_inv]
  simp [padicCayleyTwoMatrix]

/-- The nonnegative norm of the inverse-coordinate source denominator
determinant. -/
theorem nnnorm_det_one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    ‖Matrix.det
        (1 -
          ((((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
              F p hF).symm g).1 :
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
            Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ =
      ‖Matrix.det
        (((g.1 : specialOrthogonalMatrixSet
            (F.map (algebraMap ℚ ℚ_[p]))) :
          Matrix (Fin n) (Fin n) ℚ_[p]) + 1)‖₊⁻¹ *
        ‖(2 : ℚ_[p])‖₊ ^ n := by
  rw [det_one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm,
    nnnorm_mul, nnnorm_inv, nnnorm_pow]

/-- For a symmetric nonsingular form, the rational skew-adjoint rank is
`n.choose 2`. -/
theorem finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) =
      n.choose 2 := by
  rw [← finrank_skewAdjointScalarExtension_padic F 2]
  rw [(skewAdjointPadicSkewSymmetricContinuousLinearEquiv
    2 F hFsymm hF).toLinearEquiv.finrank_eq]
  exact finrank_skewSymmetricMatricesSubmodule (K := ℚ_[2]) (n := n)
    (by norm_num)

private theorem target_cayley_scalar_density_identity
    (c a : ℝ≥0) (hc : c ≠ 0) :
    c⁻¹ ^ (n.choose 2) * (a * c ^ n) ^ (n - 1) =
      c ^ (n.choose 2) * a ^ (n - 1) := by
  have hchoose :
      n * (n - 1) = n.choose 2 + n.choose 2 := by
    cases n with
    | zero => simp
    | succ n =>
        simpa [Nat.mul_two] using Nat.add_one_mul_choose_eq n 1
  rw [mul_pow, ← pow_mul, hchoose, pow_add, inv_pow]
  calc
    (c ^ n.choose 2)⁻¹ *
          (a ^ (n - 1) *
            (c ^ n.choose 2 * c ^ n.choose 2)) =
        a ^ (n - 1) *
          ((c ^ n.choose 2)⁻¹ * c ^ n.choose 2) *
            c ^ n.choose 2 := by ac_rfl
    _ = a ^ (n - 1) * c ^ n.choose 2 := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ hc), mul_one]
    _ = c ^ n.choose 2 * a ^ (n - 1) := mul_comm _ _

/-- The target density before combining the scalar powers. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_expanded
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF g =
      ((‖(2 : ℚ_[p])‖₊⁻¹ ^
            Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
          (‖Matrix.det
              (((g.1 : specialOrthogonalMatrixSet
                  (F.map (algebraMap ℚ ℚ_[p]))) :
                Matrix (Fin n) (Fin n) ℚ_[p]) + 1)‖₊⁻¹ *
            ‖(2 : ℚ_[p])‖₊ ^ n) ^ (n - 1) : ℝ≥0) : ℝ≥0∞) := by
  simp only [
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal,
    skewAdjointPadicCayleyCoordinateJacobianDensityENNReal,
    skewAdjointPadicCayleyCoordinateJacobianDensity]
  rw [
    nnnorm_det_one_sub_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm]

/-- For a symmetric nonsingular form, the target Jacobian density is the
closed target-coordinate determinant formula. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF g =
      ((‖(2 : ℚ_[p])‖₊ ^ (n.choose 2) *
          ‖Matrix.det
            (((g.1 : specialOrthogonalMatrixSet
                (F.map (algebraMap ℚ ℚ_[p]))) :
              Matrix (Fin n) (Fin n) ℚ_[p]) + 1)‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  rw [
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_expanded,
    finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two n F hFsymm hF]
  congr 1
  exact target_cayley_scalar_density_identity n
    ‖(2 : ℚ_[p])‖₊
    ‖Matrix.det
      (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) :
        Matrix (Fin n) (Fin n) ℚ_[p]) + 1)‖₊⁻¹
    (ne_of_gt (nnnorm_pos.mpr (by norm_num)))

/-- At an odd prime, the target Jacobian density has only the inverse
`g + 1` determinant factor. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_of_ne_two
    (hp_two : p ≠ 2)
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF g =
      ((‖Matrix.det
          (((g.1 : specialOrthogonalMatrixSet
              (F.map (algebraMap ℚ ℚ_[p]))) :
            Matrix (Fin n) (Fin n) ℚ_[p]) + 1)‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  rw [
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq
      p n F hFsymm hF g,
    nnnorm_two_padic_eq_one_of_ne_two p hp_two,
    one_pow, one_mul]

/-- At the dyadic place, the target Jacobian density retains the scalar
`(2⁻¹)^(n.choose 2)`. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_two
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F 2) :
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        2 n F hF g =
      ((((2 : ℝ≥0)⁻¹) ^ (n.choose 2) *
          ‖Matrix.det
            (((g.1 : specialOrthogonalMatrixSet
                (F.map (algebraMap ℚ ℚ_[2]))) :
              Matrix (Fin n) (Fin n) ℚ_[2]) + 1)‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  rw [
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq
      2 n F hFsymm hF g,
    nnnorm_two_dyadic]

end Matrix
