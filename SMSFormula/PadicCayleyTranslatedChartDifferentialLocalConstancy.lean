import SMSFormula.PadicCayleyTranslatedChartDifferentialRegularity
import SMSFormula.PadicCayleyTranslatedChartOverlapJacobianLocalConstancy

/-!
# Local constancy of the corrected p-adic Cayley differential density

The Cayley scalar depends on the p-adic norm of
`det (1 - X)`.  On the exact Cayley source this determinant is nonzero.
Continuity of the determinant and local constancy of the p-adic norm away
from zero therefore make both the scalar and its correctly oriented
reciprocal density locally constant.

This module works directly on the exact source subtype.  It does not select
coordinate balls.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The determinant `det (1 - X)` is continuous on the exact p-adic Cayley
source. -/
theorem continuous_det_one_sub_skewAdjointPadicCayleySource
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Continuous
      (fun X : skewAdjointPadicCayleySource F p =>
        Matrix.det
          (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))) := by
  fun_prop

/-- The determinant `det (1 - X)` is nonzero on the exact p-adic Cayley
source. -/
theorem det_one_sub_skewAdjointPadicCayleySource_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    Matrix.det
        (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])) ≠
      0 :=
  isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det
      (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))).mp X.2)

/-- The nonnegative norm of `det (1 - X)` is locally constant on the exact
p-adic Cayley source. -/
theorem isLocallyConstant_nnnorm_det_one_sub_skewAdjointPadicCayleySource
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyConstant
      (fun X : skewAdjointPadicCayleySource F p =>
        ‖Matrix.det
          (1 - (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊) :=
  PositiveDefiniteIntegralLattice.isLocallyConstant_nnnorm_of_continuous_ne_zero_padic
    _
    (continuous_det_one_sub_skewAdjointPadicCayleySource p n F)
    (det_one_sub_skewAdjointPadicCayleySource_ne_zero p n F)

/-- The inverse-Jacobian Cayley scalar is locally constant on the
exact source. -/
theorem
    isLocallyConstant_skewAdjointPadicCayleyCoordinateJacobianDensity_source
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyConstant
      (fun X : skewAdjointPadicCayleySource F p =>
        skewAdjointPadicCayleyCoordinateJacobianDensity p n F X.1) := by
  have hdet :=
    isLocallyConstant_nnnorm_det_one_sub_skewAdjointPadicCayleySource
      p n F
  have hformula :=
    hdet.comp
      (fun r : NNReal =>
        ‖(2 : ℚ_[p])‖₊⁻¹ ^
            Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) *
          r ^ (n - 1))
  simpa only [skewAdjointPadicCayleyCoordinateJacobianDensity] using hformula

/-- The correctly oriented `NNReal` Cayley source differential density is
locally constant. -/
theorem
    isLocallyConstant_skewAdjointPadicCayleySourceDifferentialDensityNNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyConstant
      (skewAdjointPadicCayleySourceDifferentialDensityNNReal p n F) := by
  have h :=
    (isLocallyConstant_skewAdjointPadicCayleyCoordinateJacobianDensity_source
      p n F).comp (fun r : NNReal => r⁻¹)
  simpa only [skewAdjointPadicCayleySourceDifferentialDensityNNReal] using h

/-- The correctly oriented `ENNReal` Cayley source differential density is
locally constant. -/
theorem
    isLocallyConstant_skewAdjointPadicCayleySourceDifferentialDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyConstant
      (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F) := by
  have h :=
    (isLocallyConstant_skewAdjointPadicCayleySourceDifferentialDensityNNReal
      p n F).comp (fun r : NNReal => (r : ENNReal))
  convert h using 1
  funext X
  exact
    skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe
      p n F X

end Matrix
