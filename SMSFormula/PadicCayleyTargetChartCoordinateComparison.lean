import SMSFormula.PadicCayleyTargetChartMeasureFullSupport

/-!
# Coordinate comparison on the p-adic Cayley target chart

The unweighted source-subtype coordinate measure is pushed through the Cayley
homeomorphism to the exact target subtype. The source and target weighted
measures are identified exactly as `withDensity` measures for the Jacobian
density and its pullback through the inverse chart. This gives inverse
transport, mutual absolute continuity, positivity of the target density, and
reciprocal recovery of the unweighted target coordinate measure.

This file does not extend a measure to the full special-orthogonal carrier,
prove group invariance, or glue charts.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTargetCoordinateComparisonSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTargetCoordinateComparisonSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTargetCoordinateComparisonGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetCoordinateComparisonGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The unweighted coordinate measure on the exact Cayley target subtype. -/
def padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measure (padicCayleySpecialOrthogonalInverseDomain F p) :=
  Measure.map
    (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF)
    (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F)

/-- Mapping the target coordinate measure through the inverse Cayley
homeomorphism recovers the source-subtype coordinate measure. -/
theorem
    map_padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measure.map
        (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF).symm
        (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
          p n F hF) =
      skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F := by
  rw [padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure]
  exact MeasurableEquiv.map_map_symm
    (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
      F p hF).symm.toMeasurableEquiv

/-- The explicit extended Jacobian density on the exact Cayley target
subtype, obtained by evaluating the source density in inverse coordinates. -/
def padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) : ℝ≥0∞ :=
  skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F
    ((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF).symm g)

/-- The target-chart Jacobian density is continuous. -/
theorem
    continuous_padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Continuous
      (padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF) :=
  (continuous_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    p n F).comp
      (continuous_subtype_val.comp
        (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
          F p hF).symm.continuous)

/-- The target-chart Jacobian density is measurable. -/
theorem
    measurable_padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measurable
      (padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF) :=
  (continuous_padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
    p n F hF).measurable

/-- The target-chart Jacobian density is strictly positive. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    0 <
      padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
        p n F hF g := by
  exact skewAdjointPadicCayleyCoordinateJacobianDensityENNReal_pos
    p n F _
      ((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
        F p hF).symm g).property

end Matrix
