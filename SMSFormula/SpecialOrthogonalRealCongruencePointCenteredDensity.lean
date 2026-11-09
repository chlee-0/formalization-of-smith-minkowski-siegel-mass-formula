import SMSFormula.SpecialOrthogonalRealCongruencePointCenteredDifferential

/-!
# Density factorization for point-centered real congruence charts

This module rewrites the three determinant factors in the point-centered
derivative certificate as the two chart densities and the cross-form
Jacobian.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source moving-transition determinant is the source identity-chart
coordinate density. -/
theorem specialFormPreservingSmoothRealCongruenceSourceCoordinateDensity_eq_abs_det_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet 1
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y) =
      |LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
            F hF hdet W y)
          (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
            F hF hdet W y).1).toLinearMap| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq]
  rfl

/-- The middle derivative determinant is the fixed-source cross-form
Jacobian. -/
theorem specialFormPreservingSmoothRealCongruenceCrossDeterminant_abs_eq_jacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    |LinearMap.det
      (specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W x).toLinearMap| =
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
        F hF hdet W x :=
  rfl

/-- Conjugating the target moving-transition derivative through tangent
congruence does not change its determinant. -/
theorem specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt_det
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    LinearMap.det
        (specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt
          F hF hdet W y x).toLinearMap =
      LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealSkewAdjointTransition
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
            (specialFormPreservingSmoothRealCongruenceTargetPointAt
              F hF hdet W y))
          (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
            F W x)).toLinearMap := by
  rw [specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt,
    ← ContinuousLinearMap.comp_assoc]
  simpa only [ContinuousLinearMap.comp_assoc] using
    LinearMap.det_conj
      (fderiv ℝ
        (specialFormPreservingSmoothRealSkewAdjointTransition
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
          (specialFormPreservingSmoothRealCongruenceTargetPointAt
            F hF hdet W y))
        (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
          F W x)).toLinearMap
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
        F W).symm.toLinearEquiv

/-- The target moving-transition determinant is the target identity-chart
coordinate density. -/
theorem specialFormPreservingSmoothRealCongruenceTargetCoordinateDensity_eq_abs_det_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealChartCoordinateDensity
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
          F hF hdet W y hy) =
      |LinearMap.det
        (specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt
          F hF hdet W y
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
              F hF hdet W y).1)).toLinearMap| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq,
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt_det,
    specialFormPreservingSmoothRealCongruenceChartSourceTransition_sourceCoordinateAt
      F hF hdet W y hy,
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply]
  rw [specialFormPreservingSmoothRealCongruenceStandardCoordinateAt,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition_samePoint
      F hF hdet W y hy]
  rfl

/-- The source and target identity-chart densities satisfy the real-valued
cross-form Jacobian cocycle. -/
theorem specialFormPreservingSmoothRealCongruenceChartDensityCocycle_source_real
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet 1
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y) =
      specialFormPreservingSmoothRealChartCoordinateDensity
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
          (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
            F hF hdet W y hy) *
        specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
          F hF hdet W
          (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
            F hF hdet W y).1 := by
  rw [
    specialFormPreservingSmoothRealCongruenceSourceCoordinateDensity_eq_abs_det_source,
    specialFormPreservingSmoothRealCongruenceTargetCoordinateDensity_eq_abs_det_target
      F hF hdet W y hy,
    ← specialFormPreservingSmoothRealCongruenceCrossDeterminant_abs_eq_jacobian,
    ← abs_mul,
    det_target_mul_det_cross_eq_det_source_specialFormPreservingSmoothRealCongruencePointCentered
      F hF hdet W y hy]

/-- The fixed-source form of the transported/standard density cocycle. -/
theorem specialFormPreservingSmoothRealCongruenceChartDensityCocycle_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet 1
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y) =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
          (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
            F hF hdet W y hy) *
        ENNReal.ofReal
          (specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
            F hF hdet W
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
              F hF hdet W y).1) := by
  have hreal :=
    specialFormPreservingSmoothRealCongruenceChartDensityCocycle_source_real
      F hF hdet W y hy
  have h := congrArg ENNReal.ofReal hreal
  have hnonneg :
      0 ≤ specialFormPreservingSmoothRealChartCoordinateDensity
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
          F hF hdet W y hy) :=
    (specialFormPreservingSmoothRealChartCoordinateDensity_pos
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
      (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
        F hF hdet W y hy)).le
  rw [ENNReal.ofReal_mul hnonneg] at h
  exact h

/-- The transported chart density and the target-form identity-chart density
satisfy the exact Jacobian cocycle on their full overlap. -/
theorem specialFormPreservingSmoothRealCongruenceChartDensityCocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
          F hF hdet W y =
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
            ⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
                F hF hdet W y,
              specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
                F hF hdet W y hy⟩ *
          ENNReal.ofReal
            |specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
              F hF hdet W y.1| := by
  apply
    (specialFormPreservingSmoothRealCongruenceChartDensityCocycle_iff_source
      F hF hdet W y hy).2
  exact specialFormPreservingSmoothRealCongruenceChartDensityCocycle_source
    F hF hdet W y hy

end PositiveDefiniteIntegralLattice
