import SMSFormula.SpecialOrthogonalRealFormCongruencePointCenteredDifferential

/-!
# Density factorization for explicit real-congruence point-centered charts

This module rewrites the three complete determinant factors from the
point-centered derivative certificate as the source density, target density,
and explicit-real cross-transition Jacobian.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source moving-transition determinant is the source identity-chart
coordinate density. -/
theorem specialFormPreservingSmoothRealFormCongruenceSourceCoordinateDensity_eq_abs_det_source
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet 1
        ⟨x, hx.1⟩ =
      |LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
            F F' hF hdet hF' hdet' c x) x).toLinearMap| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq]
  rfl

/-- The middle derivative determinant is the explicit-real
cross-transition Jacobian. -/
theorem specialFormPreservingSmoothRealFormCongruenceCrossDeterminant_abs_eq_jacobian
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    |LinearMap.det
      (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c x).toLinearMap| =
      specialFormPreservingSmoothRealFormCongruenceTransitionJacobian
        F F' hF hdet hF' hdet' c x :=
  rfl

/-- Conjugating the target moving-transition derivative through the explicit
tangent equivalence does not change its determinant. -/
theorem specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt_det
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    LinearMap.det
        (specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
          F F' hF hdet hF' hdet' c x y).toLinearMap =
      LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealSkewAdjointTransition
            F' hF' hdet' 1
            (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
              F F' hF hdet hF' hdet' c x))
          (c.tangentEquiv y)).toLinearMap := by
  rw [
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt,
    ← ContinuousLinearMap.comp_assoc]
  simpa only [ContinuousLinearMap.comp_assoc] using
    LinearMap.det_conj
      (fderiv ℝ
        (specialFormPreservingSmoothRealSkewAdjointTransition
          F' hF' hdet' 1
          (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
            F F' hF hdet hF' hdet' c x))
        (c.tangentEquiv y)).toLinearMap
      c.tangentEquiv.symm.toLinearEquiv

/-- The target moving-transition determinant is the independently chosen
target identity-chart coordinate density. -/
theorem specialFormPreservingSmoothRealFormCongruenceTargetCoordinateDensity_eq_abs_det_target
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealChartCoordinateDensity F' hF' hdet' 1
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx) =
      |LinearMap.det
        (specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
          F F' hF hdet hF' hdet' c x
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x)).toLinearMap| := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensity_eq,
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt_det,
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at
      F F' hF hdet hF' hdet' c x hx,
    c.tangentEquiv.apply_symm_apply]
  rw [show
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx).1 =
      specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x by
      exact (specialFormPreservingSmoothRealIdentityChart
        F' hF' hdet').left_inv hx.2]
  rfl

/-- The source and target identity-chart densities satisfy the real-valued
explicit-real cross-transition Jacobian cocycle. -/
theorem specialFormPreservingSmoothRealFormCongruenceChartDensityCocycle_source_real
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealChartCoordinateDensity F hF hdet 1
        ⟨x, hx.1⟩ =
      specialFormPreservingSmoothRealChartCoordinateDensity F' hF' hdet' 1
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx) *
        specialFormPreservingSmoothRealFormCongruenceTransitionJacobian
          F F' hF hdet hF' hdet' c x := by
  rw [
    specialFormPreservingSmoothRealFormCongruenceSourceCoordinateDensity_eq_abs_det_source
      F F' hF hdet hF' hdet' c x hx,
    specialFormPreservingSmoothRealFormCongruenceTargetCoordinateDensity_eq_abs_det_target
      F F' hF hdet hF' hdet' c x hx,
    ← specialFormPreservingSmoothRealFormCongruenceCrossDeterminant_abs_eq_jacobian,
    ← abs_mul,
    det_target_mul_det_cross_eq_det_source_specialFormPreservingSmoothRealFormCongruencePointCentered
      F F' hF hdet hF' hdet' c x hx]

/-- Fixed-source `ENNReal` form of the explicit-real density cocycle. -/
theorem specialFormPreservingSmoothRealFormCongruenceChartDensityCocycle_source
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal F hF hdet 1
        ⟨x, hx.1⟩ =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
          F' hF' hdet' 1
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx) *
        ENNReal.ofReal
          (specialFormPreservingSmoothRealFormCongruenceTransitionJacobian
            F F' hF hdet hF' hdet' c x) := by
  have hreal :=
    specialFormPreservingSmoothRealFormCongruenceChartDensityCocycle_source_real
      F F' hF hdet hF' hdet' c x hx
  have h := congrArg ENNReal.ofReal hreal
  have hnonneg :
      0 ≤ specialFormPreservingSmoothRealChartCoordinateDensity
        F' hF' hdet' 1
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx) :=
    (specialFormPreservingSmoothRealChartCoordinateDensity_pos
      F' hF' hdet' 1
      (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
        F F' hF hdet hF' hdet' c x hx)).le
  rw [ENNReal.ofReal_mul hnonneg] at h
  exact h

end PositiveDefiniteIntegralLattice
