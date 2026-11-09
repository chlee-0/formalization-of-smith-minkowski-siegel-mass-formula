import SMSFormula.RealCrossChartAmbient

/-!
# Ambient measure comparison for real congruence chart overlaps

This module keeps the transported/standard overlap on the fixed source
skew-adjoint tangent carrier.  It records the exact open source and image
sets, an explicit pointwise inverse, and the ambient nonlinear
change-of-variables identity.  No homeomorphism between nested dependent
overlap subtypes is introduced.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The exact fixed-carrier source on which source identity coordinates,
group congruence, and target identity coordinates are simultaneously
defined. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  realCrossChartAmbientSource
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph

/-- The exact standard target-coordinate image, pulled back through tangent
congruence to the fixed source tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  realCrossChartAmbientTarget
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)

/-- The pointwise inverse of the fixed-carrier cross-form transition on its
exact standard-coordinate image. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  realCrossChartAmbientTransitionInv
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W) z


end PositiveDefiniteIntegralLattice
