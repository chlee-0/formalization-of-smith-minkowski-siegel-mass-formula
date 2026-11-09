import SMSFormula.SpecialOrthogonalRealCongruenceOverlapEquivalence

/-!
# Inverse maps for ambient real congruence chart overlaps
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The explicit inverse maps the exact ambient target overlap back into the
exact ambient source overlap. -/
theorem mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set.MapsTo
      (specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :=
  mapsTo_realCrossChartAmbientTransitionInv
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)

end PositiveDefiniteIntegralLattice
