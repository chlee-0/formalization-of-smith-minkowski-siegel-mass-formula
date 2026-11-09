import SMSFormula.SpecialOrthogonalRealCongruenceOverlapTopology

/-!
# Ambient equivalence facts for real congruence chart overlaps

The fixed-carrier cross-form transition and its explicit inverse give a
setwise bijection between the exact ambient source and target overlaps.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- On the exact source overlap, the fixed-carrier transition is the generic
cross-chart coordinate transition. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_crossChart
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x =
      realCrossChartAmbientTransition
        (specialFormPreservingSmoothRealIdentityChart F hF hdet)
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))
        (specialFormPreservingRealCongruenceContinuousMulEquiv
          F W).toHomeomorph
        (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W) x := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  change x ∈ realCrossChartAmbientSource I J C.toHomeomorph at hx
  change
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x =
      realCrossChartAmbientTransition I J C.toHomeomorph e x
  apply e.injective
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
    F hF hdet W x hx.1 hx.2]
  exact (realCrossChartAmbientTransition_apply I J C.toHomeomorph e x).symm

/-- The fixed-carrier transition maps the exact ambient source overlap into
the exact ambient target overlap. -/
theorem mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set.MapsTo
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W) := by
  intro x hx
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_crossChart
    F hF hdet W x hx]
  exact mapsTo_realCrossChartAmbientTransition
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W) hx


end PositiveDefiniteIntegralLattice
