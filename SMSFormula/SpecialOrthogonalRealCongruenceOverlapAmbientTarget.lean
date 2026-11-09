import SMSFormula.SpecialOrthogonalRealCongruenceOverlapAmbientCoordinate

/-!
# Target-coordinate facts for the ambient real congruence overlap
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The tangent-congruence image of `Psi_W x` belongs to the target
identity-chart target. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_mem_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x) ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  exact
    mem_target_of_mem_realCrossChartAmbientTarget I J C.toHomeomorph e
      (mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
        F hF hdet W hx)

/-- The target-coordinate subtype represented by `Psi_W x` equals
the independently selected standard coordinate of the transported point. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_targetCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    (⟨Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x),
      specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_mem_target
        F hF hdet W x hx⟩ :
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target) =
    specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
      F hF hdet W
      (specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
        F hF hdet W x hx)
      (specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate_mem_overlap
        F hF hdet W x hx) := by
  apply Subtype.ext
  exact
    (specialFormPreservingSmoothRealCongruenceAmbientTransition_ambientTransported
      F hF hdet W x hx).symm

end PositiveDefiniteIntegralLattice
