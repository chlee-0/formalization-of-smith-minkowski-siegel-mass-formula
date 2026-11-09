import SMSFormula.SpecialOrthogonalRealCongruenceOverlapMeasure

/-!
# Topology of ambient real congruence chart overlaps

The exact source and target overlap sets on the fixed source tangent carrier
are open and therefore measurable.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceAmbientOverlapTangentMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceAmbientOverlapTangentBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The exact ambient source overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :=
  isOpen_realCrossChartAmbientSource
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph

/-- The exact ambient target overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W) :=
  isOpen_realCrossChartAmbientTarget
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)

/-- The exact ambient source overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    F hF hdet W).measurableSet

/-- The exact ambient target overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
    F hF hdet W).measurableSet

end PositiveDefiniteIntegralLattice
