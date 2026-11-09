import SMSFormula.SpecialOrthogonalRealCongruenceOverlapAmbientDensity

/-!
# Coordinates connecting the ambient and cross-form real congruence overlaps
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A fixed-source ambient overlap coordinate, transported to the
cross-form chart target. -/
def specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W :=
  specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W ⟨x, hx.1⟩

/-- The transported coordinate belongs to the exact transported/standard
overlap. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate_mem_overlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
        F hF hdet W x hx ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  change x ∈ realCrossChartAmbientSource I J C.toHomeomorph at hx
  change
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm
      (specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
        F hF hdet W x hx)).1 ∈ J.source
  rw [coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply,
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate,
    coe_specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph_apply,
    e.symm_apply_apply]
  exact hx.2

/-- Pulling the transported coordinate back through tangent congruence
recovers the original fixed-source coordinate. -/
theorem specialFormPreservingSmoothRealCongruenceSourceCoordinateAt_ambientTransported
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
          F hF hdet W x hx) =
      ⟨x, hx.1⟩ := by
  rw [specialFormPreservingSmoothRealCongruenceSourceCoordinateAt,
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate,
    (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
      F hF hdet W).symm_apply_apply]

/-- The standard target coordinate represented by the transported point is
the tangent-congruence image of `Psi_W x`. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientTransition_ambientTransported
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
          F hF hdet W x hx) =
      Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  change x ∈ realCrossChartAmbientSource I J C.toHomeomorph at hx
  rw [specialFormPreservingSmoothRealCongruenceChartAmbientTransition,
    coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply,
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate,
    coe_specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph_apply,
    e.symm_apply_apply]
  exact
    (specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
      F hF hdet W x hx.1 hx.2).symm

end PositiveDefiniteIntegralLattice
