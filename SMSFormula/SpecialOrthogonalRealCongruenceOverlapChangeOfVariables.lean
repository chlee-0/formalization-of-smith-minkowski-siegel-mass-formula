import SMSFormula.SpecialOrthogonalRealCongruenceOverlapDifferential

/-!
# Change of variables on ambient real congruence chart overlaps
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapChangeOfVariablesMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapChangeOfVariablesBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The real nonlinear change-of-variables theorem on the fixed source
tangent carrier.  The Jacobian is kept explicit; the congruence basis scalar
enters only when coordinate measures are transported between carriers. -/
theorem map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
            F hF hdet W)).withDensity
          fun x => ENNReal.ofReal
            |(fderiv ℝ
              (specialFormPreservingSmoothRealCongruenceChartSourceTransition
                F hF hdet W) x).det|) =
      (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
          F hF hdet W) := by
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let U :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  let V :=
    specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
      F hF hdet W
  let Ψ :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0
  have hderiv : ∀ x ∈ U,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) U x := by
    intro x hx
    exact
      hasFDerivWithinAt_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
        F hF hdet W x hx
  have hmap := @MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule
    _ _ _ U Ψ (fun x => fderiv ℝ Ψ x)
    (realCongruenceOverlapChangeOfVariablesMeasurableSpace F)
    (realCongruenceOverlapChangeOfVariablesBorelSpace F) μ
    (Matrix.skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure F 0)
    (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W).nullMeasurableSet
    hderiv
    (injOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
      F hF hdet W)
  have himage : Ψ '' U = V :=
    image_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  simpa [μ, U, V, Ψ, himage] using hmap

end PositiveDefiniteIntegralLattice
