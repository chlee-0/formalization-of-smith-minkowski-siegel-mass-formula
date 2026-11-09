import SMSFormula.SpecialOrthogonalRealCongruenceOverlapBijection

/-!
# Differential on the ambient real congruence chart overlap
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- On the exact ambient overlap, the full derivative is also a
derivative within the overlap source. -/
theorem hasFDerivWithinAt_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    HasFDerivWithinAt
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (fderiv ℝ
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W) x)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) x := by
  rw [fderiv_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    F hF hdet W x hx.1]
  exact
    (hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W x hx.1).hasFDerivWithinAt

end PositiveDefiniteIntegralLattice
