import SMSFormula.SpecialOrthogonalRealCongruenceOverlapAmbientTarget

/-!
# Ambient density cocycle for real congruence chart overlaps

The subtype density cocycle is rewritten on the fixed source tangent
carrier.  This is the form used by the ambient nonlinear
change-of-variables theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- On the exact ambient source overlap, the source density is the target
density after `Psi_W`, times the absolute Frechet Jacobian. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientDensityCocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
        F hF hdet x =
      specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
          F hF hdet W
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W x) *
        ENNReal.ofReal
          |(fderiv ℝ
            (specialFormPreservingSmoothRealCongruenceChartSourceTransition
              F hF hdet W) x).det| := by
  let y :=
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate
      F hF hdet W x hx
  have hy :
      y ∈
        specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
          F hF hdet W :=
    specialFormPreservingSmoothRealCongruenceAmbientTransportedCoordinate_mem_overlap
      F hF hdet W x hx
  rw [
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity_eq
      F hF hdet x hx.1,
    specialFormPreservingSmoothRealCongruenceAmbientTargetDensity_eq
      F hF hdet W
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_mem_target
        F hF hdet W x hx),
    specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_targetCoordinate
      F hF hdet W x hx]
  simpa [y,
    specialFormPreservingSmoothRealCongruenceSourceCoordinateAt_ambientTransported
      F hF hdet W x hx,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_eq_fderiv
      F hF hdet W x hx.1] using
    specialFormPreservingSmoothRealCongruenceChartDensityCocycle_source
      F hF hdet W y hy

end PositiveDefiniteIntegralLattice
