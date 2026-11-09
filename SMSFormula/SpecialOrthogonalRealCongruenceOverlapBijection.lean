import SMSFormula.SpecialOrthogonalRealCongruenceOverlapInverseMaps

/-!
# Bijection of ambient real congruence chart overlaps
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The explicit inverse is a left inverse on the exact ambient source
overlap. -/
theorem leftInverseOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set.LeftInvOn
      (specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) := by
  intro x hx
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_crossChart
    F hF hdet W x hx]
  exact leftInverseOn_realCrossChartAmbientTransition
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W) hx

/-- The explicit inverse is a right inverse on the exact ambient target
overlap. -/
theorem rightInverseOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set.RightInvOn
      (specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W) := by
  intro z hz
  have hinv :=
    mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
      F hF hdet W hz
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_crossChart
    F hF hdet W
      (specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W z) hinv]
  exact rightInverseOn_realCrossChartAmbientTransition
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W) hz

/-- The fixed-carrier transition is injective on the exact ambient source
overlap. -/
theorem injOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set.InjOn
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :=
  (leftInverseOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    F hF hdet W).injOn

/-- The image of the exact ambient source overlap is exactly the ambient
target overlap. -/
theorem image_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W ''
        specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W =
      specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
      F hF hdet W hx
  · intro z hz
    exact ⟨
      specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W z,
      mapsTo_specialFormPreservingSmoothRealCongruenceAmbientSourceTransitionInv
        F hF hdet W hz,
      rightInverseOn_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
        F hF hdet W hz⟩

end PositiveDefiniteIntegralLattice
