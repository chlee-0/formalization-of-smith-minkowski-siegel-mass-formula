import SMSFormula.SpecialOrthogonalRealChartMeasure

/-!
# Conjugating real special-orthogonal chart derivatives

This module differentiates a same-form chart transition after
conjugating its tangent coordinates through an arbitrary continuous linear
equivalence. It is independent of rational congruence data.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Conjugating a same-form real chart transition through a continuous linear
equivalence conjugates its Frechet derivative by the same equivalence. -/
theorem hasFDerivAt_conjugate_specialFormPreservingSmoothRealSkewAdjointTransition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (e : E ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (x : E)
    (hx : e x ∈
      (specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h).source) :
    HasFDerivAt
      (fun z =>
        e.symm
          (specialFormPreservingSmoothRealSkewAdjointTransition
            F hF hdet g h (e z)))
      (e.symm.toContinuousLinearMap.comp
        ((fderiv ℝ
          (specialFormPreservingSmoothRealSkewAdjointTransition
            F hF hdet g h) (e x)).comp
          e.toContinuousLinearMap))
      x := by
  exact
    e.symm.hasFDerivAt.comp x
      ((hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h (e x) hx).comp x e.hasFDerivAt)

/-- The conjugated transition derivative with its domain hypothesis stated as
membership in the pulled-back source.  This form avoids re-elaborating the
equivalent image-membership proposition in later form-indexed statements. -/
theorem hasFDerivAt_conjugate_specialFormPreservingSmoothRealSkewAdjointTransition_of_mem_preimage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (e : E ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (x : E)
    (hx : x ∈ e ⁻¹'
      (specialFormPreservingSmoothRealSkewAdjointTransition
        F hF hdet g h).source) :
    HasFDerivAt
      (fun z =>
        e.symm
          (specialFormPreservingSmoothRealSkewAdjointTransition
            F hF hdet g h (e z)))
      (e.symm.toContinuousLinearMap.comp
        ((fderiv ℝ
          (specialFormPreservingSmoothRealSkewAdjointTransition
            F hF hdet g h) (e x)).comp
          e.toContinuousLinearMap))
      x := by
  change e x ∈
    (specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet g h).source at hx
  exact
    hasFDerivAt_conjugate_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet g h e x hx

end PositiveDefiniteIntegralLattice
