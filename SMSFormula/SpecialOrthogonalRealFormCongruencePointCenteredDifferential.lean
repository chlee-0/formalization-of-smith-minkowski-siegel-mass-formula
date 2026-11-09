import SMSFormula.SpecialOrthogonalRealFormCongruencePointCentered
import SMSFormula.SpecialOrthogonalRealCongruencePointCenteredDifferential

/-!
# Derivative factorization for explicit real-congruence point-centered charts

This module consumes the explicit-real neighborhood commutation theorem through
small component derivative certificates.  All derivatives are complete
endomorphisms of the fixed source tangent carrier.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source moving-center transition has its actual derivative at the
represented source coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x)
      (fderiv ℝ
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x) x) x := by
  exact
    hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet 1
      (specialFormPreservingSmoothRealFormCongruenceSourcePointAt
        F F' hF hdet hF' hdet' c x)
      x
      (sourceCoordinate_mem_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x hx.1)

/-- The explicit-real cross transition has its chain-rule derivative at the
represented source coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_self
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c x) x :=
  hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    F F' hF hdet hF' hdet' c x hx

/-- After moving the represented source coordinate to zero, the cross
transition has identity derivative. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at_sourcePointTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule))
      (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x x) := by
  rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self]
  have h :=
    hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c 0
      (zero_mem_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
  simpa only [
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative_zero]
    using h

/-- Complete derivative of the target moving-center transition, conjugated
back to the fixed source tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  c.tangentEquiv.symm.toContinuousLinearMap.comp
    ((fderiv ℝ
      (specialFormPreservingSmoothRealSkewAdjointTransition
        F' hF' hdet' 1
        (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x))
      (c.tangentEquiv y)).comp c.tangentEquiv.toContinuousLinearMap)

/-- The target moving-center transition has the conjugated same-form
derivative at the represented cross-transition coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt_ambientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
        F F' hF hdet hF' hdet' c x)
      (specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
        F F' hF hdet hF' hdet' c x
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c x))
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x) := by
  exact
    hasFDerivAt_conjugate_specialFormPreservingSmoothRealSkewAdjointTransition_of_mem_preimage
      F' hF' hdet' 1
      (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x)
      c.tangentEquiv
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x)
      (ambientTransitionAt_mem_specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionSourceAt
        F F' hF hdet hF' hdet' c x hx)

/-- The explicit-real point-centered square packages the three complete
fixed-carrier derivatives needed for determinant factorization. -/
def specialFormPreservingSmoothRealFormCongruencePointCenteredDerivativeCertificate
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    ContinuousLinearCompositionCertificate ℝ
      ((skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) where
  target :=
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
      F F' hF hdet hF' hdet' c x
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x)
  cross :=
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
      F F' hF hdet hF' hdet' c x
  source :=
    fderiv ℝ
      (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x) x
  comp_eq := by
    have hcomp :=
      hasFDerivAt_comp_eq_comp_of_eventuallyEq
        (P :=
          specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c)
        (R :=
          specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
            F F' hF hdet hF' hdet' c x)
        (S :=
          specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
            F F' hF hdet hF' hdet' c x)
        (eventuallyEq_specialFormPreservingSmoothRealFormCongruencePointCentered
          F F' hF hdet hF' hdet' c x hx)
        (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_self
          F F' hF hdet hF' hdet' c x hx)
        (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt_ambientTransition
          F F' hF hdet hF' hdet' c x hx)
        (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self
          F F' hF hdet hF' hdet' c x hx)
        (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at_sourcePointTransition
          F F' hF hdet hF' hdet' c x)
    calc
      _ = (ContinuousLinearMap.id ℝ
          ((skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule)).comp
          (fderiv ℝ
            (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
              F F' hF hdet hF' hdet' c x) x) := hcomp
      _ = _ := by
        ext z
        rfl

/-- The point-centered square factors the determinants of its three complete
fixed-carrier derivatives. -/
theorem det_target_mul_det_cross_eq_det_source_specialFormPreservingSmoothRealFormCongruencePointCentered
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    LinearMap.det
        (specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionDerivativeAt
          F F' hF hdet hF' hdet' c x
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c x)).toLinearMap *
      LinearMap.det
        (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
          F F' hF hdet hF' hdet' c x).toLinearMap =
      LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
            F F' hF hdet hF' hdet' c x) x).toLinearMap := by
  exact
    ContinuousLinearCompositionCertificate.det_target_mul_det_cross
      (specialFormPreservingSmoothRealFormCongruencePointCenteredDerivativeCertificate
        F F' hF hdet hF' hdet' c x hx)

end PositiveDefiniteIntegralLattice
