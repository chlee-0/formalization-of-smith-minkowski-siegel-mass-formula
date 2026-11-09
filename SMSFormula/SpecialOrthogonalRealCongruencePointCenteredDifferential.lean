import SMSFormula.SpecialOrthogonalRealCongruencePointCentered
import SMSFormula.SpecialOrthogonalRealTransitionConjugationDifferential

/-!
# Derivative factorization for point-centered real congruence charts

This module derives the derivative factorization from the neighborhood-level
commutation theorem, using small derivative certificates. The generic
chain-rule lemma is stated independently of the form-indexed tangent carriers.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

/-- An eventual commutative square and four component derivative
certificates equate the two complete chain-rule derivatives. -/
theorem hasFDerivAt_comp_eq_comp_of_eventuallyEq
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {P R S : E → E} {x : E}
    {DP DR DS DP₀ : E →L[𝕜] E}
    (heq : (fun z => R (P z)) =ᶠ[nhds x] fun z => P (S z))
    (hP : HasFDerivAt P DP x)
    (hR : HasFDerivAt R DR (P x))
    (hS : HasFDerivAt S DS x)
    (hP₀ : HasFDerivAt P DP₀ (S x)) :
    DR.comp DP = DP₀.comp DS := by
  have hleft := hR.comp x hP
  have hright := hP₀.comp x hS
  calc
    DR.comp DP = fderiv 𝕜 (fun z => R (P z)) x := hleft.fderiv.symm
    _ = fderiv 𝕜 (fun z => P (S z)) x := heq.fderiv_eq
    _ = DP₀.comp DS := hright.fderiv

/-- Three complete continuous-linear endomorphisms together with the
composition identity needed for point-centered Jacobian factorization. -/
structure ContinuousLinearCompositionCertificate
    (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  target : E →L[𝕜] E
  cross : E →L[𝕜] E
  source : E →L[𝕜] E
  comp_eq : target.comp cross = source

/-- A complete derivative-composition certificate factors the corresponding
endomorphism determinant. -/
theorem ContinuousLinearCompositionCertificate.det_target_mul_det_cross
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (c : ContinuousLinearCompositionCertificate 𝕜 E) :
    LinearMap.det c.target.toLinearMap * LinearMap.det c.cross.toLinearMap =
      LinearMap.det c.source.toLinearMap := by
  rw [← LinearMap.det_comp]
  apply congrArg LinearMap.det
  simpa using
    congrArg (fun f : E →L[𝕜] E => f.toLinearMap) c.comp_eq

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source moving-center transition has its actual derivative at the
represented source coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    HasFDerivAt
      (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y)
      (fderiv ℝ
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y)
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y).1)
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1 := by
  exact
    hasFDerivAt_specialFormPreservingSmoothRealSkewAdjointTransition
      F hF hdet 1
      (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y)
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1
      (sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y)

/-- The fixed cross-form transition has the stated derivative at the
represented source coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition_sourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    HasFDerivAt
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y).1)
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1 :=
  hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    F hF hdet W
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
      F hF hdet W y).1
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
      F hF hdet W y).2

/-- The fixed cross-form transition has identity derivative at the image of
the represented coordinate under its source moving-center transition. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition_at_sourcePointTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    HasFDerivAt
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule))
      (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y).1) := by
  rw [
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt]
  have h :=
    hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W 0
      (zero_mem_specialFormPreservingSmoothRealIdentityChart_target F hF hdet)
  simpa only [
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_zero]
    using h

/-- The fixed cross-form image of the represented source coordinate lies in
the exact source of the target moving-center transition. -/
theorem sourceTransition_sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y).1 ∈
      specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt
        F hF hdet W y := by
  let x :=
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
      F hF hdet W y).1
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let q := specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y
  have hxcommon :=
    sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
      F hF hdet W y hy
  have hxcong := hxcommon.2.1
  have hxcongPoint := hxcommon.2.2.1
  have hPx :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
      F hF hdet W x
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).2 hxcong
  rw [
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt,
    Set.mem_preimage, hPx]
  change
    J
      (specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x)) ∈
      (J.symm.trans
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) q)).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · exact J.map_source hxcong
  · change
      J.symm (J
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x))) ∈
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) q).source
    rw [J.left_inv hxcong]
    exact hxcongPoint

/-- The complete derivative of the target moving-center transition, conjugated
back to the fixed source tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  let F' := Matrix.skewAdjointCongruenceForm F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let q := specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y
  e.symm.toContinuousLinearMap.comp
    ((fderiv ℝ
      (specialFormPreservingSmoothRealSkewAdjointTransition
        F' (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1 q)
      (e x)).comp e.toContinuousLinearMap)

/-- The point-centered commutative square packages the three complete
fixed-carrier derivatives needed for determinant factorization. -/
def specialFormPreservingSmoothRealCongruencePointCenteredDerivativeCertificate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    ContinuousLinearCompositionCertificate ℝ
      ((skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) where
  target :=
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt
      F hF hdet W y
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
          F hF hdet W y).1)
  cross :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
      F hF hdet W
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1
  source :=
    fderiv ℝ
      (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y)
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1
  comp_eq := by
    have hcomp :=
      hasFDerivAt_comp_eq_comp_of_eventuallyEq
        (P :=
          specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W)
        (R :=
          specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
            F hF hdet W y)
        (S :=
          specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
            F hF hdet W y)
        (eventuallyEq_specialFormPreservingSmoothRealCongruencePointCentered
          F hF hdet W y hy)
        (hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition_sourceCoordinateAt
          F hF hdet W y)
        (hasFDerivAt_conjugate_specialFormPreservingSmoothRealSkewAdjointTransition_of_mem_preimage
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
          (specialFormPreservingSmoothRealCongruenceTargetPointAt
            F hF hdet W y)
          (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
              F hF hdet W y).1)
          (sourceTransition_sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt
            F hF hdet W y hy))
        (hasFDerivAt_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt
          F hF hdet W y)
        (hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition_at_sourcePointTransition
          F hF hdet W y)
    calc
      _ = (ContinuousLinearMap.id ℝ
          ((skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule)).comp
          (fderiv ℝ
            (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
              F hF hdet W y)
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
              F hF hdet W y).1) := hcomp
      _ = _ := by
        ext z
        rfl

/-- The point-centered square factors the determinants of its three complete
fixed-carrier derivatives. -/
theorem det_target_mul_det_cross_eq_det_source_specialFormPreservingSmoothRealCongruencePointCentered
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    LinearMap.det
        (specialFormPreservingSmoothRealCongruenceTargetPointTransitionDerivativeAt
          F hF hdet W y
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
              F hF hdet W y).1)).toLinearMap *
      LinearMap.det
        (specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
          F hF hdet W
          (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
            F hF hdet W y).1).toLinearMap =
      LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
            F hF hdet W y)
          (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
            F hF hdet W y).1).toLinearMap := by
  exact
    ContinuousLinearCompositionCertificate.det_target_mul_det_cross
      (specialFormPreservingSmoothRealCongruencePointCenteredDerivativeCertificate
        F hF hdet W y hy)

end PositiveDefiniteIntegralLattice
