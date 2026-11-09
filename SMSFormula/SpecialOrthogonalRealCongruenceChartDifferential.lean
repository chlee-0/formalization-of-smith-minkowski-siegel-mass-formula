import SMSFormula.SpecialOrthogonalRealCongruenceChartOverlap
import SMSFormula.SkewAdjointRealCongruenceCompatibility

/-!
# Differential of the real congruence-chart transition

For `F' = Wᵀ F W`, this module unfolds the transition from the transported
`F`-chart to the independently chosen identity chart for `F'` into maps on
the ambient target skew-adjoint space. It also records the exact staged
chain-rule derivative map. All comparisons with the exact overlap remain
pointwise, avoiding function equalities between nested subtypes.

The `HasFDerivAt` statement for the staged derivative is not stated here.
The inverse-chart and inverse-congruence derivative results are in the
imported modules, but restating their composition over this dependent
cross-form carrier runs into kernel reduction limits.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ContDiff

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem congruenceDifferential_isSymm_map_algebraMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    (F.map (algebraMap ℚ ℝ)).IsSymm :=
  hF.map _

private theorem congruenceDifferential_det_map_algebraMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℝ)).det ≠ 0 := by
  have hmap : algebraMap ℚ ℝ F.det ≠ 0 := by
    intro hz
    apply hdet
    apply (algebraMap ℚ ℝ).injective
    simpa using hz
  have heq :
      (F.map (algebraMap ℚ ℝ)).det = algebraMap ℚ ℝ F.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((algebraMap ℚ ℝ).map_det F).symm
  rwa [heq]

private theorem congruenceDifferential_ringChar_ne_two :
    ringChar ℝ ≠ 2 := by
  norm_num [ringChar.eq ℝ]

/-- Matrix conjugation underlying the real group congruence, as a continuous
linear map on the ambient matrix space. -/
def specialFormPreservingRealCongruenceMatrixContinuousLinearMap
    (W : GL (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
    (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ)
    (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ)

@[simp]
theorem specialFormPreservingRealCongruenceMatrixContinuousLinearMap_apply
    (W : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℝ) :
    specialFormPreservingRealCongruenceMatrixContinuousLinearMap W A =
      (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ) * A *
        (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- Matrix congruence fixes the matrix identity. -/
@[simp]
theorem specialFormPreservingRealCongruenceMatrixContinuousLinearMap_one
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
      (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  change
    (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ) * 1 *
      (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) = 1
  rw [show rationalMatrixUnitReal W⁻¹ =
    (rationalMatrixUnitReal W)⁻¹ by
      simp [rationalMatrixUnitReal]]
  have hunit :
      (rationalMatrixUnitReal W)⁻¹ * rationalMatrixUnitReal W =
        (1 : GL (Fin n) ℝ) := by
    group
  have h := congrArg
    (fun U : GL (Fin n) ℝ => (U : Matrix (Fin n) (Fin n) ℝ))
    hunit
  simpa only [Matrix.mul_one] using h

/-- The matrix underlying the inverse real identity chart is the
ambient inverse-coordinate formula. -/
theorem coe_specialFormPreservingSmoothRealIdentityChart_symm_eq_inverseCoordinateMatrix
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).target) :
    (((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y).1.1.1 :
        Matrix (Fin n) (Fin n) ℝ) =
      specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet y := by
  have htarget :
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target =
        Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
          (F.map (algebraMap ℚ ℝ))
          (congruenceDifferential_isSymm_map_algebraMap F hF)
          (congruenceDifferential_det_map_algebraMap_ne_zero F hdet)
          congruenceDifferential_ringChar_ne_two :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
      (F.map (algebraMap ℚ ℝ))
      (congruenceDifferential_isSymm_map_algebraMap F hF)
      (congruenceDifferential_det_map_algebraMap_ne_zero F hdet)
      congruenceDifferential_ringChar_ne_two 1
  let yc : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ))
      (congruenceDifferential_isSymm_map_algebraMap F hF)
      (congruenceDifferential_det_map_algebraMap_ne_zero F hdet)
      congruenceDifferential_ringChar_ne_two :=
    ⟨y, htarget ▸ hy⟩
  have h :=
    coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
      (F.map (algebraMap ℚ ℝ))
      (congruenceDifferential_isSymm_map_algebraMap F hF)
      (congruenceDifferential_det_map_algebraMap_ne_zero F hdet)
      congruenceDifferential_ringChar_ne_two 1 yc
  convert h using 1
  all_goals simp [yc, specialFormPreservingSmoothRealInverseCoordinateMatrix]

/-- The first two ambient stages: inverse tangent congruence followed by the
source inverse chart. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientInverseStage
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) : Matrix (Fin n) (Fin n) ℝ :=
  specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet
    ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm y)

/-- The first three ambient stages, including matrix conjugation. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) : Matrix (Fin n) (Fin n) ℝ :=
  specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
    (specialFormPreservingSmoothRealCongruenceChartAmbientInverseStage
      F hF hdet W y)

/-- The cross-form transition written on the full target skew-adjoint space:
inverse tangent congruence, source inverse chart, matrix conjugation, and the
target-form forward coordinate. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientTransitionFormula
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule :=
  specialFormPreservingSmoothRealForwardCoordinate
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
    (specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage
      F hF hdet W y)

/-- On the exact transported overlap, the existing subtype transition is the
target-form forward coordinate of its represented group matrix. -/
theorem specialFormPreservingSmoothRealCongruenceChartAmbientTransition_eq_forwardCoordinate
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy :
      y ∈ specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W y =
      specialFormPreservingSmoothRealForwardCoordinate
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)
        (((specialFormPreservingSmoothRealCongruenceChartHomeomorph
          F hF hdet W).symm y).1.1.1.1 :
            Matrix (Fin n) (Fin n) ℝ) := by
  rw [specialFormPreservingSmoothRealCongruenceChartAmbientTransition]
  exact specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y).1 hy

/-- The exact ambient set on which the cross-form transition formula is analytic. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientTransitionSmoothSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set ((skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :=
  specialFormPreservingSmoothRealCongruenceChartTargetSet F hF hdet W

/-- The exact ambient smoothness set is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartAmbientTransitionSmoothSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceChartAmbientTransitionSmoothSet
        F hF hdet W) :=
  isOpen_specialFormPreservingSmoothRealCongruenceChartTargetSet F hF hdet W

/-- Derivative of inverse tangent congruence followed by the source inverse
chart. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientInverseStageDerivative
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
  (fderiv ℝ
    (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
    ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
      F W).symm y)).comp
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
      F W).symm.toContinuousLinearMap

/-- Derivative after adding ambient matrix conjugation. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStageDerivative
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
  (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W).comp
    (specialFormPreservingSmoothRealCongruenceChartAmbientInverseStageDerivative
      F hF hdet W y)

/-- The explicit chain-rule derivative of the ambient cross-form transition. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDerivative
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (fderiv ℝ
    (specialFormPreservingSmoothRealForwardCoordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage
      F hF hdet W y)).comp
    (specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStageDerivative
      F hF hdet W y)

/-- The cross-form transition conjugated back to the fixed source tangent
model. Both domain and codomain now depend only on `F`. -/
def specialFormPreservingSmoothRealCongruenceChartSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
    (specialFormPreservingSmoothRealForwardCoordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
      (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x)))

/-- The fixed-carrier cross-form transition fixes its central coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransition_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W 0 = 0 := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition,
    specialFormPreservingSmoothRealInverseCoordinateMatrix_zero,
    specialFormPreservingRealCongruenceMatrixContinuousLinearMap_one]
  have hzero :=
    specialFormPreservingSmoothRealForwardCoordinate_one_add
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
      (0 : (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule)
  simpa using congrArg
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm hzero

/-- The fixed source identity-chart target is the exact smooth domain of the
source-model transition. -/
def specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).target

/-- The source-model smoothness set is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).open_target

/-- The fixed-carrier cross-form transition is maximally smooth on the source
identity-chart target. -/
theorem contDiffOn_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet) := by
  have hinv :=
    contDiffOn_specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet 1
  have hmatrix :=
    (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W).contDiff
      |>.comp_contDiffOn hinv
  have hforward :=
    (contDiff_specialFormPreservingSmoothRealForwardCoordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).comp_contDiffOn hmatrix
  have houter :=
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
      F W).symm.contDiff.comp_contDiffOn hforward
  simpa only [
    specialFormPreservingSmoothRealCongruenceChartSourceTransition,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet,
    specialFormPreservingSmoothRealIdentityChart] using houter

/-- Conjugating the ambient target transition by tangent congruence gives the
fixed-carrier source transition, pointwise. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x =
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
        (specialFormPreservingSmoothRealCongruenceChartAmbientTransitionFormula
          F hF hdet W
            (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x)) := by
  simp [specialFormPreservingSmoothRealCongruenceChartSourceTransition,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransitionFormula,
    specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage,
    specialFormPreservingSmoothRealCongruenceChartAmbientInverseStage]

/-- Explicit chain-rule derivative of the fixed-carrier source transition. -/
def specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
      F W).symm.toContinuousLinearMap.comp
    ((fderiv ℝ
      (specialFormPreservingSmoothRealForwardCoordinate
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W))
      (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x))).comp
      ((specialFormPreservingRealCongruenceMatrixContinuousLinearMap W).comp
        (fderiv ℝ
          (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
          x)))

/-- At the central coordinate, the fixed-carrier cross-form transition has
identity derivative.  The source inverse chart contributes tangent
inclusion, matrix congruence intertwines the two tangent carriers, and the
target forward chart cancels its tangent inclusion. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  have hinv :
      fderiv ℝ
        (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet) 0 =
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL :=
    (hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix_zero
      F hF hdet).fderiv
  have hmatrix :
      (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W).comp
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL =
        (skewAdjointMatricesLieSubalgebra
          ((Matrix.skewAdjointCongruenceForm F W).map
            (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
          e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro X
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL',
      specialFormPreservingRealCongruenceMatrixContinuousLinearMap_apply,
      e] using
        (coe_skewAdjointRealCongruenceContinuousLinearEquiv_apply
          F W X).symm
  have hfwd :=
    fderiv_specialFormPreservingSmoothRealForwardCoordinate_one_comp_subtypeL
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  have hmiddle :
      (fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)) 1).comp
          ((skewAdjointMatricesLieSubalgebra
            ((Matrix.skewAdjointCongruenceForm F W).map
              (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
            e.toContinuousLinearMap) =
        e.toContinuousLinearMap := by
    rw [← ContinuousLinearMap.comp_assoc, hfwd]
    simp
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative,
    hinv, specialFormPreservingSmoothRealInverseCoordinateMatrix_zero,
    specialFormPreservingRealCongruenceMatrixContinuousLinearMap_one,
    hmatrix, hmiddle]
  simp [e]

/-- The fixed-carrier source transition has the explicit chain-rule derivative
at every point of the source identity-chart target. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet) :
    HasFDerivAt
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W x) x := by
  have hinv :=
    hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet 1 x hx
  have hmatrix :=
    (specialFormPreservingRealCongruenceMatrixContinuousLinearMap
      W).hasFDerivAt.comp x hinv
  have hfwd : HasFDerivAt
      (specialFormPreservingSmoothRealForwardCoordinate
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W))
      (fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))
        (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
          (specialFormPreservingSmoothRealInverseCoordinateMatrix
            F hF hdet x)))
      (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x)) := by
    apply DifferentiableAt.hasFDerivAt
    exact
      ((contDiff_specialFormPreservingSmoothRealForwardCoordinate
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).differentiable
        (by simp)).differentiableAt
  have hinner : HasFDerivAt
      (fun z =>
        specialFormPreservingSmoothRealForwardCoordinate
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)
          (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
            (specialFormPreservingSmoothRealInverseCoordinateMatrix
              F hF hdet z)))
      ((fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))
        (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
          (specialFormPreservingSmoothRealInverseCoordinateMatrix
            F hF hdet x))).comp
        ((specialFormPreservingRealCongruenceMatrixContinuousLinearMap W).comp
          (fderiv ℝ
            (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
            x))) x := by
    simpa only [Function.comp_apply] using hfwd.comp x hmatrix
  have houter :=
    Matrix.hasFDerivAt_skewAdjointRealCongruenceContinuousLinearEquiv_symm
      F W
        (specialFormPreservingSmoothRealForwardCoordinate
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)
          (specialFormPreservingRealCongruenceMatrixContinuousLinearMap W
            (specialFormPreservingSmoothRealInverseCoordinateMatrix
              F hF hdet x)))
  simpa only [specialFormPreservingSmoothRealCongruenceChartSourceTransition,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative,
    Function.comp_apply] using houter.comp x hinner

/-- On the exact source smoothness set, the ambient Frechet derivative is the
fixed-carrier chain-rule endomorphism. -/
theorem fderiv_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet) :
    fderiv ℝ
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W) x =
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W x :=
  (hasFDerivAt_specialFormPreservingSmoothRealCongruenceChartSourceTransition
    F hF hdet W x hx).fderiv

/-- The actual Frechet derivative of the fixed-carrier transition at its
central coordinate is the identity. -/
theorem fderiv_specialFormPreservingSmoothRealCongruenceChartSourceTransition_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    fderiv ℝ
      (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W) 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  have hzero : (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) ∈
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet := by
    rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet,
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target]
    exact Matrix.zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ))
      (congruenceDifferential_isSymm_map_algebraMap F hF)
      (congruenceDifferential_det_map_algebraMap_ne_zero F hdet)
      congruenceDifferential_ringChar_ne_two
  rw [fderiv_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W 0 hzero,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_zero]

end PositiveDefiniteIntegralLattice
