import SMSFormula.SpecialOrthogonalRealCongruenceChartJacobian

/-!
# Point-centered factorization of real congruence chart transitions

This module records the exact represented points and the two moving-center
coordinate changes associated to an arbitrary transported/standard overlap
coordinate. It defines an explicit open ambient common domain, proves the
point-centered square throughout that domain, and records the resulting
eventual equality at the represented coordinate. Derivative composition is
done in a separate module.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source identity-chart coordinate represented by a transported target
coordinate. -/
def specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
  (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W).symm y

/-- The source group point represented by a transported target coordinate. -/
def specialFormPreservingSmoothRealCongruenceSourcePointAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1

/-- The target group point represented by a transported target coordinate. -/
def specialFormPreservingSmoothRealCongruenceTargetPointAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map (algebraMap ℚ ℝ)) :=
  ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
    F hF hdet W).symm y).1

/-- The represented target point is the congruence image of the represented
source point. -/
theorem specialFormPreservingSmoothRealCongruenceTargetPointAt_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y =
      specialFormPreservingRealCongruenceContinuousMulEquiv F W
        (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y) := by
  rfl

/-- The source identity coordinate followed by the chart centered at the
represented source point. -/
def specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    OpenPartialHomeomorph
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm.trans
    (specialFormPreservingSmoothRealChart F hF hdet
      (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y))

/-- The target identity-chart coordinate of an exact transported/standard
overlap coordinate. -/
def specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  ⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
      F hF hdet W y,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
      F hF hdet W y hy⟩

/-- The exact source of the target identity-to-represented-point transition,
pulled back to the fixed source tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W ⁻¹'
    ((specialFormPreservingSmoothRealSkewAdjointTransition
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
      (specialFormPreservingSmoothRealCongruenceTargetPointAt
        F hF hdet W y)).source)

/-- The target identity-to-represented-point transition, conjugated back to
the fixed source tangent carrier and kept as an ambient pointwise map. -/
def specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
    ((specialFormPreservingSmoothRealSkewAdjointTransition
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
      (specialFormPreservingSmoothRealCongruenceTargetPointAt
        F hF hdet W y))
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x))

/-- The pointwise inverse of the target point-centered transition on the
fixed source tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceTargetPointTransitionInvAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
    (((specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm.trans
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)
          (specialFormPreservingSmoothRealCongruenceTargetPointAt
            F hF hdet W y))).symm
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x))

/-- The represented source coordinate lies in its identity-to-point
transition. -/
theorem sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 ∈
      (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y).source := by
  rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt, OpenPartialHomeomorph.trans_source]
  constructor
  · exact (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).2
  · change specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y ∈
      (specialFormPreservingSmoothRealChart F hF hdet
        (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y)).source
    exact self_mem_specialFormPreservingSmoothRealChart_source F hF hdet _

/-- The source point-centered transition sends the represented coordinate to
zero. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 =
      0 := by
  rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt, OpenPartialHomeomorph.trans_apply]
  change
    specialFormPreservingSmoothRealChart F hF hdet
        (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y)
        (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y) =
      0
  exact specialFormPreservingSmoothRealChart_center F hF hdet _

/-- The inverse-tangent-congruence image of the standard coordinate lies in
the target point-centered transition. -/
theorem standardCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt F hF hdet W y hy).1 ∈
      specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt
        F hF hdet W y := by
  rw [specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt,
    Set.mem_preimage,
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply]
  change
    (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
      F hF hdet W y hy).1 ∈
      ((specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm.trans
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)
          (specialFormPreservingSmoothRealCongruenceTargetPointAt
            F hF hdet W y))).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨(specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
    F hF hdet W y hy).2, ?_⟩
  change
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
          F hF hdet W y hy).1 ∈
      (specialFormPreservingSmoothRealChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)
        (specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y)).source
  rw [specialFormPreservingSmoothRealCongruenceStandardCoordinateAt,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition_samePoint
      F hF hdet W y hy]
  exact self_mem_specialFormPreservingSmoothRealChart_source
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W) _

/-- The target point-centered transition sends the represented standard
coordinate to zero. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt_standardCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt F hF hdet W y
      ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt F hF hdet W y hy).1) =
      0 := by
  rw [specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt,
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply]
  let q :
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source :=
    ⟨specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y, hy⟩
  have hcenter :=
    specialFormPreservingSmoothRealChart_transition_to_self_apply_coordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1 q
  have hmiddle :
      (specialFormPreservingSmoothRealSkewAdjointTransition
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
        (specialFormPreservingSmoothRealCongruenceTargetPointAt
          F hF hdet W y))
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
          F hF hdet W y hy).1 =
        0 := by
    simpa only [specialFormPreservingSmoothRealSkewAdjointTransition,
      q, specialFormPreservingSmoothRealCongruenceStandardCoordinateAt,
      specialFormPreservingSmoothRealCongruenceChartAmbientTransition,
      specialFormPreservingSmoothRealCongruenceTargetPointAt] using hcenter
  rw [hmiddle]
  exact map_zero _

/-- The inverse source point-centered transition sends zero back to the
represented source coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_symm_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y).symm 0 =
      (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 := by
  calc
    (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y).symm 0 =
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y).symm
          (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y
            (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1) := by
              rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt]
    _ = (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 :=
      (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y).left_inv
        (sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y)

/-- The inverse target point-centered transition sends zero back to the
represented standard coordinate on the fixed source tangent carrier. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceTargetPointTransitionInvAt_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionInvAt
        F hF hdet W y 0 =
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt F hF hdet W y hy).1 := by
  let M :=
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm.trans
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)
          (specialFormPreservingSmoothRealCongruenceTargetPointAt
            F hF hdet W y))
  let z :=
    (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt
      F hF hdet W y hy).1
  have hz : z ∈ M.source := by
    have h :=
      standardCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
        F hF hdet W y hy
    simpa only [specialFormPreservingSmoothRealCongruenceTargetPointTransitionSourceAt,
      Set.mem_preimage,
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply,
      M, z] using h
  have hMz : M z = 0 := by
    have h := congrArg
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)
      (specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt_standardCoordinateAt
        F hF hdet W y hy)
    simpa only [specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt,
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply,
      map_zero, M, z] using h
  rw [specialFormPreservingSmoothRealCongruenceTargetPointTransitionInvAt, map_zero]
  congr 1
  calc
    M.symm 0 = M.symm (M z) := congrArg M.symm hMz.symm
    _ = z := M.left_inv hz

/-- At the represented source coordinate, the fixed cross-form transition is
the standard target identity coordinate, conjugated back to the fixed source
tangent carrier. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransition_sourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransition F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 =
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
        (specialFormPreservingSmoothRealCongruenceStandardCoordinateAt F hF hdet W y hy).1 := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_ambient]
  congr 1
  rw [show
    Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1 = y.1 by
      exact (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply y.1]
  change
    specialFormPreservingSmoothRealCongruenceChartAmbientTransitionFormula
        F hF hdet W y.1 =
      specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W y
  rw [specialFormPreservingSmoothRealCongruenceChartAmbientTransition_eq_forwardCoordinate
    F hF hdet W y hy]
  simp [specialFormPreservingSmoothRealCongruenceChartAmbientTransitionFormula,
    specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage,
    specialFormPreservingSmoothRealCongruenceChartAmbientInverseStage,
    coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply]
  rw [coe_specialFormPreservingSmoothRealIdentityChart_symm_eq_inverseCoordinateMatrix
    F hF hdet
    ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm y.1)
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).2]

/-- On the source identity-chart target, the fixed cross-form transition is
the target identity coordinate of group congruence.  The target-domain
hypothesis fixes the independently selected target chart. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈ (specialFormPreservingSmoothRealIdentityChart F hF hdet).target)
    (hcong :
      specialFormPreservingRealCongruenceContinuousMulEquiv F W
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source) :
    Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x) =
      specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x)) := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition,
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).apply_symm_apply,
    specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) _ hcong]
  apply congrArg
    (specialFormPreservingSmoothRealForwardCoordinate
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
  rw [specialFormPreservingRealCongruenceMatrixContinuousLinearMap_apply,
    coe_specialFormPreservingRealCongruenceContinuousMulEquiv_apply,
    coe_specialFormPreservingSmoothRealIdentityChart_symm_eq_inverseCoordinateMatrix
      F hF hdet x hx]

/-- The explicit ambient neighborhood on which the two point-centered
cross-form transition paths are simultaneously chart-defined. -/
def specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  {x |
    x ∈
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y).source ∧
    specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source ∧
    specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x) ∈
      (specialFormPreservingSmoothRealChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)
        (specialFormPreservingSmoothRealCongruenceTargetPointAt
          F hF hdet W y)).source ∧
    (specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y)⁻¹ *
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ∧
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y x ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ∧
    specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
          (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
            F hF hdet W y x)) ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source}

/-- The explicit point-centered commutation domain is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    IsOpen
      (specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
        F hF hdet W y) := by
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let p := specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y
  let q := specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y
  let S :=
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
      F hF hdet W y
  let K := specialFormPreservingSmoothRealChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W) q
  let g := fun x => C (I.symm x)
  let shift := fun x => p⁻¹ * I.symm x
  let gS := fun x => C (I.symm (S x))
  have hSI : Set.MapsTo (fun x => x) S.source I.target := by
    intro x hx
    change
      x ∈ (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y).source at hx
    rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt,
      OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  have hIinv : ContinuousOn (fun x => I.symm x) S.source :=
    I.symm.continuousOn.mono hSI
  have hg : ContinuousOn g S.source :=
    C.continuous.comp_continuousOn hIinv
  let A1 := S.source ∩ g ⁻¹' J.source
  have hA1 : IsOpen A1 :=
    hg.isOpen_inter_preimage S.open_source J.open_source
  let A2 := A1 ∩ g ⁻¹' K.source
  have hA1S : A1 ⊆ S.source := fun _ hx => hx.1
  have hA2 : IsOpen A2 :=
    (hg.mono hA1S).isOpen_inter_preimage hA1 K.open_source
  let A3 := A2 ∩ shift ⁻¹' I.source
  have hA2S : A2 ⊆ S.source := fun _ hx => hx.1.1
  have hshift : ContinuousOn shift A2 :=
    continuousOn_const.mul (hIinv.mono hA2S)
  have hA3 : IsOpen A3 :=
    hshift.isOpen_inter_preimage hA2 I.open_source
  let A4 := A3 ∩ S ⁻¹' I.target
  have hA3S : A3 ⊆ S.source := fun _ hx => hx.1.1.1
  have hA4 : IsOpen A4 :=
    (S.continuousOn.mono hA3S).isOpen_inter_preimage hA3 I.open_target
  have hA4S : A4 ⊆ S.source := fun _ hx => hx.1.1.1.1
  have hA4map : Set.MapsTo S A4 I.target := fun _ hx => hx.2
  have hgS : ContinuousOn gS A4 :=
    C.continuous.comp_continuousOn
      (I.symm.continuousOn.comp (S.continuousOn.mono hA4S) hA4map)
  have hfinal : IsOpen (A4 ∩ gS ⁻¹' J.source) :=
    hgS.isOpen_inter_preimage hA4 J.open_source
  have hset :
      specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
          F hF hdet W y =
        A4 ∩ gS ⁻¹' J.source := by
    ext x
    simp only [
      specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet,
      C, I, J, p, q, S, K, g, shift, gS, A1, A2, A3, A4,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact hfinal

/-- The point-centered cross-form square commutes throughout its explicit
ambient common chart domain. -/
theorem specialFormPreservingSmoothRealCongruencePointCentered_square
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
        F hF hdet W y) :
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
        F hF hdet W y
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x) =
      specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y x) := by
  rcases hx with ⟨hxS, hxcong, hxcongPoint, hxshift, hxS_target, hxS_cong⟩
  have hx_target :
      x ∈ (specialFormPreservingSmoothRealIdentityChart F hF hdet).target := by
    rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt,
      OpenPartialHomeomorph.trans_source] at hxS
    exact hxS.1
  have hPsi :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
      F hF hdet W x hx_target hxcong
  have hPsiS :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_identityChart
      F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y x) hxS_target hxS_cong
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let p := specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y
  let q := specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y
  let S :=
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
      F hF hdet W y
  let T :=
    specialFormPreservingSmoothRealSkewAdjointTransition
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1 q
  have hTsource :
      e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x) ∈ T.source := by
    change
      e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x) ∈
        (J.symm.trans
          (specialFormPreservingSmoothRealChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) q)).source
    rw [OpenPartialHomeomorph.trans_source, hPsi]
    constructor
    · exact J.map_source hxcong
    · change
        J.symm (J
          (specialFormPreservingRealCongruenceContinuousMulEquiv F W
            ((specialFormPreservingSmoothRealIdentityChart
              F hF hdet).symm x))) ∈
          (specialFormPreservingSmoothRealChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) q).source
      rw [J.left_inv hxcong]
      exact hxcongPoint
  have hSformula :
      S x = I (p⁻¹ * I.symm x) := by
    simpa only [S, I, p,
      specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt] using
      specialFormPreservingSmoothRealSkewAdjointTransition_apply
        F hF hdet 1 p x hxS
  have hTformula :
      T (e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x)) =
        J (q⁻¹ * J.symm
          (e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W x))) := by
    simpa only [T, J, q] using
      specialFormPreservingSmoothRealSkewAdjointTransition_apply
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1 q
        (e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x)) hTsource
  rw [specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt]
  apply e.injective
  rw [e.apply_symm_apply]
  rw [hTformula, hPsiS, hPsi]
  congr 1
  rw [J.left_inv hxcong]
  have hIshift : I.symm (S x) = p⁻¹ * I.symm x := by
    rw [hSformula, I.left_inv hxshift]
  rw [hIshift]
  change q⁻¹ * C (I.symm x) = C (p⁻¹ * I.symm x)
  have hq : q = C p := by
    simpa only [q, C, p] using
      specialFormPreservingSmoothRealCongruenceTargetPointAt_eq
        F hF hdet W y
  rw [hq]
  simp

/-- The represented source coordinate belongs to the ambient point-centered
commutation domain. -/
theorem sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
      F hF hdet W y).1 ∈
      specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
        F hF hdet W y := by
  let x :=
    (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
      F hF hdet W y).1
  let p := specialFormPreservingSmoothRealCongruenceSourcePointAt F hF hdet W y
  let q := specialFormPreservingSmoothRealCongruenceTargetPointAt F hF hdet W y
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  have hIx : I.symm x = p := by
    rfl
  have hq : q = C p := by
    simpa only [q, C, p] using
      specialFormPreservingSmoothRealCongruenceTargetPointAt_eq
        F hF hdet W y
  change
    x ∈
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y).source ∧
      C (I.symm x) ∈ J.source ∧
      C (I.symm x) ∈
        (specialFormPreservingSmoothRealChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) q).source ∧
      p⁻¹ * I.symm x ∈ I.source ∧
      specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y x ∈ I.target ∧
      C (I.symm
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y x)) ∈ J.source
  constructor
  · exact
      sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
        F hF hdet W y
  constructor
  · rw [hIx, ← hq]
    exact hy
  constructor
  · rw [hIx, ← hq]
    exact self_mem_specialFormPreservingSmoothRealChart_source
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) q
  constructor
  · rw [hIx]
    have hp : p⁻¹ * p = 1 := by simp
    rw [hp]
    change 1 ∈ (specialFormPreservingSmoothRealIdentityChart F hF hdet).source
    exact self_mem_specialFormPreservingSmoothRealChart_source F hF hdet 1
  constructor
  · rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt]
    exact zero_mem_specialFormPreservingSmoothRealIdentityChart_target F hF hdet
  · rw [specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt,
      specialFormPreservingSmoothRealIdentityChart_symm_zero, map_one]
    exact self_mem_specialFormPreservingSmoothRealChart_source
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1

/-- The neighborhood-level square is an eventual equality at its represented
source coordinate. This opaque form is the intended input to later
derivative composition, avoiding re-elaboration of the common domain. -/
theorem eventuallyEq_specialFormPreservingSmoothRealCongruencePointCentered
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    (fun x =>
      specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt
        F hF hdet W y
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x)) =ᶠ[
      nhds (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt
        F hF hdet W y).1]
    (fun x =>
      specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt
          F hF hdet W y x)) := by
  filter_upwards [
    (isOpen_specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
      F hF hdet W y).mem_nhds
        (sourceCoordinateAt_mem_specialFormPreservingSmoothRealCongruencePointCenteredCommutationSet
          F hF hdet W y hy)] with x hx
  exact specialFormPreservingSmoothRealCongruencePointCentered_square
    F hF hdet W y x hx

/-- The point-centered cross-form square commutes at its represented
coordinate.  This is a pointwise base-point theorem, not a neighborhood-level
commutation statement. -/
theorem specialFormPreservingSmoothRealCongruencePointCentered_square_at_sourceCoordinateAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy : y ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt F hF hdet W y
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1) =
      specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt F hF hdet W y
          (specialFormPreservingSmoothRealCongruenceSourceCoordinateAt F hF hdet W y).1) := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransition_sourceCoordinateAt F hF hdet W y hy,
    specialFormPreservingSmoothRealCongruenceTargetPointTransitionAt_standardCoordinateAt F hF hdet W y hy,
    specialFormPreservingSmoothRealCongruenceSourcePointTransitionAt_sourceCoordinateAt,
    specialFormPreservingSmoothRealCongruenceChartSourceTransition_zero]

end PositiveDefiniteIntegralLattice
