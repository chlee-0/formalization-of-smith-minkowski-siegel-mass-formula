import SMSFormula.PadicCayleyTranslatedChartOverlapMeasure
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure

/-!
# Determinant orientation for weighted p-adic Cayley overlaps

This module factors each exact translated source-overlap density measure into
its coordinate measure and the Cayley scalar.  That scalar is the inverse
determinant modulus of the forward Cayley differential.  The differential-form
density is therefore its reciprocal.

The inverse-density algebra below is not the differential measure needed for
chart gluing: its reciprocal source weight would square the raw transition's
reciprocal pushforward scalar.  The differential measure instead has the
cocycle

`differentialSource = differentialTarget ∘ transition * |det D transition|`

and hence reduces to the bare coordinate pushforward weighted by the forward
determinant modulus.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapReductionSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapReductionSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The Cayley Jacobian density restricted to an exact translated source
overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
  (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ENNReal :=
  Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F X.1

theorem measurable_skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
        p n F hF c d) := by
  exact
    (Matrix.measurable_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
      p n F).comp
      (continuous_subtype_val.comp continuous_subtype_val).measurable

/-- The differential-form density on an overlap is the reciprocal of the
coordinate pushforward scalar. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ENNReal :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
    p n F hF c d X)⁻¹

theorem
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
        p n F hF c d) :=
  (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
    p n F hF c d).inv

/-- The correctly oriented differential measure on one exact overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d).withDensity
    (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
      p n F hF c d)

/-- The reciprocal determinant modulus dictated by the source-form overlap
density cocycle. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ENNReal :=
  (‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ENNReal)⁻¹

/-- The forward determinant modulus of the exact overlap transition.  This,
not its reciprocal, is the source weight which cancels the raw transition's
reciprocal Haar scaling. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ENNReal :=
  (‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ENNReal)

private theorem transitionDeterminantModulus_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ENNReal) ≠ 0 := by
  rw [ENNReal.coe_ne_zero, ne_eq, nnnorm_eq_zero]
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

private theorem transitionDeterminantModulus_ne_top
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ENNReal) ≠ ⊤ :=
  ENNReal.coe_ne_top

theorem skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal_cocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
        p n F hF c d X =
      skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
          p n F hF d c
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X) *
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
          p n F hF c d X := by
  let D : ENNReal :=
    (‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ENNReal)
  let source : ENNReal :=
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF c d X
  let target : ENNReal :=
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X)
  have hD0 : D ≠ 0 :=
    transitionDeterminantModulus_ne_zero p n F hF c d X
  have hDtop : D ≠ ⊤ :=
    transitionDeterminantModulus_ne_top p n F hF c d X
  have hcenter :=
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_center_change
      F p hFsymm hF c d X
  rw [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph,
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph]
      at hcenter
  have hcenter' : target = source * D := by
    simpa [target, source, D,
      skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal]
      using hcenter
  change source = target * D⁻¹
  calc
    source = source * 1 := (mul_one source).symm
    _ = source * (D * D⁻¹) := by
      rw [ENNReal.mul_inv_cancel hD0 hDtop]
    _ = (source * D) * D⁻¹ := by ac_rfl
    _ = target * D⁻¹ := by rw [hcenter']

/-- The reciprocal transition modulus is measurable on the exact overlap. -/
theorem
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hF c d) := by
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d
  let source :=
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF c d
  let target :=
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF d c
  have hsource : Measurable source :=
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF c d
  have htarget : Measurable (target ∘ T) :=
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF d c).comp T.measurable
  have hratio :
      ∀ X,
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
            p n F hF c d X =
          ((target ∘ T) X * (source X)⁻¹)⁻¹ := by
    intro X
    have h :=
      coe_nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_targetDensity_ratio
        F p hFsymm hF c d X
    rw [
      padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph,
      padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph]
        at h
    exact congrArg Inv.inv h
  rw [show
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hF c d =
      fun X => ((target ∘ T) X * (source X)⁻¹)⁻¹ by
        funext X
        exact hratio X]
  exact (htarget.mul hsource.inv).inv

/-- The forward transition determinant modulus is measurable. -/
theorem
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
        p n F hF c d) := by
  have h :=
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
      p n F hFsymm hF c d).inv
  simpa only [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse,
    inv_inv] using h

/-- With the determinant orientation fixed, the differential densities obey
the source-form cocycle with the forward transition determinant. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal_cocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
        p n F hF c d X =
      skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
          p n F hF d c
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X) *
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
          p n F hF c d X := by
  let target :=
    skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal
      p n F hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X)
  have htarget0 : target ≠ 0 := by
    dsimp [
      target,
      skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal]
    exact ne_of_gt
      (Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal_pos
        p n F _
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1.2)
  have htargetTop : target ≠ ⊤ := by
    dsimp [
      target,
      skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal,
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal]
    exact ENNReal.coe_ne_top
  have h :=
    congrArg Inv.inv
      (skewAdjointPadicCayleyTranslatedSourceOverlapJacobianDensityENNReal_cocycle
        p n F hFsymm hF c d X)
  change _ = (target * _)⁻¹ at h
  rw [ENNReal.mul_inv (Or.inl htarget0) (Or.inl htargetTop)] at h
  simpa only [
    target,
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse,
    inv_inv] using h

/-- The correctly oriented conditional reduction: differential overlap
compatibility follows from the coordinate pushforward weighted by the
*forward* transition determinant. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_of_map_coordinate_withDensity_transitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (hcoordinate :
      Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d)
          ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
              p n F hF c d).withDensity
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
              p n F hF c d)) =
        skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
          p n F hF d c) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d)
        (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
          p n F hF c d) =
      skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
        p n F hF d c := by
  exact map_withDensity_of_ae_density_cocycle
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF d c)
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
      p n F hF d c)
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d).measurable
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
      p n F hFsymm hF c d).aemeasurable
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal
      p n F hF d c)
    hcoordinate
    (Filter.Eventually.of_forall fun Y =>
      skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialDensityENNReal_cocycle
        p n F hFsymm hF c d Y)

end PositiveDefiniteIntegralLattice
