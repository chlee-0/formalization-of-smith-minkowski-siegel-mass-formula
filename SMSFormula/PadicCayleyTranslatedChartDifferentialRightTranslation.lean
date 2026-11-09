import SMSFormula.PadicCayleySpecialOrthogonalAdjointMeasure
import SMSFormula.PadicCayleyTranslatedChartDifferentialTranslation

/-!
# Right translation of corrected p-adic Cayley chart measures

Right multiplication by `g` identifies the translated Cayley target centered
at `c` with the target centered at `c * g`.  In source coordinates it acts by
the special-orthogonal adjoint homeomorphism `X ↦ g⁻¹ X g`.  The source
differential measure is invariant under that homeomorphism, so both target and
ambient translated-chart measures are carried exactly to their right
translates.

No global chart gluing or inversion-invariance theorem is used here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialRightTranslationSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialRightTranslationSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyDifferentialRightTranslationGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialRightTranslationGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The translated Cayley chart intertwines source adjoint action with literal
right multiplication on the target group. -/
theorem coe_skewAdjointPadicCayleyTranslatedHomeomorph_adjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyTranslatedHomeomorph F p hF (c * g)
        (Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hFsymm hF g X)).1 =
      (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X).1 * g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change
    ((c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
      Matrix.padicCayleyForwardMatrix p
        ((Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hFsymm hF g X).1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
    ((c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
      Matrix.padicCayleyForwardMatrix p
        (X.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
  rw [Matrix.coe_skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph_apply]
  rw [Matrix.padicCayleyForwardMatrix_specialOrthogonalAdjoint
    p n F hFsymm hF g X]
  have hGunit :
      IsUnit (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) :=
    Units.isUnit g.1.1
  have hGdet :
      IsUnit (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hGunit
  have hGmul :
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hGdet
  calc
    ((c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        ((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹ *
          Matrix.padicCayleyForwardMatrix p
            (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) =
      (c.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        ((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹) *
        Matrix.padicCayleyForwardMatrix p
          (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
          noncomm_ring
    _ = _ := by rw [hGmul]; noncomm_ring

/-- Right multiplication identifies the exact translated target at `c` with
the target at `c * g`. -/
def padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTarget F p c ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTarget F p (c * g) where
  toFun y :=
    ⟨y.1 * g, by
      let e := skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
      let X := e.symm y
      have hy : e X = y := e.apply_symm_apply y
      have hchart :=
        coe_skewAdjointPadicCayleyTranslatedHomeomorph_adjoint
          p n F hFsymm hF c g X
      rw [hy] at hchart
      rw [← hchart]
      exact
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF (c * g)
          (Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
            p n F hFsymm hF g X)).2⟩
  invFun y :=
    ⟨y.1 * g⁻¹, by
      let e := skewAdjointPadicCayleyTranslatedHomeomorph F p hF (c * g)
      let X := e.symm y
      have hy : e X = y := e.apply_symm_apply y
      have hchart :=
        coe_skewAdjointPadicCayleyTranslatedHomeomorph_adjoint
          p n F hFsymm hF (c * g) g⁻¹ X
      rw [hy] at hchart
      rw [← hchart]
      simpa using
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF ((c * g) * g⁻¹)
          (Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
            p n F hFsymm hF g⁻¹ X)).2⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul continuous_const

@[simp]
theorem
    coe_padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (y : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    (padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
      p n F hFsymm hF c g y).1 = y.1 * g :=
  rfl

/-- The target right-translation homeomorphism commutes with the translated
Cayley charts and the source adjoint homeomorphism. -/
@[simp]
theorem
    padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_chart
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
        p n F hFsymm hF c g
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X) =
      skewAdjointPadicCayleyTranslatedHomeomorph F p hF (c * g)
        (Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hFsymm hF g X) := by
  apply Subtype.ext
  rw [
    coe_padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_apply]
  exact
    (coe_skewAdjointPadicCayleyTranslatedHomeomorph_adjoint
      p n F hFsymm hF c g X).symm

/-- Right translation transports the corrected differential measure from the
target chart at `c` to the target chart at `c * g`. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
          p n F hFsymm hF c g)
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF c) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF (c * g) := by
  let eC := skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
  let eCG := skewAdjointPadicCayleyTranslatedHomeomorph F p hF (c * g)
  let A :=
    Matrix.skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
      p n F hFsymm hF g
  let R :=
    padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
      p n F hFsymm hF c g
  let μ := Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
    p n F
  change Measure.map R (Measure.map eC μ) = Measure.map eCG μ
  calc
    Measure.map R (Measure.map eC μ) = Measure.map (R ∘ eC) μ := by
      rw [Measure.map_map R.continuous.measurable eC.continuous.measurable]
    _ = Measure.map (eCG ∘ A) μ := by
      apply Measure.map_congr
      filter_upwards [] with X
      exact
        padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_chart
          p n F hFsymm hF c g X
    _ = Measure.map eCG (Measure.map A μ) := by
      rw [Measure.map_map eCG.continuous.measurable A.continuous.measurable]
    _ = Measure.map eCG μ := by
      rw [
        Matrix.map_skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_specialOrthogonalAdjoint
          p n F hFsymm hF g]

/-- Literal right multiplication transports the ambient corrected chart
measure at `c` to the ambient corrected chart measure at `c * g`. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (Homeomorph.mulRight g)
        (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (c * g) := by
  let R :=
    padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph
      p n F hFsymm hF c g
  let μ :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF c
  calc
    Measure.map (Homeomorph.mulRight g)
        (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF c) =
        Measure.map ((Homeomorph.mulRight g) ∘ Subtype.val) μ := by
      rw [padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure,
        Measure.map_map
          (Homeomorph.mulRight g).continuous.measurable
          continuous_subtype_val.measurable]
    _ = Measure.map (Subtype.val ∘ R) μ := by
      apply Measure.map_congr
      filter_upwards [] with y
      exact
        (coe_padicCayleySpecialOrthogonalTranslatedTargetRightTranslationHomeomorph_apply
          p n F hFsymm hF c g y).symm
    _ = Measure.map Subtype.val (Measure.map R μ) := by
      symm
      rw [Measure.map_map continuous_subtype_val.measurable
        R.continuous.measurable]
    _ = Measure.map Subtype.val
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF (c * g)) := by
      rw [
        map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_right
          p n F hFsymm hF c g]
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (c * g) :=
      rfl

end PositiveDefiniteIntegralLattice
