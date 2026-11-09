import SMSFormula.PadicCayleyTranslatedChartDifferentialSigmaFinite

/-!
# Chartwise left translation of the corrected p-adic differential

Left multiplication by `a` identifies the exact translated Cayley target
centered at `g` with the one centered at `a * g`.  This identification
commutes with the two translated Cayley charts.  Since every corrected target
differential is the direct image of the same corrected source differential,
the target identification transports the corrected measure exactly.

The final theorem includes this equality into the full group and obtains the
corresponding ambient-chart transport.  No restriction of the glued global
measure, global invariance, Haar uniqueness, or stabilizer volume is used.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialTranslationSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialTranslationSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyDifferentialTranslationGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialTranslationGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Left multiplication identifies the exact translated target at `g` with
the exact translated target at `a * g`. -/
def padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ)
    (a g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTarget F p g ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTarget F p (a * g) where
  toFun y :=
    ⟨a * y.1, by
      apply
        (mem_padicCayleySpecialOrthogonalTranslatedTarget_iff
          F p (a * g) (a * y.1)).2
      have hy :=
        (mem_padicCayleySpecialOrthogonalTranslatedTarget_iff
          F p g y.1).1 y.2
      simpa [mul_assoc] using hy⟩
  invFun y :=
    ⟨a⁻¹ * y.1, by
      apply
        (mem_padicCayleySpecialOrthogonalTranslatedTarget_iff
          F p g (a⁻¹ * y.1)).2
      have hy :=
        (mem_padicCayleySpecialOrthogonalTranslatedTarget_iff
          F p (a * g) y.1).1 y.2
      simpa [mul_assoc] using hy⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

@[simp]
theorem
    coe_padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ)
    (a g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (y : padicCayleySpecialOrthogonalTranslatedTarget F p g) :
    (padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
      p n F a g y).1 =
      a * y.1 :=
  rfl

/-- Exact target left translation commutes with the translated Cayley charts
at `g` and `a * g`. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph_chart
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
        p n F a g
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF g X) =
      skewAdjointPadicCayleyTranslatedHomeomorph F p hF (a * g) X := by
  apply Subtype.ext
  simp only [
    coe_padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph_apply]
  change a * (g * _) = (a * g) * _
  rw [mul_assoc]

/-- Exact left translation transports the corrected target differential from
the chart at `g` to the chart at `a * g`. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
          p n F a g)
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF g) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF (a * g) := by
  let eG :=
    skewAdjointPadicCayleyTranslatedHomeomorph F p hF g
  let eAG :=
    skewAdjointPadicCayleyTranslatedHomeomorph F p hF (a * g)
  let L :=
    padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
      p n F a g
  let μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F
  change Measure.map L (Measure.map eG μ) = Measure.map eAG μ
  calc
    Measure.map L (Measure.map eG μ) =
        Measure.map (L ∘ eG) μ := by
      rw [Measure.map_map L.continuous.measurable eG.continuous.measurable]
    _ = Measure.map eAG μ := by
      apply Measure.map_congr
      filter_upwards [] with X
      exact
        padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph_chart
          p n F hF a g X

/-- Left multiplication transports the ambient corrected chart measure at
`g` to the ambient corrected chart measure at `a * g`. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (a g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (Homeomorph.mulLeft a)
        (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF g) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (a * g) := by
  let L :=
    padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph
      p n F a g
  let μ :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF g
  calc
    Measure.map (Homeomorph.mulLeft a)
        (padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
          p n F hF g) =
        Measure.map ((Homeomorph.mulLeft a) ∘ Subtype.val) μ := by
      rw [
        padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure,
        Measure.map_map
          (Homeomorph.mulLeft a).continuous.measurable
          continuous_subtype_val.measurable]
    _ = Measure.map (Subtype.val ∘ L) μ := by
      apply Measure.map_congr
      filter_upwards [] with y
      exact
        coe_padicCayleySpecialOrthogonalTranslatedTargetLeftHomeomorph_apply
          p n F a g y
    _ = Measure.map Subtype.val (Measure.map L μ) := by
      symm
      rw [Measure.map_map continuous_subtype_val.measurable
        L.continuous.measurable]
    _ = Measure.map Subtype.val
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF (a * g)) := by
      rw [
        map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_left
          p n F hF a g]
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF (a * g) :=
      rfl

end PositiveDefiniteIntegralLattice
