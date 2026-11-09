import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedSubtype

/-!
# Corrected differential measures on translated p-adic Cayley charts

The Cayley Jacobian density is the inverse determinant modulus of the forward
Cayley differential.  This module therefore defines the source differential
measure using its reciprocal, transports that measure through each exact
translated Cayley chart, and identifies its exact overlap restrictions.

The nonlinear overlap theorem then shows that the left and right
translated-chart differential restrictions agree on every common target.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleySourceDifferentialMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleySourceDifferentialBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The reciprocal of the Cayley Jacobian scalar on the full exact source
subtype.  This is the correctly oriented differential-form density. -/
def skewAdjointPadicCayleySourceDifferentialDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    ENNReal :=
  (skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    p n F X.1)⁻¹

/-- The full-source differential density is measurable. -/
theorem measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measurable
      (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F) :=
  ((measurable_skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
    p n F).comp continuous_subtype_val.measurable).inv

/-- The correctly oriented differential measure on the full exact Cayley
source subtype. -/
def skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure (skewAdjointPadicCayleySource F p) :=
  (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F).withDensity
    (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F)

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedDifferentialSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTranslatedDifferentialSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTranslatedDifferentialSubgroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedDifferentialSubgroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

private theorem comap_subtype_withDensity
    {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (f : α → ENNReal) :
    Measure.comap Subtype.val (μ.withDensity f) =
      (Measure.comap Subtype.val μ).withDensity
        (f ∘ Subtype.val : s → ENNReal) := by
  ext t ht
  rw [comap_subtype_coe_apply hs, withDensity_apply _
      ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 ht),
    withDensity_apply _ ht]
  change (∫⁻ a in Subtype.val '' t, f a ∂μ) =
    ∫⁻ x : s in t, f x ∂Measure.comap Subtype.val μ
  rw [setLIntegral_subtype hs t f]

/-- The corrected differential measure on the translated target chart
centered at `c`. -/
def padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (padicCayleySpecialOrthogonalTranslatedTarget F p c) :=
  Measure.map
    (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c)
    (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
      p n F)

/-- Inverse chart transport recovers the corrected full-source differential
measure. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_chart_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).symm
        (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p n F hF c) =
      Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n F := by
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure]
  exact MeasurableEquiv.map_map_symm
    (skewAdjointPadicCayleyTranslatedHomeomorph
      F p hF c).symm.toMeasurableEquiv

/-- Restricting the corrected full-source measure to an exact translated
source overlap gives the already constructed overlap differential measure. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_eq_comap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
        p n F hF c d =
      Measure.comap Subtype.val
        (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n F) := by
  rw [
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure,
    comap_subtype_withDensity
      (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapSet
        F p hF c d).measurableSet]
  rfl

/-- The restriction of the corrected `c`-chart differential measure to the
common target overlap. -/
def
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d) :=
  Measure.comap
    (padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
      p n F c d)
    (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF c)

/-- The restriction of the corrected `d`-chart differential measure to the
common target overlap. -/
def
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d) :=
  Measure.comap
    (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
      p n F c d)
    (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF d)

/-- Including the common target overlap into the `c` chart identifies its
corrected differential restriction setwise. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
          p n F c d)
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
          p n F hF c d) =
      (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF c).restrict
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
          p n F c d) := by
  rw [
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft,
    (measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
      p n F c d).map_comap,
    range_padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft]

/-- Including the common target overlap into the `d` chart identifies its
corrected differential restriction setwise. -/
theorem
    map_padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
          p n F c d)
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
          p n F hF c d) =
      (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF d).restrict
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
          p n F c d) := by
  rw [
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight,
    (measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
      p n F c d).map_comap,
    range_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight]

end PositiveDefiniteIntegralLattice
