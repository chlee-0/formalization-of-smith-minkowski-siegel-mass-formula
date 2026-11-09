import SMSFormula.PadicCayleyTranslatedChartDifferentialMeasure

/-!
# Right-chart transport of corrected p-adic differentials

This small opaque layer transports the corrected source-overlap differential
measure through the reordered right translated Cayley chart.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedDifferentialRightSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTranslatedDifferentialRightSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTranslatedDifferentialRightSubgroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedDifferentialRightSubgroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

private theorem map_comap_comap_measurableEquiv
    {A A' B X : Type*}
    [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace B]
    [MeasurableSpace X]
    (e : A ≃ᵐ B)
    (i : A → A') (j : A' → X) (k : B → X)
    (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (hk : MeasurableEmbedding k)
    (hcomm : ∀ a, k (e a) = j (i a))
    (μ : Measure X) :
    Measure.map e (Measure.comap i (Measure.comap j μ)) =
      Measure.comap k μ := by
  ext s hs
  rw [e.map_apply, hi.comap_apply, hj.comap_apply, hk.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨e a, ha, hcomm a⟩
  · rintro ⟨b, hb, rfl⟩
    let a := e.symm b
    refine ⟨i a, ⟨a, ?_, rfl⟩, ?_⟩
    · simpa [a] using hb
    · rw [← hcomm a]
      simp [a]

/-- The corrected source-overlap differential measure transports through the
`d` chart to its reordered common-target restriction. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
          p n F hF c d)
        (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
          p n F hF d c) =
      padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
        p n F hF c d := by
  let e := skewAdjointPadicCayleyTranslatedHomeomorph F p hF d
  let μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F
  let ν :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF d
  have hmap : Measure.map e μ = ν := by
    rfl
  have hμ : μ = Measure.comap e ν := by
    rw [← hmap]
    exact (e.toMeasurableEquiv.measurableEmbedding.comap_map μ).symm
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_eq_comap,
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight]
  change Measure.map
      (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
        p n F hF c d)
      (Measure.comap Subtype.val μ) =
    Measure.comap
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
        p n F c d) ν
  rw [hμ]
  apply map_comap_comap_measurableEquiv
    (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
      p n F hF c d).toMeasurableEquiv
    Subtype.val e
    (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
      p n F c d)
  · exact MeasurableEmbedding.subtype_coe
      (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapSet
        F p hF d c).measurableSet
  · exact e.toMeasurableEquiv.measurableEmbedding
  · exact
      measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
        p n F c d
  · intro X
    rfl

end PositiveDefiniteIntegralLattice
