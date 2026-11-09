import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedGluing

/-!
# Exact-overlap transport of the forward p-adic Jacobian theorem

The ambient forward-Jacobian change-of-variables theorem is transported back
through the exact open overlap embeddings.  The first two results are the
forward-density analogues of the inverse-density
interfaces in `PadicCayleyTranslatedChartOverlapAmbient`.

The final theorem feeds the resulting coordinate pushforward into the
correctly oriented differential-density cocycle.  No translated-chart gluing
or finite-place Haar construction occurs here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedSubtypeMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedSubtypeBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The exact overlap inclusion transports the coordinate measure weighted by
the forward transition determinant to ambient restricted coordinate Haar
weighted by the ambient forward determinant. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_forwardJacobian_ambientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d)
        ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
            p n F hF c d).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
            p n F hF c d)) =
      ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d)).withDensity
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
          p n F hF c d) := by
  have hfun :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
          p n F hF c d =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d ∘
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d := by
    funext X
    simpa only [
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian]
      using
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian_eq
          p n F hF c d X).symm
  rw [hfun]
  rw [map_withDensity_comp_of_measurable
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
      p n F hF c d)
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d).continuous.measurable
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
      p n F hFsymm hF c d)]
  rw [
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_ambientInclusion
      p n F hF c d]

/-- The exact-overlap forward-Jacobian coordinate pushforward is equivalent
to its ambient restricted-Haar form. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_transitionJacobian_iff_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d)
        ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
            p n F hF c d).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
            p n F hF c d)) =
      skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
        p n F hF d c) ↔
    (Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
              p n F hF c d)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF d c)) := by
  let i :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d
  let j :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF d c
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d
  let Ψ :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let μ :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d).withDensity
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
        p n F hF c d)
  let ν :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF d c
  let μa :=
    ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d)).withDensity
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
        p n F hF c d)
  let νa :=
    (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF d c)
  have hμ : Measure.map i μ = μa :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_forwardJacobian_ambientInclusion
      p n F hFsymm hF c d
  have hν : Measure.map j ν = νa :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_ambientInclusion
      p n F hF d c
  have hcomm : Measure.map Ψ (Measure.map i μ) =
      Measure.map j (Measure.map T μ) :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_map_ambientInclusion
      p n F hF c d μ
  constructor
  · intro h
    change Measure.map Ψ μa = νa
    calc
      Measure.map Ψ μa =
          Measure.map Ψ (Measure.map i μ) := by rw [hμ]
      _ = Measure.map j (Measure.map T μ) := hcomm
      _ = Measure.map j ν := by rw [h]
      _ = νa := hν
  · intro h
    change Measure.map T μ = ν
    apply
      (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF d c).measurableEmbedding.map_injective
    calc
      Measure.map j (Measure.map T μ) =
          Measure.map Ψ (Measure.map i μ) := hcomm.symm
      _ = Measure.map Ψ μa := by rw [hμ]
      _ = νa := h
      _ = Measure.map j ν := hν.symm

/-- The internally proved ambient nonlinear theorem gives the exact-overlap
coordinate pushforward with the correctly oriented forward determinant. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_transitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d)
        ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
            p n F hF c d).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobian
            p n F hF c d)) =
      skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
        p n F hF d c := by
  apply
    (map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_transitionJacobian_iff_ambient
      p n F hFsymm hF c d).2
  exact
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbient_withDensity_forwardJacobian
      p n F hF c d

/-- The correctly normalized exact-overlap differential measures are
invariant under center change. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d)
        (skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
          p n F hF c d) =
      skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
        p n F hF d c := by
  exact
    map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_of_map_coordinate_withDensity_transitionJacobian
      p n F hFsymm hF c d
      (map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_transitionJacobian
        p n F hFsymm hF c d)

end PositiveDefiniteIntegralLattice
