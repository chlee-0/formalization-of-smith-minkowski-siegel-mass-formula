import SMSFormula.PadicCayleyTranslatedChartOverlapWeightedReduction

/-!
# Ambient form of the remaining p-adic Cayley overlap pushforward

This module embeds each exact translated Cayley source overlap into the
transported skew-adjoint `ℚ_[p]` carrier.  Its open range is the ambient
overlap set.  The relative transition and reciprocal tangent-determinant
density are extended measurably from that range.

The coordinate overlap measure, with or without the reciprocal density, is
identified with the corresponding restricted ambient additive Haar measure.
Consequently, the remaining bare nonlinear pushforward on overlap subtypes is
equivalent to its ambient restricted-Haar form.

No nonlinear change-of-variables theorem is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapAmbientMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapAmbientBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
  BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The exact translated overlap, included directly in its transported
skew-adjoint ambient carrier. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  X.1.1

/-- The exact overlap inclusion is an open topological embedding. -/
theorem isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Topology.IsOpenEmbedding
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d) := by
  exact
    (Matrix.isOpen_skewAdjointPadicCayleySource F p).isOpenEmbedding_subtypeVal.comp
      (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapSet
        F p hF c d).isOpenEmbedding_subtypeVal

/-- The open ambient image of an exact translated source overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Set.range
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d)

/-- The ambient overlap image is open. -/
theorem isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d) :=
  (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
    p n F hF c d).isOpen_range

/-- The ambient overlap image is measurable. -/
theorem measurableSet_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    MeasurableSet
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d) :=
  (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
    p n F hF c d).measurableSet

/-- A globally measurable extension of the relative translated-coordinate
transition from the exact ambient overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Function.extend
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d)
    (fun X =>
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X))
    (fun _ => 0) x

/-- The ambient relative transition extension is measurable. -/
theorem measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d) := by
  exact
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d).measurableEmbedding.measurable_extend
      ((isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c).continuous.comp
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d).continuous).measurable
      measurable_const

/-- On the exact overlap, the ambient extension is the overlap transition. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X) := by
  exact Function.Injective.extend_apply
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d).injective _ _ X

/-- The ambient extension sends the source ambient overlap into the target
ambient overlap. -/
theorem mapsTo_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set.MapsTo
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d)
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d)
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF d c) := by
  rintro x ⟨X, rfl⟩
  exact
    ⟨skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X,
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq
        p n F hF c d X |>.symm⟩

/-- The exact image of the source ambient overlap is the target ambient
overlap. -/
theorem image_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d ''
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF d c := by
  apply Set.Subset.antisymm
  · exact
      (mapsTo_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d).image_subset
  · rintro y ⟨Y, rfl⟩
    let T :=
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d
    refine
      ⟨skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d (T.symm Y),
        ⟨T.symm Y, rfl⟩, ?_⟩
    rw [
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq]
    exact congrArg
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF d c)
      (T.apply_symm_apply Y)

/-- The measurable ambient extension is injective on its exact source
overlap. -/
theorem injOn_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set.InjOn
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d)
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d) := by
  rintro x ⟨X, rfl⟩ y ⟨Y, rfl⟩ hxy
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq,
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq
  ] at hxy
  have hT :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d Y :=
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF d c).injective hxy
  have hXY : X = Y :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d).injective hT
  subst Y
  rfl

/-- On the exact overlap, the ambient extension is the explicit inverse-Cayley
relative transition for `d⁻¹c`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_relativeTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d X) :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      padicCayleyRelativeTransitionMatrix p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  rw [skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq p n F hF c d X]
  exact
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_relativeTransition
      F p hF c d X

/-- The reciprocal tangent-determinant modulus of the overlap transition, extended
measurably by zero from the exact ambient overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    ENNReal :=
  Function.extend
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
      p n F hF c d)
    (fun _ => 0) x

/-- The ambient reciprocal transition determinant is measurable. -/
theorem measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d) := by
  exact
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d).measurableEmbedding.measurable_extend
      (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hFsymm hF c d)
      measurable_const

/-- The ambient reciprocal density agrees with the subtype density on
the exact overlap. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hF c d X := by
  exact Function.Injective.extend_apply
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d).injective _ _ X

/-- On the exact overlap, the ambient reciprocal density is the reciprocal
determinant modulus of the restricted derivative. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq_endomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d X) =
      (‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
          F p hF c d X).toLinearMap‖₊ : ENNReal)⁻¹ := by
  rw [skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq p n F hF c d X,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq]
  rfl

/-- Pulling the ambient overlap image back to the common Cayley source gives
the original translated source-overlap set. -/
theorem preimage_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Subtype.val :
      Matrix.skewAdjointPadicCayleySource F p →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ⁻¹'
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d =
      skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d := by
  ext X
  constructor
  · rintro ⟨Y, hY⟩
    have hYX : Y.1 = X := Subtype.ext hY
    simpa [hYX] using Y.2
  · intro hX
    exact ⟨⟨X, hX⟩, rfl⟩

/-- The ambient overlap image lies in the common Cayley source. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet_subset_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d ⊆
      Matrix.skewAdjointPadicCayleySource F p := by
  rintro x ⟨X, rfl⟩
  exact X.1.2

/-- Including the coordinate overlap measure into the ambient tangent carrier
gives additive Haar restricted to the ambient overlap image. -/
theorem map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_ambientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d)
        (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
          p n F hF c d) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d) := by
  let i :
      skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d →
        Matrix.skewAdjointPadicCayleySource F p :=
    Subtype.val
  let j :
      Matrix.skewAdjointPadicCayleySource F p →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    Subtype.val
  let μ :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d
  let ν := Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  let m := Matrix.skewAdjointPadicCoordinateMeasure F p
  let A := skewAdjointPadicCayleyTranslatedSourceOverlapSet F p hF c d
  let U := skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d
  have hi : Measurable i := continuous_subtype_val.measurable
  have hj : Measurable j := continuous_subtype_val.measurable
  have hU : MeasurableSet U :=
    (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d).measurableSet
  have hpre : j ⁻¹' U = A :=
    preimage_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d
  change Measure.map (j ∘ i) μ = m.restrict U
  rw [← Measure.map_map hj hi]
  rw [show Measure.map i μ = ν.restrict A by
    exact
      map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_subtype
        p n F hF c d]
  rw [← hpre, ← Measure.restrict_map hj hU]
  rw [show Measure.map j ν =
      m.restrict (Matrix.skewAdjointPadicCayleySource F p) by
    exact Matrix.map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
      p n F]
  rw [Measure.restrict_restrict hU]
  rw [Set.inter_eq_left.mpr (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet_subset_source p n F hF c d)]

/-- The same ambient inclusion transports the reciprocal-Jacobian weighted
coordinate overlap measure to its ambient restricted-Haar form. -/
theorem map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_ambientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d)
        ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
            p n F hF c d).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
            p n F hF c d)) =
      ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d) := by
  have hfun :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
          p n F hF c d =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d ∘ skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d := by
    funext X
    exact (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq p n F hF c d X).symm
  rw [hfun]
  rw [map_withDensity_comp_of_measurable
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d)
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d)
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d).continuous.measurable
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hFsymm hF c d)]
  rw [map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_ambientInclusion p n F hF c d]

/-- Mapping after the ambient inclusion commutes with the overlap
transition. -/
theorem map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_map_ambientInclusion
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (μ : Measure
      (skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)) :
    Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition p n F hF c d)
        (Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d) μ) =
      Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c)
        (Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d) μ) := by
  rw [Measure.map_map
    (measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition p n F hF c d)
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d).continuous.measurable]
  rw [Measure.map_map
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c).continuous.measurable
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d).measurable]
  apply congrArg (fun f => Measure.map f μ)
  funext X
  exact skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq p n F hF c d X

/-- The remaining reciprocal-Jacobian pushforward on exact overlap subtypes is
equivalent to the corresponding pushforward between two open restrictions of
ambient additive Haar. -/
theorem map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_transitionJacobianInverse_iff_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d)
        ((skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
            p n F hF c d).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
            p n F hF c d)) =
      skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
        p n F hF d c) ↔
    (Measure.map (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d)).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF d c)) := by
  let i :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF c d
  let j :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d
  let Ψ :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition p n F hF c d
  let μ :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF c d).withDensity
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hF c d)
  let ν :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
      p n F hF d c
  let μa :=
    ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF c d)).withDensity
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse p n F hF c d)
  let νa :=
    (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet p n F hF d c)
  have hμ : Measure.map i μ = μa :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_withDensity_ambientInclusion p n F hFsymm hF c d
  have hν : Measure.map j ν = νa :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_ambientInclusion p n F hF d c
  have hcomm : Measure.map Ψ (Measure.map i μ) =
      Measure.map j (Measure.map T μ) :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_map_ambientInclusion p n F hF c d μ
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
    apply (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion p n F hF d c).measurableEmbedding.map_injective
    calc
      Measure.map j (Measure.map T μ) =
          Measure.map Ψ (Measure.map i μ) := hcomm.symm
      _ = Measure.map Ψ μa := by rw [hμ]
      _ = νa := h
      _ = Measure.map j ν := hν.symm

end PositiveDefiniteIntegralLattice
