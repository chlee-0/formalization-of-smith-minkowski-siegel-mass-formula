import SMSFormula.PadicCayleyTranslatedChartOverlapRawImage
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport

/-!
# Affine tangent Haar scaling on a p-adic overlap ball

The fixed transported skew-adjoint coordinate Haar measure scales under the
overlap tangent equivalence by the inverse determinant norm.  Additive
translation invariance turns this into the corresponding statement for the
centered affine tangent map.

Restricting to the exact source coordinate ball and its affine tangent target
coset gives the local affine pushforward needed before the nonlinear
transition is reintroduced.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance padicCayleyOverlapTangentHaarMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapTangentHaarBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The overlap tangent equivalence scales the fixed coordinate Haar
measure by its inverse determinant norm. -/
theorem
    map_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X)
        (Matrix.skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊⁻¹ •
        Matrix.skewAdjointPadicCoordinateMeasure F p :=
  Matrix.map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det
    F p
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X)

/-- The centered affine tangent map is continuous. -/
theorem
    continuous_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    Continuous
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
        F p hF c d X) := by
  exact continuous_const.add
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X).continuous.comp
        (continuous_id.sub continuous_const))

/-- The affine tangent map has the same determinant scaling as its linear
part on the full coordinate Haar measure. -/
theorem
    map_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentAffineMap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X)
        (Matrix.skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊⁻¹ •
        Matrix.skewAdjointPadicCoordinateMeasure F p := by
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let t :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d x
  let A :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X
  let sourceTranslation :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    fun y => -x + y
  let targetTranslation :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    fun y => t + y
  letI : Measure.IsAddHaarMeasure μ :=
    Matrix.skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  have hsourceMeasurable : Measurable sourceTranslation :=
    (continuous_const.add continuous_id).measurable
  have htargetMeasurable : Measurable targetTranslation :=
    (continuous_const.add continuous_id).measurable
  have hAMeasurable : Measurable A :=
    A.continuous.measurable
  have hsourceMap :
      Measure.map sourceTranslation μ = μ :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self (-x)
  have htargetMap :
      Measure.map targetTranslation μ = μ :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self t
  have hlinearMap :
      Measure.map A μ =
        ‖LinearMap.det A.toLinearMap‖₊⁻¹ • μ :=
    map_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentEquiv
      F p hF c d X
  have haffine :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X =
        targetTranslation ∘ A ∘ sourceTranslation := by
    funext y
    dsimp [
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap,
      sourceTranslation, targetTranslation, x, t, A]
    rw [sub_eq_add_neg, add_comm y]
  rw [haffine]
  calc
    Measure.map (targetTranslation ∘ A ∘ sourceTranslation) μ =
        Measure.map targetTranslation
          (Measure.map A (Measure.map sourceTranslation μ)) := by
      rw [
        Measure.map_map htargetMeasurable hAMeasurable,
        Measure.map_map (htargetMeasurable.comp hAMeasurable)
          hsourceMeasurable]
      rfl
    _ = Measure.map targetTranslation (Measure.map A μ) := by
      rw [hsourceMap]
    _ =
        Measure.map targetTranslation
          (‖LinearMap.det A.toLinearMap‖₊⁻¹ • μ) := by
      rw [hlinearMap]
    _ =
        ‖LinearMap.det A.toLinearMap‖₊⁻¹ •
          Measure.map targetTranslation μ := by
      rw [Measure.map_smul]
    _ = ‖LinearMap.det A.toLinearMap‖₊⁻¹ • μ := by
      rw [htargetMap]

/-- The exact target tangent coset has the selected coordinate ball as its
full preimage under the affine tangent equivalence. -/
theorem
    preimage_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X ⁻¹'
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k =
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) := by
  let f :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X
  let B :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X)
  have himage :
      f '' B =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k :=
    image_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap_coordinateBall
      F p hF c d X k
  have hinj : Function.Injective f :=
    injective_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X
  apply Set.Subset.antisymm
  · intro y hy
    have hy' :
        f y ∈
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
            F p hF c d X k := hy
    rw [← himage] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := hinj hzy
    rwa [← hzy']
  · intro y hy
    have hy' :
        f y ∈
          skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
            F p hF c d X k := by
      rw [← himage]
      exact ⟨y, hy, rfl⟩
    exact hy'

/-- Restricting the affine tangent Haar scaling to the selected coordinate
ball gives the exact restricted target-coset measure. -/
theorem
    map_restrict_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentAffineMap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X)
        ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X))) =
      ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊⁻¹ •
        (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
            F p hF c d X k) := by
  let f :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X
  let B :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X)
  let C :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
      F p hF c d X k
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  let s :=
    ‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊⁻¹
  have hf : Measurable f :=
    (continuous_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X).measurable
  have hC : MeasurableSet C :=
    (isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
      F p hF c d X k).2.measurableSet
  have hpre : f ⁻¹' C = B :=
    preimage_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
      F p hF c d X k
  have hmap : Measure.map f μ = s • μ :=
    map_skewAdjointPadicCoordinateMeasure_translatedSourceOverlapTransitionTangentAffineMap
      F p hF c d X
  change Measure.map f (μ.restrict B) = s • μ.restrict C
  rw [← hpre, ← Measure.restrict_map hf hC]
  rw [hmap, Measure.restrict_smul]

end PositiveDefiniteIntegralLattice
