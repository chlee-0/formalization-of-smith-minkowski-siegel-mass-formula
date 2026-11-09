import SMSFormula.RationalSpecialOrthogonalDifferentialNormalization
import SMSFormula.SpecialOrthogonalRealChartMeasure
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter
import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus
import SMSFormula.PadicCayleyTangentModulus

/-!
# Compatibility of differential measures on real chart overlaps

This module proves the real nonlinear change-of-variables compatibility for the
chart measures of `SpecialOrthogonalRealChartMeasure`. It keeps every
comparison on the exact overlap subtypes and uses the ambient transition
`MeasurePreserving` theorem.

The result is local. This file does not construct a measure on the full
real special orthogonal group or compare it with a reference Haar measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator ContDiff ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realOverlapGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realOverlapGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realOverlapModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realOverlapModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

private theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : α → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

private theorem map_withDensity_of_density_cocycle
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [MeasurableSpace β]
    [BorelSpace α] [BorelSpace β]
    (e : α ≃ₜ β) (μ : Measure α) (ν : Measure β)
    {J f : α → ENNReal} {g : β → ENNReal}
    (hJ : Measurable J) (hg : Measurable g)
    (hmap : Measure.map e (μ.withDensity J) = ν)
    (hcocycle : ∀ x, f x = g (e x) * J x) :
    Measure.map e (μ.withDensity f) = ν.withDensity g := by
  have hge : Measurable (g ∘ e) := hg.comp e.continuous.measurable
  calc
    Measure.map e (μ.withDensity f) =
        Measure.map e (μ.withDensity ((g ∘ e) * J)) := by
      apply congrArg (Measure.map e)
      apply withDensity_congr_ae
      filter_upwards [] with x
      exact hcocycle x
    _ = Measure.map e (μ.withDensity (J * (g ∘ e))) := by
      apply congrArg (Measure.map e)
      apply withDensity_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _
    _ = Measure.map e ((μ.withDensity J).withDensity (g ∘ e)) := by
      rw [withDensity_mul μ hJ hge]
    _ = (Measure.map e (μ.withDensity J)).withDensity
          ((g ∘ e) ∘ e.symm) :=
      map_withDensity_measurableEquiv e.toMeasurableEquiv (μ.withDensity J) hge
    _ = ν.withDensity g := by
      rw [hmap]
      apply withDensity_congr_ae
      filter_upwards [] with y
      simp [Function.comp_def]

private theorem map_conjugate_homeomorph
    {α β γ δ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    [TopologicalSpace δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ]
    [BorelSpace α] [BorelSpace β] [BorelSpace γ] [BorelSpace δ]
    (E : α ≃ₜ δ) (eL : α ≃ₜ β) (T : β ≃ₜ γ) (eR : δ ≃ₜ γ)
    (νL : Measure α) (μL : Measure β) (μR : Measure γ) (νR : Measure δ)
    (hcomm : ∀ x, eR (E x) = T (eL x))
    (hL : Measure.map eL νL = μL)
    (hT : Measure.map T μL = μR)
    (hR : Measure.map eR νR = μR) :
    Measure.map E νL = νR := by
  calc
    Measure.map E νL = Measure.map (eR.symm ∘ T ∘ eL) νL := by
      apply Measure.map_congr
      filter_upwards [] with x
      apply eR.injective
      change eR (E x) = eR (eR.symm (T (eL x)))
      rw [eR.apply_symm_apply]
      exact hcomm x
    _ = Measure.map eR.symm (Measure.map T (Measure.map eL νL)) := by
      symm
      rw [Measure.map_map T.continuous.measurable eL.continuous.measurable,
        Measure.map_map eR.symm.continuous.measurable
          (T.continuous.measurable.comp eL.continuous.measurable)]
    _ = Measure.map eR.symm (Measure.map T μL) := by rw [hL]
    _ = Measure.map eR.symm μR := by rw [hT]
    _ = Measure.map eR.symm (Measure.map eR νR) := by rw [hR]
    _ = νR := by
      rw [Measure.map_map eR.symm.continuous.measurable eR.continuous.measurable]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- The exact real overlap transition pushes the left coordinate measure
weighted by its absolute Jacobian to the right coordinate measure. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_withJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
          F hF hdet g h)
        ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
          F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
            F hF hdet g h)) =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h := by
  let T :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
      F hF hdet g h
  let eL :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeftHomeomorphSource
      F hF hdet g h
  let eR :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromRightHomeomorphTarget
      F hF hdet g h
  let t :=
    (specialFormPreservingSmoothRealChart F hF hdet g).symm.trans
      (specialFormPreservingSmoothRealChart F hF hdet h)
  let μL :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
      F hF hdet g h
  let μR :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
      F hF hdet g h
  let J :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
      F hF hdet g h
  calc
    Measure.map T (μL.withDensity J) =
        Measure.map
          (eR.symm ∘ t.toHomeomorphSourceTarget ∘ eL)
          (μL.withDensity J) := by
      apply Measure.map_congr
      filter_upwards [] with y
      apply eR.injective
      change eR (T y) =
        eR (eR.symm (t.toHomeomorphSourceTarget (eL y)))
      rw [eR.apply_symm_apply]
      exact
        specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageHomeomorph_commute
          F hF hdet g h y
    _ = Measure.map eR.symm
          (Measure.map t.toHomeomorphSourceTarget
            (Measure.map eL (μL.withDensity J))) := by
      symm
      rw [Measure.map_map
        t.toHomeomorphSourceTarget.continuous.measurable
        eL.continuous.measurable,
        Measure.map_map
          eR.symm.continuous.measurable
          (t.toHomeomorphSourceTarget.continuous.measurable.comp
            eL.continuous.measurable)]
    _ = Measure.map eR.symm
          (Measure.map t.toHomeomorphSourceTarget
            ((Measure.comap Subtype.val
              (Matrix.skewAdjointRealCoordinateDetMeasure F 0)).withDensity
              (specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionSourceJacobian
                F hF hdet g h))) := by
      exact congrArg (Measure.map eR.symm)
        (congrArg (Measure.map t.toHomeomorphSourceTarget)
          (map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_withDensity_source
            F hF hdet g h))
    _ = Measure.map eR.symm
          (Measure.comap Subtype.val
            (Matrix.skewAdjointRealCoordinateDetMeasure F 0)) := by
      exact congrArg (Measure.map eR.symm) (by
        simpa [t] using
          map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealSkewAdjointTransition_sourceTarget
            F hF hdet g h)
    _ = Measure.map eR.symm (Measure.map eR μR) := by
      rw [
        map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight_target]
    _ = μR := by
      rw [Measure.map_map eR.symm.continuous.measurable
        eR.continuous.measurable]
      simp

theorem specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensity_cocycle
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (y : specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageFromLeft
      F hF hdet g h) :
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
        F hF hdet g h y =
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
          F hF hdet g h y *
        specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
            F hF hdet g h y) := by
  rw [
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensity_center_change]
  exact mul_comm _ _

/-- The invariant differential density makes the exact real coordinate
transition measure preserving. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
          F hF hdet g h)
        ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
          F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
            F hF hdet g h)) =
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h) := by
  refine map_withDensity_of_density_cocycle
    (e :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h)
    (μ :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h)
    (ν :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h)
    (J :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
        F hF hdet g h)
    (f :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
        F hF hdet g h)
    (g :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
        F hF hdet g h) ?_ ?_ ?_ ?_
  · exact
      measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateTransitionJacobian
        F hF hdet g h
  · exact
      measurable_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
        F hF hdet g h
  · exact
      map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft_withJacobian
        F hF hdet g h
  · intro y
    exact
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensity_center_change
        F hF hdet g h y

/-- The invariant differential measures induced by two centered real charts
agree after transport across their exact native overlap transition. -/
theorem map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
          F hF hdet g h) =
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
        F hF hdet g h := by
  refine map_conjugate_homeomorph
    (E :=
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph
        F hF hdet g h)
    (eL :=
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
        F hF hdet g h)
    (T :=
      specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
        F hF hdet g h)
    (eR :=
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
        F hF hdet g h)
    (νL :=
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
        F hF hdet g h)
    (μL :=
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
        F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
            F hF hdet g h))
    (μR :=
      (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
        F hF hdet g h).withDensity
          (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
            F hF hdet g h))
    (νR :=
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
        F hF hdet g h) ?_ ?_ ?_ ?_
  · intro y
    exact
        specialFormPreservingSmoothRealChartTargetOverlapCoordinateHomeomorph_apply
          F hF hdet g h y
  · exact
      map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_eq_coordinateImageMeasure_withDensity
        F hF hdet g h
  · exact
      map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityMeasure
        F hF hdet g h
  · exact
      map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight_eq_coordinateImageMeasure_withDensity
        F hF hdet g h

/-- The invariant density measure induced on a common group overlap by the
chart centered at `g`. -/
def specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :=
  Measure.map
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph.symm
    ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
          F hF hdet g h))

/-- The invariant density measure induced on a common group overlap by the
chart centered at `h`. -/
def specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :=
  Measure.map
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).toHomeomorph.symm
    ((specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h))

/-- The two centered real charts induce the same invariant differential
measure on their exact same-point group overlap. -/
theorem specialFormPreservingSmoothRealChartSourceOverlapDensityMeasure_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
        F hF hdet g h =
      specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
        F hF hdet g h := by
  let eL :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph
  let eR :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).toHomeomorph
  let T :=
    specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph
      F hF hdet g h
  let μL :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
          F hF hdet g h)
  let μR :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h)
  change Measure.map eL.symm μL = Measure.map eR.symm μR
  calc
    Measure.map eL.symm μL =
        Measure.map (eR.symm ∘ T) μL := by
      apply Measure.map_congr
      filter_upwards [] with y
      change eL.symm y = eR.symm (T y)
      apply eR.injective
      rw [eR.apply_symm_apply]
      have ht :=
        specialFormPreservingSmoothRealChartSourceOverlapCoordinateHomeomorph_apply
          F hF hdet g h (eL.symm y)
      change T (eL (eL.symm y)) = eR (eL.symm y) at ht
      rw [eL.apply_symm_apply] at ht
      exact ht.symm
    _ = Measure.map eR.symm (Measure.map T μL) := by
      rw [Measure.map_map eR.symm.continuous.measurable T.continuous.measurable]
    _ = Measure.map eR.symm μR := by
      exact congrArg (Measure.map eR.symm)
        (map_specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityMeasure
          F hF hdet g h)

end PositiveDefiniteIntegralLattice
