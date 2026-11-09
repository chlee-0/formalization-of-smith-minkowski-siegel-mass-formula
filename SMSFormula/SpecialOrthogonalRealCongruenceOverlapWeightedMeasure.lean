import SMSFormula.SpecialOrthogonalRealCongruenceOverlapAmbientCocycle

/-!
# Weighted ambient measure comparison for real congruence overlaps

This module combines the fixed-carrier nonlinear Jacobian theorem with the
ambient density cocycle.  A measurable extension of the transition is used
only for generic `Measure.map` algebra; it agrees with the transition on the
restricted source.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapWeightedMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapWeightedBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Mapping a measure with a pulled-back measurable density commutes with
adding that density after the map. -/
theorem map_withDensity_comp_of_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) (g : β → ENNReal)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs,
    setLIntegral_map hs hg hf]
  rfl

/-- A baseline Jacobian pushforward and an almost-everywhere density cocycle
give the corresponding weighted pushforward. -/
theorem map_withDensity_of_ae_density_cocycle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) (ν : Measure β)
    (J source : α → ENNReal) (target : β → ENNReal)
    (hf : Measurable f) (hJ : AEMeasurable J μ)
    (htarget : Measurable target)
    (hmap : Measure.map f (μ.withDensity J) = ν)
    (hcocycle : source =ᵐ[μ] (target ∘ f) * J) :
    Measure.map f (μ.withDensity source) =
      ν.withDensity target := by
  have htargetf : AEMeasurable (target ∘ f) μ :=
    (htarget.comp hf).aemeasurable
  calc
    Measure.map f (μ.withDensity source) =
        Measure.map f (μ.withDensity ((target ∘ f) * J)) := by
      exact congrArg (Measure.map f) (withDensity_congr_ae hcocycle)
    _ = Measure.map f (μ.withDensity (J * (target ∘ f))) := by
      apply congrArg (Measure.map f)
      apply withDensity_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _
    _ = Measure.map f ((μ.withDensity J).withDensity (target ∘ f)) := by
      rw [withDensity_mul₀ hJ htargetf]
    _ = (Measure.map f (μ.withDensity J)).withDensity target :=
      map_withDensity_comp_of_measurable
        f (μ.withDensity J) target hf htarget
    _ = ν.withDensity target := by rw [hmap]

/-- A globally measurable extension of `Psi_W` from the exact open ambient
source. -/
def specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  Function.extend
    (Subtype.val :
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (fun z =>
      specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W z.1)
    (fun _ => 0) x

/-- The measurable extension agrees with `Psi_W` on the exact source. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
        F hF hdet W x =
      specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- The global extension of `Psi_W` is measurable. -/
theorem measurable_specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measurable
      (specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
        F hF hdet W) := by
  letI : OpensMeasurableSpace
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet F hF hdet W) :=
    @Subtype.opensMeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule
      _ (realCongruenceOverlapWeightedMeasurableSpace F)
      (@BorelSpace.opensMeasurable _ _
        (realCongruenceOverlapWeightedMeasurableSpace F)
        (realCongruenceOverlapWeightedBorelSpace F))
      (fun x => x ∈
        specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet F hF hdet W)
  apply
    (MeasurableEmbedding.subtype_coe
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)).measurable_extend
      _ measurable_const
  have hcontinuous : Continuous
      (fun x : specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W =>
        specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x.1) :=
    ((contDiffOn_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W).continuousOn.mono fun _ hx => hx.1).restrict
  exact hcontinuous.measurable

/-- The absolute Frechet Jacobian is continuous on the exact ambient source. -/
theorem continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    ContinuousOn
      (fun x => ENNReal.ofReal
        |(fderiv ℝ
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W) x).det|)
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) := by
  have hdiff :
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W) :=
    (contDiffOn_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W).mono fun _
        (hx : _ ∈
          specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
            F hF hdet W) => hx.1
  have hfderiv :=
    hdiff.continuousOn_fderiv_of_isOpen
      (isOpen_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by simp)
  exact
    (ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ContinuousLinearMap.continuous_det)).comp_continuousOn
        hfderiv

/-- The density-weighted fixed-carrier transition sends the source
identity-chart coordinate measure on the exact overlap to the independently
defined target density measure on its exact image. -/
theorem map_withDensity_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
            F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
            F hF hdet)) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
          F hF hdet W)).withDensity
        (specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
          F hF hdet W) := by
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)
  let ν :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W)
  let Ψ :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W
  let Ψm :=
    specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
      F hF hdet W
  let J := fun x => ENNReal.ofReal |(fderiv ℝ Ψ x).det|
  let source :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity F hF hdet
  let target :=
    specialFormPreservingSmoothRealCongruenceAmbientTargetDensity F hF hdet W
  have hU :
      MeasurableSet
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W) :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  have hΨm : Measurable Ψm :=
    measurable_specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
      F hF hdet W
  have htarget : Measurable target :=
    measurable_specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
      F hF hdet W
  have hJ : AEMeasurable J μ := by
    exact
      (continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
        F hF hdet W).aemeasurable hU
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact
      specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
        F hF hdet W x hx
  have hmap : Measure.map Ψm (μ.withDensity J) = ν := by
    calc
      Measure.map Ψm (μ.withDensity J) =
          Measure.map Ψ (μ.withDensity J) :=
        Measure.map_congr
          ((withDensity_absolutelyContinuous μ J).ae_eq hΨeq)
      _ = ν := by
        simpa [μ, ν, Ψ, J] using
          map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition
            F hF hdet W
  have hcocycle : source =ᵐ[μ] (target ∘ Ψm) * J := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hΨmx : Ψm x = Ψ x := by
      simpa [Ψm, Ψ] using
        specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
          F hF hdet W x hx
    change source x = target (Ψm x) * J x
    rw [hΨmx]
    simpa [source, target, J, Ψ] using
      specialFormPreservingSmoothRealCongruenceAmbientDensityCocycle
        F hF hdet W x hx
  have hweighted :
      Measure.map Ψm (μ.withDensity source) =
        ν.withDensity target :=
    map_withDensity_of_ae_density_cocycle
      Ψm μ ν J source target hΨm hJ htarget hmap hcocycle
  calc
    Measure.map Ψ (μ.withDensity source) =
        Measure.map Ψm (μ.withDensity source) :=
      Measure.map_congr
        ((withDensity_absolutelyContinuous μ source).ae_eq hΨeq.symm)
    _ = ν.withDensity target := hweighted

end PositiveDefiniteIntegralLattice
