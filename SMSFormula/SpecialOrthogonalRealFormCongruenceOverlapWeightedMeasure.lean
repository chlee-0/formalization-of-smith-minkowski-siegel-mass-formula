import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapAmbientMeasure
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure

/-!
# Weighted ambient measures for explicit real-congruence overlaps

This module combines the explicit-real density cocycle with the nonlinear
Jacobian pushforward.  The tangent basis comparison scalar does not enter this
fixed-carrier change-of-variables step.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceOverlapWeightedMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapWeightedBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- A globally measurable extension of the explicit-real transition from its
exact open source. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  Function.extend
    (Subtype.val :
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (fun z =>
      specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c z.1)
    (fun _ => 0) x

/-- The measurable extension agrees with the transition on its exact
source. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
        F F' hF hdet hF' hdet' c x =
      specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- The global extension of the explicit-real transition is measurable. -/
theorem measurable_specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measurable
      (specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
        F F' hF hdet hF' hdet' c) := by
  letI : OpensMeasurableSpace
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
    @Subtype.opensMeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule
      _ (realFormCongruenceOverlapWeightedMeasurableSpace F)
      (@BorelSpace.opensMeasurable _ _
        (realFormCongruenceOverlapWeightedMeasurableSpace F)
        (realFormCongruenceOverlapWeightedBorelSpace F))
      (fun x => x ∈ specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
  apply
    (MeasurableEmbedding.subtype_coe
      (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet).measurable_extend
      _ measurable_const
  have hcontinuous : Continuous
      (fun x : specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c =>
        specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c x.1) :=
    (contDiffOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c).continuousOn.restrict
  exact hcontinuous.measurable

/-- The absolute Frechet Jacobian is continuous on the exact ambient source. -/
theorem continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    ContinuousOn
      (fun x => ENNReal.ofReal
        |(fderiv ℝ
          (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c) x).det|)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) := by
  have hfderiv :=
    (contDiffOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c).continuousOn_fderiv_of_isOpen
      (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by simp)
  exact
    (ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ContinuousLinearMap.continuous_det)).comp_continuousOn
        hfderiv

/-- The density-weighted explicit-real transition sends source chart
coordinates on the exact overlap to the independently normalized target
density on its exact fixed-carrier image. -/
theorem map_withDensity_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
            F hF hdet)) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
          F F' hF hdet hF' hdet' c)).withDensity
        (specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
          F F' hF' hdet' c) := by
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
  let ν :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c)
  let Ψ :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c
  let Ψm :=
    specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
      F F' hF hdet hF' hdet' c
  let J := fun x => ENNReal.ofReal |(fderiv ℝ Ψ x).det|
  let source :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
      F hF hdet
  let target :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
      F F' hF' hdet' c
  have hU :
      MeasurableSet
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c) :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hΨm : Measurable Ψm :=
    measurable_specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
      F F' hF hdet hF' hdet' c
  have htarget : Measurable target :=
    measurable_specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
      F F' hF' hdet' c
  have hJ : AEMeasurable J μ :=
    (continuousOn_abs_det_fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c).aemeasurable hU
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact
      specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
        F F' hF hdet hF' hdet' c x hx
  have hmap : Measure.map Ψm (μ.withDensity J) = ν := by
    calc
      Measure.map Ψm (μ.withDensity J) =
          Measure.map Ψ (μ.withDensity J) :=
        Measure.map_congr
          ((withDensity_absolutelyContinuous μ J).ae_eq hΨeq)
      _ = ν := by
        simpa [μ, ν, Ψ, J] using
          map_withDensity_abs_det_fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c
  have hcocycle : source =ᵐ[μ] (target ∘ Ψm) * J := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have hΨmx : Ψm x = Ψ x := by
      simpa [Ψm, Ψ] using
        specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
          F F' hF hdet hF' hdet' c x hx
    change source x = target (Ψm x) * J x
    rw [hΨmx]
    simpa [source, target, J, Ψ] using
      specialFormPreservingSmoothRealFormCongruenceAmbientDensityCocycle
        F F' hF hdet hF' hdet' c x hx
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
