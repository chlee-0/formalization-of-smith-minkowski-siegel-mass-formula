import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductAmbientDensity
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure

/-!
# Weighted square-transition measure for the identity north-pole product

This module combines the square-transition Jacobian pushforward with the
ambient product-density cocycle.  A measurable extension of the square
transition is used only for the generic `Measure.map` algebra and agrees with
the geometric transition on the restricted source.
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductWeightedSquareMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductWeightedSquareBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

/-- The square transition is smooth on its exact open source. -/
theorem
    contDiffOn_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
    (n : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  exact
    (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
      ).symm.contDiff.comp_contDiffOn
      (contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition_higherChartSource
        n)

/-- A globally measurable extension of the square transition from its exact
open source. -/
def
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n) :=
  Function.extend
    (Subtype.val :
      identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n →
        identitySpecialOrthogonalMappedTangent n ×
          EuclideanSpace ℝ (Fin n))
    (fun z =>
      identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n z.1)
    (fun _ => 0) x

/-- The measurable extension agrees with the square transition on the exact
source. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition_eq
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition n x =
      identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n x := by
  exact
    Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- The global square-transition extension is measurable. -/
theorem
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
        n) := by
  letI : OpensMeasurableSpace
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :=
    Subtype.opensMeasurableSpace _
  apply
    (MeasurableEmbedding.subtype_coe
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
        ).measurableSet).measurable_extend
      _ measurable_const
  have hcontinuous :
      Continuous (fun z :
        identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n =>
        identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n z.1) :=
    (contDiffOn_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
      n).continuousOn.restrict
  exact hcontinuous.measurable

/-- On the exact source, the ambient `fderiv` of the square transition is the
square derivative. -/
theorem
    fderiv_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_eq
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n) x =
      identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
        n x :=
  ((hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
    n hx).hasFDerivAt
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
        |>.mem_nhds hx)).fderiv

/-- The square Jacobian is continuous on the exact source. -/
theorem
    continuousOn_identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
    (n : ℕ) :
    ContinuousOn
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian n)
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  have hfderiv :=
    (contDiffOn_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
      n).continuousOn_fderiv_of_isOpen
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n)
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by simp)
  have hcontinuous :
      ContinuousOn
        (fun x => ENNReal.ofReal
          |LinearMap.det
            (fderiv ℝ
              (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
                n) x).toLinearMap|)
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_abs.comp
        ContinuousLinearMap.continuous_det)).comp_continuousOn hfderiv
  refine hcontinuous.congr ?_
  intro x hx
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian,
    ← fderiv_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_eq
      n x hx]

/-- The square Jacobian is almost-everywhere measurable for the exact
restricted source-coordinate measure. -/
theorem
    aemeasurable_identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
    (n : ℕ) :
    AEMeasurable
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian n)
      ((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
        n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)) :=
  (continuousOn_identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
    n).aemeasurable
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
      ).measurableSet

/-- The square transition sends the source-density-weighted exact product
coordinate measure to the pulled-back higher-density-weighted square target.
The fixed linear equivalence remains unapplied. -/
theorem
    map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap_sourceDensity
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n)
        (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
          n).restrict
          (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
            )).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      ((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
        n).restrict
        ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
          ).symm ''
          identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
        ).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
            n) := by
  let μ :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
      (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
  let ν :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
      ((identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n
        ).symm ''
        identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n)
  let f :=
    identitySpecialOrthogonalNorthPoleProductTransitionSquareMap n
  let fm :=
    identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition n
  let J :=
    identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian n
  let source :=
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n
  let target :=
    identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity n
  have hfm : Measurable fm :=
    measurable_identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition
      n
  have hJ : AEMeasurable J μ := by
    simpa [J, μ] using
      aemeasurable_identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
        n
  have htarget : Measurable target := by
    simpa [target] using
      measurable_identitySpecialOrthogonalNorthPoleProductAmbientSquareTargetDensity
        n
  have hfmeq : fm =ᵐ[μ] f := by
    filter_upwards [
      MeasureTheory.ae_restrict_mem
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
          ).measurableSet] with x hx
    exact
      identitySpecialOrthogonalNorthPoleProductMeasurableSquareTransition_eq
        n x hx
  have hmap : Measure.map fm (μ.withDensity J) = ν := by
    calc
      Measure.map fm (μ.withDensity J) =
          Measure.map f (μ.withDensity J) :=
        Measure.map_congr
          ((withDensity_absolutelyContinuous μ J).ae_eq hfmeq)
      _ = ν := by
        simpa [μ, ν, f, J,
          identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian]
          using
            map_withDensity_identitySpecialOrthogonalNorthPoleProductTransitionSquareMap
              n
  have hcocycle : source =ᵐ[μ] (target ∘ fm) * J := by
    filter_upwards [
      identitySpecialOrthogonalNorthPoleProductAmbientDensityCocycle_ae n,
      hfmeq] with x hx hfx
    simpa [source, target, J, Function.comp_apply, hfx] using hx
  have hweighted :
      Measure.map fm (μ.withDensity source) =
        ν.withDensity target :=
    map_withDensity_of_ae_density_cocycle
      fm μ ν J source target hfm hJ htarget hmap hcocycle
  calc
    Measure.map f (μ.withDensity source) =
        Measure.map fm (μ.withDensity source) :=
      Measure.map_congr
        ((withDensity_absolutelyContinuous μ source).ae_eq hfmeq.symm)
    _ = ν.withDensity target := hweighted

end PositiveDefiniteIntegralLattice
