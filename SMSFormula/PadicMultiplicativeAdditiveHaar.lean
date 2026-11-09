import SMSFormula.PadicScalarAdditiveHaar
import SMSFormula.RationalCliffordGeneralSpinPadicIntegralCoordinates
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure
import Mathlib.Topology.Algebra.IsOpenUnits

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Padic

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩
local instance : MeasurableSpace ℚ_[prime]ˣ := borel _
local instance : BorelSpace ℚ_[prime]ˣ := ⟨rfl⟩

private theorem unitVal_openEmbedding : IsOpenEmbedding (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) :=
  IsOpenUnits.isOpenEmbedding_unitsVal

def additiveUnitMeasure (haar : Measure ℚ_[prime]) : Measure ℚ_[prime]ˣ :=
  Measure.comap Units.val haar

variable (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]

omit [haar.IsAddHaarMeasure] in
theorem map_additiveUnitMeasure_restrict (source : Set ℚ_[prime]ˣ) :
    Measure.map (Units.val : ℚ_[prime]ˣ → ℚ_[prime])
      ((additiveUnitMeasure prime haar).restrict source) =
      haar.restrict (Units.val '' source) := by
  have hval := (unitVal_openEmbedding prime).measurableEmbedding
  rw [additiveUnitMeasure, hval.restrict_comap, hval.map_comap,
    Measure.restrict_restrict hval.measurableSet_range,
    Set.inter_eq_right.mpr (Set.image_subset_range _ _)]

theorem map_additiveUnitMeasure_mul (unit : ℚ_[prime]ˣ) :
    Measure.map (fun value ↦ unit * value) (additiveUnitMeasure prime haar) =
      ‖(unit : ℚ_[prime])‖₊⁻¹ • additiveUnitMeasure prime haar := by
  have hval := (unitVal_openEmbedding prime).measurableEmbedding
  apply hval.map_injective
  rw [Measure.map_smul, additiveUnitMeasure, hval.map_comap,
    Measure.map_map (f := fun value ↦ unit * value) hval.measurable
      (Homeomorph.mulLeft unit).measurable]
  have hcomp : (fun value : ℚ_[prime]ˣ ↦ ((unit * value : ℚ_[prime]ˣ) : ℚ_[prime])) =
      (fun value : ℚ_[prime] ↦ (unit : ℚ_[prime]) * value) ∘ Units.val := rfl
  change Measure.map (fun value : ℚ_[prime]ˣ ↦ ((unit * value : ℚ_[prime]ˣ) : ℚ_[prime])) _ = _
  rw [hcomp, ← Measure.map_map (g := fun value : ℚ_[prime] ↦ (unit : ℚ_[prime]) * value)
    (continuous_const.mul continuous_id).measurable hval.measurable,
    hval.map_comap]
  have hpre : (fun value : ℚ_[prime] ↦ (unit : ℚ_[prime]) * value) ⁻¹'
      Set.range (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) =
      Set.range (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) := by
    ext value
    constructor
    · rintro ⟨witness, hwitness⟩
      refine ⟨unit⁻¹ * witness, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, hwitness,
        inv_mul_cancel_left₀ unit.ne_zero]
    · rintro ⟨witness, rfl⟩
      exact ⟨unit * witness, rfl⟩
  have hrestrict := Measure.restrict_map
    (f := fun value : ℚ_[prime] ↦ (unit : ℚ_[prime]) * value)
    (μ := haar) (continuous_const.mul continuous_id).measurable hval.measurableSet_range
  rw [hpre] at hrestrict
  rw [← hrestrict, map_additiveHaar_mul_unit, Measure.restrict_smul]

def inverseNormUnitWeight (value : ℚ_[prime]ˣ) : ℝ≥0∞ :=
  (‖(value : ℚ_[prime])‖₊ : ℝ≥0∞)⁻¹

theorem measurable_inverseNormUnitWeight : Measurable (inverseNormUnitWeight prime) :=
  (Units.continuous_val.nnnorm.measurable.coe_nnreal_ennreal).inv

def multiplicativeMeasureFromAdditive (haar : Measure ℚ_[prime]) : Measure ℚ_[prime]ˣ :=
  (additiveUnitMeasure prime haar).withDensity (inverseNormUnitWeight prime)

theorem map_multiplicativeMeasureFromAdditive_mul (unit : ℚ_[prime]ˣ) :
    Measure.map (fun value ↦ unit * value) (multiplicativeMeasureFromAdditive prime haar) =
      multiplicativeMeasureFromAdditive prime haar := by
  let weight := inverseNormUnitWeight prime
  let shiftedWeight := fun value : ℚ_[prime]ˣ ↦ weight (unit⁻¹ * value)
  have hshift : weight = shiftedWeight ∘ (fun value ↦ unit * value) := by
    funext value
    simp [shiftedWeight]
  have hshiftMeas : Measurable shiftedWeight :=
    (measurable_inverseNormUnitWeight prime).comp (Homeomorph.mulLeft unit⁻¹).measurable
  have hnorm : ‖(unit : ℚ_[prime])‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr unit.ne_zero
  have hscaled : shiftedWeight = fun value ↦
      (‖(unit : ℚ_[prime])‖₊ : ℝ≥0∞) * weight value := by
    funext value
    simp [shiftedWeight, weight, inverseNormUnitWeight, nnnorm_mul,
      ENNReal.coe_inv hnorm, ENNReal.mul_inv]
  unfold multiplicativeMeasureFromAdditive
  change Measure.map _ ((additiveUnitMeasure prime haar).withDensity weight) = _
  rw [hshift, PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable (fun value ↦ unit * value) _ _
    (Homeomorph.mulLeft unit).measurable hshiftMeas,
    map_additiveUnitMeasure_mul, hscaled]
  ext measurableSet hmeasurableSet
  rw [withDensity_apply _ hmeasurableSet, withDensity_apply _ hmeasurableSet,
    Measure.restrict_smul, lintegral_smul_measure,
    lintegral_const_mul _ (measurable_inverseNormUnitWeight prime)]
  change (↑(‖(unit : ℚ_[prime])‖₊⁻¹) : ℝ≥0∞) *
    ((‖(unit : ℚ_[prime])‖₊ : ℝ≥0∞) * _) = _
  rw [ENNReal.coe_inv hnorm, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hnorm) ENNReal.coe_ne_top, one_mul]

instance multiplicativeMeasureFromAdditive_isMulLeftInvariant :
    (multiplicativeMeasureFromAdditive prime haar).IsMulLeftInvariant :=
  ⟨map_multiplicativeMeasureFromAdditive_mul prime haar⟩

instance additiveUnitMeasure_isOpenPosMeasure :
    (additiveUnitMeasure prime haar).IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap haar (unitVal_openEmbedding prime)

private theorem inverseNormUnitWeight_eq_one_on_integralUnits
    (value : ℚ_[prime]ˣ)
    (hvalue : value ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup prime) :
    inverseNormUnitWeight prime value = 1 := by
  have hnorm : ‖(value : ℚ_[prime])‖ ≤ 1 := hvalue.1
  have hinv : ‖((value⁻¹ : ℚ_[prime]ˣ) : ℚ_[prime])‖ ≤ 1 := hvalue.2
  have hproduct : ‖(value : ℚ_[prime])‖ * ‖((value⁻¹ : ℚ_[prime]ˣ) : ℚ_[prime])‖ = 1 := by
    rw [← norm_mul]
    simp
  have hone : ‖(value : ℚ_[prime])‖₊ = 1 := by
    apply NNReal.eq
    change ‖(value : ℚ_[prime])‖ = 1
    nlinarith [norm_nonneg (value : ℚ_[prime])]
  simp [inverseNormUnitWeight, hone]

instance multiplicativeMeasureFromAdditive_isHaarMeasure :
    (multiplicativeMeasureFromAdditive prime haar).IsHaarMeasure := by
  let compactUnits := (RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup prime : Set ℚ_[prime]ˣ)
  have hopen : IsOpen compactUnits := RationalQuadraticSpaceMatrix.isOpen_padicIntegralUnitsSubgroup prime
  have hcompact : IsCompact compactUnits := RationalQuadraticSpaceMatrix.isCompact_padicIntegralUnitsSubgroup prime
  have hnonempty : compactUnits.Nonempty := ⟨1, (RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup prime).one_mem⟩
  have hmass : multiplicativeMeasureFromAdditive prime haar compactUnits =
      additiveUnitMeasure prime haar compactUnits := by
    rw [multiplicativeMeasureFromAdditive, withDensity_apply _ hopen.measurableSet]
    calc
      _ = ∫⁻ _ in compactUnits, (1 : ℝ≥0∞) ∂additiveUnitMeasure prime haar := by
        apply setLIntegral_congr_fun hopen.measurableSet
        exact inverseNormUnitWeight_eq_one_on_integralUnits prime
      _ = _ := by simp
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
    (multiplicativeMeasureFromAdditive prime haar) compactUnits hcompact
    (by rwa [hopen.interior_eq])
  · rw [hmass]
    exact hopen.measure_ne_zero _ hnonempty
  · rw [hmass, additiveUnitMeasure,
      (unitVal_openEmbedding prime).measurableEmbedding.comap_apply]
    exact (hcompact.image Units.continuous_val).measure_ne_top

local instance : SecondCountableTopology ℚ_[prime]ˣ := by
  letI : SecondCountableTopology ℚ_[prime]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[prime] × ℚ_[prime]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable (unitHaar : Measure ℚ_[prime]ˣ) [unitHaar.IsHaarMeasure]

def additiveToMultiplicativeHaarScalar : ℝ≥0 :=
  Measure.haarScalarFactor (multiplicativeMeasureFromAdditive prime haar) unitHaar

theorem additiveToMultiplicativeHaarScalar_pos :
    0 < additiveToMultiplicativeHaarScalar prime haar unitHaar :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem multiplicativeMeasureFromAdditive_eq_smul :
    multiplicativeMeasureFromAdditive prime haar =
      additiveToMultiplicativeHaarScalar prime haar unitHaar • unitHaar :=
  Measure.isMulLeftInvariant_eq_smul_of_regular _ _

theorem additiveUnitMeasure_eq_weighted_multiplicative :
    additiveUnitMeasure prime haar =
      additiveToMultiplicativeHaarScalar prime haar unitHaar •
        unitHaar.withDensity (fun value : ℚ_[prime]ˣ ↦ (‖(value : ℚ_[prime])‖₊ : ℝ≥0∞)) := by
  have hcancel := withDensity_inv_same₀
    (μ := additiveUnitMeasure prime haar)
    (measurable_inverseNormUnitWeight prime).aemeasurable
    (Filter.Eventually.of_forall fun value ↦ by
      simp [inverseNormUnitWeight])
    (Filter.Eventually.of_forall fun value ↦ by
      simp [inverseNormUnitWeight, value.ne_zero])
  have hinverse : (fun value : ℚ_[prime]ˣ ↦ (inverseNormUnitWeight prime value)⁻¹) =
      (fun value : ℚ_[prime]ˣ ↦ (‖(value : ℚ_[prime])‖₊ : ℝ≥0∞)) := by
    funext value
    simp [inverseNormUnitWeight]
  rw [hinverse] at hcancel
  rw [← hcancel]
  change (multiplicativeMeasureFromAdditive prime haar).withDensity _ = _
  rw [multiplicativeMeasureFromAdditive_eq_smul prime haar unitHaar]
  exact withDensity_smul_measure _ _

end Padic
