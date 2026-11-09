import SMSFormula.RationalPadicUnitSquareAdditiveHaar

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace Rat

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩
local instance : MeasurableSpace ℚ_[prime]ˣ := borel _
local instance : BorelSpace ℚ_[prime]ˣ := ⟨rfl⟩

theorem measurableEmbedding_padicUnitSquareScalarBranch
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) :
    MeasurableEmbedding (fun value : (unitSquareIdentityChart ℚ_[prime]).source ↦
      offset + coefficient * ((value : ℚ_[prime]ˣ) : ℚ_[prime]) ^ 2) := by
  have hval : IsOpenEmbedding (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
  have htarget := hval.comp (unitSquareIdentityChart ℚ_[prime]).open_target.isOpenEmbedding_subtypeVal
  have hbranch := htarget.comp (unitSquareIdentityChart ℚ_[prime]).toHomeomorphSourceTarget.isOpenEmbedding
  have haffine := ((Homeomorph.mulLeft₀ coefficient hcoefficient).trans
    (Homeomorph.addLeft offset)).isOpenEmbedding.comp hbranch
  convert haffine.measurableEmbedding using 1
  funext value
  simp [Function.comp_def, unitSquareIdentityChart_apply]

theorem lintegral_padicUnitSquareScalarSource_additiveJacobian_arbitrary
    (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0)
    (test : ℚ_[prime] → ℝ≥0∞) :
    (∫⁻ value in (fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
      (unitSquareIdentityChart ℚ_[prime]).target, test value ∂haar) =
      ∫⁻ scalar in padicUnitSquareScalarSource prime,
        (‖2 * coefficient * scalar‖₊ : ℝ≥0∞) * test (offset + coefficient * scalar ^ 2) ∂haar := by
  let source := (unitSquareIdentityChart ℚ_[prime]).source
  let inclusion : source → ℚ_[prime] := fun value ↦ ((value : ℚ_[prime]ˣ) : ℚ_[prime])
  let forward := fun scalar : ℚ_[prime] ↦ offset + coefficient * scalar ^ 2
  let weighted := (haar.restrict (padicUnitSquareScalarSource prime)).withDensity
    (fun scalar : ℚ_[prime] ↦ (‖2 * coefficient * scalar‖₊ : ℝ≥0∞))
  have hinclusion : MeasurableEmbedding inclusion :=
    ((IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).comp
      (unitSquareIdentityChart ℚ_[prime]).open_source.isOpenEmbedding_subtypeVal).measurableEmbedding
  have hrange : Set.range inclusion = padicUnitSquareScalarSource prime := by
    ext scalar
    constructor
    · rintro ⟨value, rfl⟩
      exact ⟨value, value.property, rfl⟩
    · rintro ⟨unit, hunit, rfl⟩
      exact ⟨⟨unit, hunit⟩, rfl⟩
  have hsupport : Measure.map inclusion (Measure.comap inclusion weighted) = weighted := by
    rw [hinclusion.map_comap, hrange]
    dsimp only [weighted]
    rw [restrict_withDensity (isOpen_padicUnitSquareScalarSource prime).measurableSet,
      Measure.restrict_restrict_of_subset (Subset.refl _)]
  have hforward : Measurable forward :=
    (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).measurable
  have hfirst := (measurableEmbedding_padicUnitSquareScalarBranch prime offset coefficient hcoefficient).lintegral_map
    (μ := Measure.comap inclusion weighted) test
  change (∫⁻ value, test value ∂Measure.map (forward ∘ inclusion) (Measure.comap inclusion weighted)) = _ at hfirst
  rw [← Measure.map_map hforward hinclusion.measurable, hsupport] at hfirst
  have hsecond := hinclusion.lintegral_map (μ := Measure.comap inclusion weighted) (fun scalar ↦ test (forward scalar))
  rw [hsupport] at hsecond
  rw [← map_padicUnitSquareScalarSource_additiveJacobian prime haar offset coefficient hcoefficient]
  change (∫⁻ value, test value ∂Measure.map forward weighted) = _
  rw [hfirst, ← hsecond]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable
    (haar.restrict (padicUnitSquareScalarSource prime))
    (f := fun scalar : ℚ_[prime] ↦ (‖2 * coefficient * scalar‖₊ : ℝ≥0∞))
    (continuous_const.mul continuous_id).nnnorm.measurable.coe_nnreal_ennreal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.coe_lt_top)
    (fun scalar ↦ test (forward scalar))

def padicUnitSquareScalarInverse (value : ℚ_[prime]) : ℚ_[prime] := by
  classical
  exact if hvalue : value ≠ 0 then
    ((unitSquareIdentityChart ℚ_[prime]).symm (Units.mk0 value hvalue) : ℚ_[prime])
  else 0

theorem padicUnitSquareScalarSource_ne_zero {scalar : ℚ_[prime]}
    (hscalar : scalar ∈ padicUnitSquareScalarSource prime) : scalar ≠ 0 := by
  obtain ⟨unit, _, rfl⟩ := hscalar
  exact unit.ne_zero

theorem padicUnitSquareScalarInverse_sq {scalar : ℚ_[prime]}
    (hscalar : scalar ∈ padicUnitSquareScalarSource prime) :
    padicUnitSquareScalarInverse prime (scalar ^ 2) = scalar := by
  obtain ⟨unit, hunit, rfl⟩ := hscalar
  rw [padicUnitSquareScalarInverse, dif_pos (pow_ne_zero 2 unit.ne_zero)]
  have hinput : Units.mk0 ((unit : ℚ_[prime]) ^ 2) (pow_ne_zero 2 unit.ne_zero) =
      unitSquareIdentityChart ℚ_[prime] unit := by
    apply Units.ext
    simp only [Units.val_mk0, unitSquareIdentityChart_apply, Units.val_pow_eq_pow_val]
  rw [hinput, (unitSquareIdentityChart ℚ_[prime]).left_inv hunit]

theorem padicUnitSquareScalarInverse_mem_and_sq {value : ℚ_[prime]}
    (hvalue : value ∈ (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) '' (unitSquareIdentityChart ℚ_[prime]).target) :
    padicUnitSquareScalarInverse prime value ∈ padicUnitSquareScalarSource prime ∧
      padicUnitSquareScalarInverse prime value ^ 2 = value := by
  obtain ⟨unit, hunit, rfl⟩ := hvalue
  rw [padicUnitSquareScalarInverse, dif_pos unit.ne_zero]
  have hinput : Units.mk0 (unit : ℚ_[prime]) unit.ne_zero = unit := Units.ext rfl
  rw [hinput]
  constructor
  · exact ⟨(unitSquareIdentityChart ℚ_[prime]).symm unit, (unitSquareIdentityChart ℚ_[prime]).map_target hunit, rfl⟩
  · have hinverse := congrArg Units.val ((unitSquareIdentityChart ℚ_[prime]).right_inv hunit)
    simpa only [unitSquareIdentityChart_apply, Units.val_pow_eq_pow_val] using hinverse

theorem padicUnitSquareScalarInverse_affine_square
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) {scalar : ℚ_[prime]}
    (hscalar : scalar ∈ padicUnitSquareScalarSource prime) :
    padicUnitSquareScalarInverse prime ((offset + coefficient * scalar ^ 2 - offset) / coefficient) = scalar := by
  rw [show (offset + coefficient * scalar ^ 2 - offset) / coefficient = scalar ^ 2 by
    field_simp
    ring]
  exact padicUnitSquareScalarInverse_sq prime hscalar

theorem lintegral_padicUnitSquareScalarSource_substitution
    (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) (weight : ℚ_[prime] → ℝ≥0∞) :
    (∫⁻ scalar in padicUnitSquareScalarSource prime, weight scalar ∂haar) =
      ∫⁻ value in (fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
        (unitSquareIdentityChart ℚ_[prime]).target,
        weight (padicUnitSquareScalarInverse prime ((value - offset) / coefficient)) /
          (‖2 * coefficient * padicUnitSquareScalarInverse prime ((value - offset) / coefficient)‖₊ : ℝ≥0∞)
        ∂haar := by
  rw [lintegral_padicUnitSquareScalarSource_additiveJacobian_arbitrary prime haar offset coefficient hcoefficient]
  apply setLIntegral_congr_fun (isOpen_padicUnitSquareScalarSource prime).measurableSet
  intro scalar hscalar
  dsimp only
  rw [padicUnitSquareScalarInverse_affine_square prime offset coefficient hcoefficient hscalar]
  have hnonzero : (‖2 * coefficient * scalar‖₊ : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) hcoefficient)
        (padicUnitSquareScalarSource_ne_zero prime hscalar)))
  rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hnonzero ENNReal.coe_ne_top, mul_one]

theorem isOpen_padicUnitSquareScalarAffineTarget
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) :
    IsOpen ((fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
      (unitSquareIdentityChart ℚ_[prime]).target) := by
  have hopen := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).isOpenMap _
    (unitSquareIdentityChart ℚ_[prime]).open_target
  have hscaled := (Homeomorph.mulLeft₀ coefficient hcoefficient).isOpenMap _ hopen
  have htranslated := (Homeomorph.addLeft offset).isOpenMap _ hscaled
  simpa only [Set.image_image, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addLeft] using htranslated

theorem padicUnitSquareScalarInverse_affine_target
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) {value : ℚ_[prime]}
    (hvalue : value ∈ (fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
      (unitSquareIdentityChart ℚ_[prime]).target) :
    offset + coefficient * padicUnitSquareScalarInverse prime ((value - offset) / coefficient) ^ 2 = value := by
  obtain ⟨unit, hunit, rfl⟩ := hvalue
  rw [show (offset + coefficient * (unit : ℚ_[prime]) - offset) / coefficient = (unit : ℚ_[prime]) by
    field_simp
    ring]
  rw [(padicUnitSquareScalarInverse_mem_and_sq prime ⟨unit, hunit, rfl⟩).2]

theorem lintegral_padicUnitSquareScalarSource_weighted_value
    (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0)
    (weight test : ℚ_[prime] → ℝ≥0∞) :
    (∫⁻ scalar in padicUnitSquareScalarSource prime,
      weight scalar * test (offset + coefficient * scalar ^ 2) ∂haar) =
      ∫⁻ value in (fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
        (unitSquareIdentityChart ℚ_[prime]).target,
        weight (padicUnitSquareScalarInverse prime ((value - offset) / coefficient)) * test value /
          (‖2 * coefficient * padicUnitSquareScalarInverse prime ((value - offset) / coefficient)‖₊ : ℝ≥0∞)
        ∂haar := by
  rw [lintegral_padicUnitSquareScalarSource_substitution prime haar offset coefficient hcoefficient]
  apply setLIntegral_congr_fun (isOpen_padicUnitSquareScalarAffineTarget prime offset coefficient hcoefficient).measurableSet
  intro value hvalue
  dsimp only
  rw [padicUnitSquareScalarInverse_affine_target prime offset coefficient hcoefficient hvalue]

end Rat
