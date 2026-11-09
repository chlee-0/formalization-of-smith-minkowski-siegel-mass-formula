import SMSFormula.PadicMultiplicativeAdditiveHaar
import SMSFormula.RationalPadicUnitSquareBranchChangeOfVariables

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Rat

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩
local instance : MeasurableSpace ℚ_[prime]ˣ := borel _
local instance : BorelSpace ℚ_[prime]ˣ := ⟨rfl⟩

private theorem map_unitSquare_restrict_multiplicative :
    Measure.map (fun value : ℚ_[prime]ˣ ↦ value ^ 2)
      (‖(2 : ℚ_[prime])‖₊ • (Measure.haar : Measure ℚ_[prime]ˣ).restrict
        (unitSquareIdentityChart ℚ_[prime]).source) =
      (Measure.haar : Measure ℚ_[prime]ˣ).restrict (unitSquareIdentityChart ℚ_[prime]).target := by
  let chart := unitSquareIdentityChart ℚ_[prime]
  have hbranch := RationalQuadraticSpaceMatrix.map_padicUnitSquareIdentityChartSourceMeasure prime
  rw [RationalQuadraticSpaceMatrix.padicUnitSquareBranchChangeOfVariables prime] at hbranch
  have hsource := (MeasurableEmbedding.subtype_coe chart.open_source.measurableSet).map_comap
    (Measure.haar : Measure ℚ_[prime]ˣ)
  have htarget := (MeasurableEmbedding.subtype_coe chart.open_target.measurableSet).map_comap
    (Measure.haar : Measure ℚ_[prime]ˣ)
  simp only [Subtype.range_coe] at hsource htarget
  have hcomp : (fun value : chart.source ↦ (value : ℚ_[prime]ˣ) ^ 2) =
      (Subtype.val : chart.target → ℚ_[prime]ˣ) ∘ chart.toHomeomorphSourceTarget := by
    funext value
    exact (unitSquareIdentityChart_apply ℚ_[prime] value).symm
  change Measure.map _ (‖(2 : ℚ_[prime])‖₊ • (Measure.haar : Measure ℚ_[prime]ˣ).restrict chart.source) = _
  rw [← hsource, Measure.map_smul, Measure.map_map (g := fun value : ℚ_[prime]ˣ ↦ value ^ 2)
    (continuous_id.pow 2).measurable measurable_subtype_coe]
  change ‖(2 : ℚ_[prime])‖₊ • Measure.map (fun value : chart.source ↦ (value : ℚ_[prime]ˣ) ^ 2) _ = _
  rw [hcomp, ← Measure.map_map measurable_subtype_coe chart.toHomeomorphSourceTarget.measurable,
    ← Measure.map_smul, ← Measure.map_smul]
  change Measure.map (Subtype.val : chart.target → ℚ_[prime]ˣ)
    (Measure.map chart.toHomeomorphSourceTarget
      (RationalQuadraticSpaceMatrix.rationalIdelePadicSquareModulus prime •
        RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartAmbientSourceMeasure prime)) = _
  rw [hbranch]
  exact htarget

variable (haar : Measure ℚ_[prime]) [haar.IsAddHaarMeasure]

theorem map_unitSquare_additiveUnitJacobian :
    Measure.map (fun value : ℚ_[prime]ˣ ↦ value ^ 2)
      (((Padic.additiveUnitMeasure prime haar).restrict (unitSquareIdentityChart ℚ_[prime]).source).withDensity
        (fun value : ℚ_[prime]ˣ ↦ (‖2 * (value : ℚ_[prime])‖₊ : ℝ≥0∞))) =
      (Padic.additiveUnitMeasure prime haar).restrict (unitSquareIdentityChart ℚ_[prime]).target := by
  let chart := unitSquareIdentityChart ℚ_[prime]
  let unitHaar := (Measure.haar : Measure ℚ_[prime]ˣ)
  let scalar := Padic.additiveToMultiplicativeHaarScalar prime haar unitHaar
  let weight := fun value : ℚ_[prime]ˣ ↦ (‖(value : ℚ_[prime])‖₊ : ℝ≥0∞)
  have hweight : Measurable weight := Units.continuous_val.nnnorm.measurable.coe_nnreal_ennreal
  have hjacobian : Measurable (fun value : ℚ_[prime]ˣ ↦ (‖2 * (value : ℚ_[prime])‖₊ : ℝ≥0∞)) :=
    (continuous_const.mul Units.continuous_val).nnnorm.measurable.coe_nnreal_ennreal
  have hsource :
      ((Padic.additiveUnitMeasure prime haar).restrict chart.source).withDensity
        (fun value : ℚ_[prime]ˣ ↦ (‖2 * (value : ℚ_[prime])‖₊ : ℝ≥0∞)) =
      scalar • (‖(2 : ℚ_[prime])‖₊ • unitHaar.restrict chart.source).withDensity
        (weight ∘ (fun value ↦ value ^ 2)) := by
    rw [Padic.additiveUnitMeasure_eq_weighted_multiplicative prime haar unitHaar,
      Measure.restrict_smul, restrict_withDensity chart.open_source.measurableSet]
    change ((scalar : ℝ≥0∞) • (unitHaar.restrict chart.source).withDensity weight).withDensity _ =
      (scalar : ℝ≥0∞) • ((‖(2 : ℚ_[prime])‖₊ : ℝ≥0∞) •
        unitHaar.restrict chart.source).withDensity _
    rw [withDensity_smul_measure, ← withDensity_mul _ hweight hjacobian,
      withDensity_smul_measure]
    congr 1
    rw [← withDensity_smul (f := weight ∘ (fun value : ℚ_[prime]ˣ ↦ value ^ 2)) _
      (hweight.comp (continuous_id.pow 2).measurable)]
    congr 1
    funext value
    simp [weight, nnnorm_mul, pow_two, mul_left_comm]
  change Measure.map _ (((Padic.additiveUnitMeasure prime haar).restrict chart.source).withDensity _) = _
  rw [hsource, Measure.map_smul,
    PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable (fun value : ℚ_[prime]ˣ ↦ value ^ 2) _ weight
      (continuous_id.pow 2).measurable hweight,
    map_unitSquare_restrict_multiplicative]
  rw [Padic.additiveUnitMeasure_eq_weighted_multiplicative prime haar unitHaar,
    Measure.restrict_smul, restrict_withDensity chart.open_target.measurableSet]

def padicUnitSquareScalarSource : Set ℚ_[prime] :=
  Units.val '' (unitSquareIdentityChart ℚ_[prime]).source

theorem isOpen_padicUnitSquareScalarSource : IsOpen (padicUnitSquareScalarSource prime) :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).isOpenMap _
    (unitSquareIdentityChart ℚ_[prime]).open_source

private theorem map_padicUnitSquareScalarSource_squareJacobian :
    Measure.map (fun value : ℚ_[prime] ↦ value ^ 2)
      ((haar.restrict (padicUnitSquareScalarSource prime)).withDensity
        (fun value : ℚ_[prime] ↦ (‖2 * value‖₊ : ℝ≥0∞))) =
      haar.restrict (Units.val '' (unitSquareIdentityChart ℚ_[prime]).target) := by
  have hval : Measurable (Units.val : ℚ_[prime]ˣ → ℚ_[prime]) := Units.continuous_val.measurable
  have hweight : Measurable (fun value : ℚ_[prime] ↦ (‖2 * value‖₊ : ℝ≥0∞)) :=
    (continuous_const.mul continuous_id).nnnorm.measurable.coe_nnreal_ennreal
  unfold padicUnitSquareScalarSource
  rw [← Padic.map_additiveUnitMeasure_restrict prime haar
    (unitSquareIdentityChart ℚ_[prime]).source]
  rw [← PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable Units.val _ _ hval hweight,
    Measure.map_map (g := fun value : ℚ_[prime] ↦ value ^ 2) (continuous_id.pow 2).measurable hval]
  have hcomp : (fun value : ℚ_[prime] ↦ value ^ 2) ∘ Units.val =
      Units.val ∘ (fun value : ℚ_[prime]ˣ ↦ value ^ 2) := by
    funext value
    simp
  rw [hcomp, ← Measure.map_map (f := fun value : ℚ_[prime]ˣ ↦ value ^ 2)
    hval (continuous_id.pow 2).measurable]
  dsimp only [Function.comp_def]
  rw [map_unitSquare_additiveUnitJacobian, Padic.map_additiveUnitMeasure_restrict]

theorem map_padicUnitSquareScalarSource_additiveJacobian
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) :
    Measure.map (fun value : ℚ_[prime] ↦ offset + coefficient * value ^ 2)
      ((haar.restrict (padicUnitSquareScalarSource prime)).withDensity
        (fun value : ℚ_[prime] ↦ (‖2 * coefficient * value‖₊ : ℝ≥0∞))) =
      haar.restrict ((fun value : ℚ_[prime]ˣ ↦ offset + coefficient * (value : ℚ_[prime])) ''
        (unitSquareIdentityChart ℚ_[prime]).target) := by
  have hweight : Measurable (fun value : ℚ_[prime] ↦ (‖2 * value‖₊ : ℝ≥0∞)) :=
    (continuous_const.mul continuous_id).nnnorm.measurable.coe_nnreal_ennreal
  have hfactor : (fun value : ℚ_[prime] ↦ (‖2 * coefficient * value‖₊ : ℝ≥0∞)) =
      (‖coefficient‖₊ : ℝ≥0∞) • (fun value : ℚ_[prime] ↦ (‖2 * value‖₊ : ℝ≥0∞)) := by
    funext value
    simp [nnnorm_mul, mul_assoc, mul_left_comm]
  rw [hfactor, withDensity_smul _ hweight]
  change Measure.map ((fun value : ℚ_[prime] ↦ offset + coefficient * value) ∘
    (fun value : ℚ_[prime] ↦ value ^ 2)) (‖coefficient‖₊ • _) = _
  rw [← Measure.map_map (g := fun value : ℚ_[prime] ↦ offset + coefficient * value)
    (f := fun value : ℚ_[prime] ↦ value ^ 2)
    (continuous_const.add (continuous_const.mul continuous_id)).measurable
    (continuous_id.pow 2).measurable,
    Measure.map_smul, map_padicUnitSquareScalarSource_squareJacobian,
    Padic.map_additiveHaar_affine_restrict prime haar offset coefficient hcoefficient]
  congr 1
  rw [Set.image_image]

theorem lintegral_padicUnitSquareScalarSource_additiveJacobian
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0)
    (test : ℚ_[prime] → ℝ≥0∞) (htest : Measurable test) :
    (∫⁻ value in (fun value : ℚ_[prime]ˣ ↦ offset + coefficient * (value : ℚ_[prime])) ''
      (unitSquareIdentityChart ℚ_[prime]).target, test value ∂haar) =
      ∫⁻ value in padicUnitSquareScalarSource prime,
        (‖2 * coefficient * value‖₊ : ℝ≥0∞) * test (offset + coefficient * value ^ 2) ∂haar := by
  rw [← map_padicUnitSquareScalarSource_additiveJacobian prime haar offset coefficient hcoefficient,
    lintegral_map (g := fun value : ℚ_[prime] ↦ offset + coefficient * value ^ 2)
      htest (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    (continuous_const.mul continuous_id).nnnorm.measurable.coe_nnreal_ennreal
    (htest.comp (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).measurable)

end Rat
