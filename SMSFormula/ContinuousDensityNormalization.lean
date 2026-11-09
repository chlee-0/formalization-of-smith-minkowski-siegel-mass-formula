import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {carrier : Type*} [TopologicalSpace carrier] [MeasurableSpace carrier]
  [BorelSpace carrier]

omit [TopologicalSpace carrier] [BorelSpace carrier] in
theorem withDensity_div_of_smul_eq (haar measure : Measure carrier)
    (density : carrier → ℝ≥0∞) (scalar : ℝ≥0) (hscalar : scalar ≠ 0)
    (hmeasure : (scalar : ℝ≥0∞) • measure = haar.withDensity density) :
    haar.withDensity (fun value ↦ density value / (scalar : ℝ≥0∞)) = measure := by
  have hnonzero : (scalar : ℝ≥0∞) ≠ 0 := by exact_mod_cast hscalar
  have hinverse : (scalar : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hnonzero
  calc
    _ = haar.withDensity ((scalar : ℝ≥0∞)⁻¹ • density) := by
      congr 1
      funext value
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    _ = (scalar : ℝ≥0∞)⁻¹ • haar.withDensity density :=
      withDensity_smul' _ _ hinverse
    _ = measure := by
      rw [← hmeasure, smul_smul, ENNReal.inv_mul_cancel hnonzero ENNReal.coe_ne_top, one_smul]

theorem continuous_density_div_eq_of_smul_eq (haar measure : Measure carrier)
    [SigmaFinite haar] [haar.IsOpenPosMeasure]
    (first second : carrier → ℝ≥0∞) (hfirst : Continuous first) (hsecond : Continuous second)
    (firstScalar secondScalar : ℝ≥0) (hfirstScalar : firstScalar ≠ 0) (hsecondScalar : secondScalar ≠ 0)
    (hfirstMeasure : (firstScalar : ℝ≥0∞) • measure = haar.withDensity first)
    (hsecondMeasure : (secondScalar : ℝ≥0∞) • measure = haar.withDensity second) :
    (fun value ↦ first value / (firstScalar : ℝ≥0∞)) =
      (fun value ↦ second value / (secondScalar : ℝ≥0∞)) := by
  have hfirstNonzero : (firstScalar : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfirstScalar
  have hsecondNonzero : (secondScalar : ℝ≥0∞) ≠ 0 := by exact_mod_cast hsecondScalar
  have hfirstContinuous := (ENNReal.continuous_div_const _ hfirstNonzero).comp hfirst
  have hsecondContinuous := (ENNReal.continuous_div_const _ hsecondNonzero).comp hsecond
  apply Measure.eq_of_ae_eq (μ := haar) _ hfirstContinuous hsecondContinuous
  apply (withDensity_eq_iff_of_sigmaFinite hfirstContinuous.measurable.aemeasurable
    hsecondContinuous.measurable.aemeasurable).mp
  dsimp only [Function.comp_def]
  rw [withDensity_div_of_smul_eq haar measure first firstScalar hfirstScalar hfirstMeasure,
    withDensity_div_of_smul_eq haar measure second secondScalar hsecondScalar hsecondMeasure]

end MeasureTheory.Measure
