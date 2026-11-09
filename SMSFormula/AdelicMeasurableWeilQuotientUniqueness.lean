import SMSFormula.AdelicWeilQuotient
import Mathlib.MeasureTheory.Group.Measure
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Uniqueness of measurable Weil quotient measures

An exact measurable fundamental domain makes the measurable Weil formula
determine the quotient measure.  Consequently, after inversion invariance
identifies the left and right ambient measures, the transported right
quotient is Mathlib's canonical fundamental-domain quotient measure.  Its
`QuotientMeasureEqMeasurePreimage` instance then makes comparison with any
other canonical quotient measure automatic.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open MeasureTheory
open scoped ENNReal

universe u

/-- An exact measurable fundamental domain makes the measurable left Weil
formula determine the quotient measure uniquely. -/
theorem IsLeftMeasurableWeilQuotientMeasure.eq_leftQuotientFundamentalDomainMeasure
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G) [Countable Gamma]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) inferInstance)
    {muG : Measure G} {muX : Measure (leftCosetSet Gamma)}
    (hWeil : IsLeftMeasurableWeilQuotientMeasure Gamma muG muX)
    {F : Set G} (hFmeas : MeasurableSet F)
    (hunique : ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ F) :
    muX = leftQuotientFundamentalDomainMeasure Gamma muG F := by
  apply Measure.ext
  intro A hA
  let S : Set G := F ∩ (leftCosetMap Gamma) ⁻¹' A
  have hq : Measurable (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  have hS : MeasurableSet S := hFmeas.inter (hq hA)
  have hperiod :
      leftPeriodize Gamma (S.indicator (fun _ => (1 : ℝ≥0∞))) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext X
    induction X using Quot.inductionOn with
    | h x =>
      change
        leftPeriodize Gamma (S.indicator (fun _ => (1 : ℝ≥0∞)))
            (leftCosetMap Gamma x) =
          A.indicator (fun _ => (1 : ℝ≥0∞)) (leftCosetMap Gamma x)
      rw [leftPeriodize_leftCosetMap]
      unfold leftPreperiodize
      obtain ⟨gamma, hgamma, hgamma_unique⟩ := hunique x
      by_cases hxA : leftCosetMap Gamma x ∈ A
      · rw [tsum_eq_single gamma]
        · have hcoset :
              leftCosetMap Gamma ((gamma : G) * x) =
                leftCosetMap Gamma x :=
            leftCosetMap_gamma_mul Gamma gamma x
          simp [S, hgamma, hcoset, hxA]
        · intro delta hdelta
          have hdeltaF : (delta : G) * x ∉ F := by
            intro hmem
            exact hdelta (hgamma_unique delta hmem)
          simp [S, hdeltaF]
      · rw [tsum_eq_single gamma]
        · have hcoset :
              leftCosetMap Gamma ((gamma : G) * x) =
                leftCosetMap Gamma x :=
            leftCosetMap_gamma_mul Gamma gamma x
          simp [S, hcoset, hxA]
        · intro delta _hdelta
          have hcoset :
              leftCosetMap Gamma ((delta : G) * x) =
                leftCosetMap Gamma x :=
            leftCosetMap_gamma_mul Gamma delta x
          simp [S, hcoset, hxA]
  rw [leftQuotientFundamentalDomainMeasure_apply_map_mspace
    (Gamma := Gamma) (μG := muG) (F := F) hmX hA]
  have hlin := hWeil.lintegral_leftPeriodize_eq
    (S.indicator (fun _ => (1 : ℝ≥0∞)))
    ((measurable_const : Measurable fun _ : G => (1 : ℝ≥0∞)).indicator hS)
  rw [hperiod] at hlin
  simpa [S, lintegral_indicator, hA, hS] using hlin

end PositiveDefiniteIntegralLattice
