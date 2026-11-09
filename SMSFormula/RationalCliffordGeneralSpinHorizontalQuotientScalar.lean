import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialWeilQuotient

/-!
# The exact scalar on the common rational GSpin quotient

The concrete horizontal bind has two independently established descriptions on
the exact rational adelic `GSpin` quotient.  Periodization compares it with the
fixed horizontal common quotient.  Differential central-extension
disintegration instead contributes, separately, the rational idele-class Haar
conversion, the lattice finite-stabilizer volume, and the ambient differential-
to-horizontal Haar conversion.

This file proves that the common quotient is nonzero and cancels it on one
finite positive logarithmic strip.  The resulting equality identifies the
periodization scalar with the product of those three literal scales.  No scale
is set to one and no local chart or new quotient is introduced.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix Set
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The certified common horizontal rational `GSpin` quotient is nonzero.
This follows from the already certified nonzero concrete horizontal bind and
its exact periodization-scalar formula. -/
theorem fullAdelicCliffordGeneralSpinHorizontalQuotientMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
        |>.quotientMeasure) ≠ 0 := by
  intro hzero
  have hmeasure :=
    L.horizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
      hn inst hP hconv
  rw [hzero, smul_zero] at hmeasure
  exact L.horizontalRawSOFiberHaarBoundMeasure_ne_zero
    hn inst hP hconv hmeasure

/-- The concrete periodization scalar is exactly the product of the
independent rational idele-class conversion, the lattice differential
finite-stabilizer volume, and the ambient differential-to-horizontal Haar
conversion. -/
theorem
    periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_eq_differentialScales
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        hn inst hP hconv =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L hn inst hP hconv
  let μ := V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let ν := L.horizontalRawSOFiberHaarBoundMeasure inst D
  let c := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    hn inst hP hconv
  let a : ℝ≥0∞ := rationalIdeleClassHaarToDifferentialWeilScalar
  let t := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  let b : ℝ≥0∞ := L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S
  have hperiod : ν = c • μ := by
    simpa only [V, D, μ, ν, c] using
      L.horizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
        hn inst hP hconv
  have hclass : ν = a •
      L.horizontalDifferentialWeilSOFiberBoundMeasure inst
        D.specialOrthogonalData.quotientMeasure := by
    simpa only [D, ν, a] using
      L.horizontalRawSOFiberHaarBoundMeasure_eq_smul_differentialWeil inst D
  have hdiff :
      L.horizontalDifferentialWeilSOFiberBoundMeasure inst
          D.specialOrthogonalData.quotientMeasure =
        (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
          ).quotientMeasure := by
    simpa only [D] using
      L.horizontalDifferentialWeilSOFiberBoundMeasure_eq_ambientQuotient
        hn inst hP hconv S
  have hambient :
      (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
        ).quotientMeasure = t • (b • μ) := by
    simpa only [V, μ, t, b] using
      L.fullAdelicDifferentialCentralFiberMeasurableWeilData_quotientMeasure hP S
  have hscaled : c • μ = (a * t * b) • μ := by
    calc
      c • μ = ν := hperiod.symm
      _ = a • L.horizontalDifferentialWeilSOFiberBoundMeasure inst
          D.specialOrthogonalData.quotientMeasure := hclass
      _ = a • (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
          ).quotientMeasure := congrArg (fun ρ => a • ρ) hdiff
      _ = a • (t • (b • μ)) := congrArg (fun ρ => a • ρ) hambient
      _ = (a * t * b) • μ := by rw [smul_smul, smul_smul]
  have hνzero : ν ≠ 0 := by
    simpa only [D, ν] using
      L.horizontalRawSOFiberHaarBoundMeasure_ne_zero hn inst hP hconv
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      ν (L.horizontalRawSOFiberHaarBoundSpanningSet m) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hνzero
    rw [← Measure.measure_univ_eq_zero,
      ← L.iUnion_horizontalRawSOFiberHaarBoundSpanningSet]
    exact measure_iUnion_null hall
  let A := L.horizontalRawSOFiberHaarBoundSpanningSet m
  have hA : MeasurableSet A := by
    exact L.measurableSet_horizontalRawSOFiberHaarBoundSpanningSet m
  have hνtop : ν A ≠ ∞ := by
    exact (L.horizontalRawSOFiberHaarBoundSpanningSet_measure_lt_top
      hn inst hP hconv m).ne
  have hperiodA : ν A = c * μ A := by
    have := congrArg (fun ρ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient =>
      ρ A) hperiod
    simpa only [Measure.smul_apply, smul_eq_mul, hA] using this
  have hc0 : c ≠ 0 := by
    exact L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero
      hn inst hP hconv
  have hμ0 : μ A ≠ 0 := by
    intro hzero
    apply hm
    rw [hperiodA, hzero, mul_zero]
  have hμtop : μ A ≠ ∞ := by
    intro htop
    apply hνtop
    rw [hperiodA, htop, ENNReal.mul_top hc0]
  have hscaledA := congrArg
    (fun ρ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient => ρ A) hscaled
  have hmul : μ A * c = μ A * (a * t * b) := by
    simpa only [Measure.smul_apply, smul_eq_mul, hA, mul_comm] using hscaledA
  exact (ENNReal.mul_right_inj hμ0 hμtop).mp hmul

end PositiveDefiniteIntegralLattice
