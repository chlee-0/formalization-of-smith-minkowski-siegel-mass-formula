import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedPeriodizedRestriction
import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientScalar
import SMSFormula.RationalCliffordSpinCandidateLatticeCofinalRawBlockScaleComparison
import SMSFormula.RationalCliffordGeneralSpinCrossedCutoffExtraction

/-!
# The common compact-unit cutoff for the lattice Spin--SO comparison

The retained vertical-cylinder calibration determines the vertical
periodization scalar.  On the canonical exceptional enlargement, the raw
Spin block agrees with the raw special-orthogonal block.  Comparing this with
the independently calibrated horizontal periodization therefore identifies
the two scalars on the common rational `GSpin` quotient.

Integrating the fixed compact logarithmic cutoff against that quotient gives
the horizontal and vertical crossed-cutoff equality required by the existing
relative Tamagawa extraction theorem.  The finite-stage block weights remain
explicit throughout; no `2 ^ |F|` factor is cancelled.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2500000

local instance relativeUnitCutoffDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The vertical and horizontal periodization scalars agree for the lattice raw
datum.  The proof retains the common finite block and cancels only the
positive finite differential-cylinder scale. -/
theorem
    periodizedVerticalSpinFiberHaarBoundRightHaarScalar_eq_horizontal_of_lattice
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L (by omega)
        (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
          (by omega)) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) inst hP hconv := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let S := V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv
  let hsurj :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  let d : ℝ≥0∞ :=
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  let q : ℝ≥0∞ :=
    D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L (by omega) hsurj
  let c : ℝ≥0∞ :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega) inst hP hconv
  let a : ℝ≥0∞ := rationalIdeleClassHaarToDifferentialWeilScalar
  let t : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  let spinBlock : ℝ≥0∞ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
  let soBlock : ℝ≥0∞ := V.finiteAdelicSpecialOrthogonalBlockWeight B
  have hSB : S ⊆ B := by
    intro v hv
    simp [B, E,
      cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces,
      cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces,
      hv]
  have hvertical : d * q = a * ((D.spinFiniteScale : ℝ≥0∞) * spinBlock) := by
    simpa only [V, S, E, B, D, hsurj, d, q, a, spinBlock] using
      L.horizontalCylinderScale_mul_periodizedVerticalSpinFiberHaarBoundRightHaarScalar_eq_conversion_mul_block
        hr D hsurj S
  have hblock :
      (D.spinFiniteScale : ℝ≥0∞) * spinBlock = t * soBlock := by
    simpa only [V, D, t, spinBlock, soBlock] using
      L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinScale_mul_blockWeight_eq_soScale_mul_blockWeight_of_comparisonBadPlaces_subset
        (by omega) inst hP hconv B hSB
  have hhorizontal :
      c = a * t * (soBlock * d⁻¹) := by
    rw [show c =
        (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
          L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
            (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) by
      simpa only [c] using
        L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_eq_differentialScales
          (by omega) inst hP hconv S]
    rw [L.coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S]
  have hd0 : d ≠ 0 := by
    exact L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_zero S
  have hdtop : d ≠ ∞ := by
    exact L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale_ne_top S
  have hdc : d * q = d * c := by
    calc
      d * q = a * ((D.spinFiniteScale : ℝ≥0∞) * spinBlock) := hvertical
      _ = a * (t * soBlock) := by rw [hblock]
      _ = d * (a * t * (soBlock * d⁻¹)) := by
        symm
        calc
          d * (a * t * (soBlock * d⁻¹)) =
              a * (t * soBlock) * (d * d⁻¹) := by ac_rfl
          _ = a * (t * soBlock) := by
            rw [ENNReal.mul_inv_cancel hd0 hdtop, mul_one]
      _ = d * c := by rw [hhorizontal]
  exact (ENNReal.mul_right_inj hd0 hdtop).mp hdc

/-- The two concrete quotient measures are equal after the ambient scalar
calibration.  This is the common-quotient form of the unit-cutoff comparison. -/
theorem
    horizontalRawSOFiberHaarBoundMeasure_eq_verticalSpinFiberHaarBoundMeasure_of_lattice
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    L.horizontalRawSOFiberHaarBoundMeasure inst D =
      D.verticalSpinFiberHaarBoundMeasure L (by omega)
        (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
          (by omega)) := by
  dsimp only
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv
  let hsurj :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  rw [L.horizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
    (by omega) inst hP hconv]
  rw [D.verticalSpinFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
    L (by omega) hsurj]
  rw [L.periodizedVerticalSpinFiberHaarBoundRightHaarScalar_eq_horizontal_of_lattice
    hr inst hP hconv]

/-- The literal horizontal and vertical compact-unit crossed cutoffs agree
for every lattice rank written as `r + 2`. -/
theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_unitCrossedCutoff_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    let V := L.rationalQuadraticSpaceMatrix
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    D.horizontalCrossedLogCutoffLIntegral V
        (L.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
          (by omega))
        rationalIdeleClassUnitLogCutoff =
      D.verticalCrossedLogCutoffLIntegral V
        (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
          (by omega))
        rationalIdeleClassUnitLogCutoff := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv
  let hHorizontal :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  let hVertical :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  let f : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
    fun z => rationalIdeleClassUnitLogCutoff
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
  have hmeasure :=
    L.horizontalRawSOFiberHaarBoundMeasure_eq_verticalSpinFiberHaarBoundMeasure_of_lattice
      hr inst hP hconv
  have hintegral := congrArg (fun μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient =>
    ∫⁻ z, f z ∂μ) hmeasure
  calc
    D.horizontalCrossedLogCutoffLIntegral V hHorizontal
          rationalIdeleClassUnitLogCutoff =
        ∫⁻ z, f z ∂L.horizontalRawSOFiberHaarBoundMeasure inst D := by
      symm
      simpa only [V, D, f, hHorizontal] using
        L.horizontalRawSOFiberHaarBoundMeasure_lintegral_logCutoff inst D
          rationalIdeleClassUnitLogCutoff measurable_rationalIdeleClassUnitLogCutoff
    _ = ∫⁻ z, f z ∂D.verticalSpinFiberHaarBoundMeasure L (by omega) hVertical := by
      simpa only [V, D, f, hVertical] using hintegral
    _ = D.verticalCrossedLogCutoffLIntegral V hVertical
          rationalIdeleClassUnitLogCutoff := by
      simpa only [V, D, f, hVertical] using
        D.verticalSpinFiberHaarBoundMeasure_lintegral_logCutoff L (by omega)
          hVertical rationalIdeleClassUnitLogCutoff
          measurable_rationalIdeleClassUnitLogCutoff

/-- The exact lattice raw datum satisfies the intrinsic Spin--SO relative
Tamagawa comparison in every rank at least three. -/
theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).IsOnoRelativeTamagawaComparison := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  apply
    L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison_of_unitCrossedCutoff_eq
      hn inst hP hconv
  simpa only using
    L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_unitCrossedCutoff_eq
      (r := r) (by omega) inst hP hconv

end PositiveDefiniteIntegralLattice

end
