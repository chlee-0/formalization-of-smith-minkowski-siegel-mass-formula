import SMSFormula.RationalCliffordGeneralSpinCrossedCutoffExtraction
import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientBind

/-!
# Sigma-finiteness of the concrete horizontal GSpin quotient bind

The logarithmic module gives a countable exhaustion of the rational adelic
`GSpin` quotient.  On each bounded logarithmic strip, the concrete raw-`SO`
fiber-Haar bind has finite mass: the horizontal crossed formula separates it
as the finite raw `SO` quotient mass times a compact real logarithmic cutoff.

This supplies the sigma-finiteness hypothesis needed to periodize the concrete
bind back to ambient adelic `GSpin`.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix
open Set
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The bounded logarithmic strips used to exhaust the rational adelic
`GSpin` quotient. -/
def horizontalRawSOFiberHaarBoundSpanningSet
    (L : PositiveDefiniteIntegralLattice (r + 2)) (m : ℕ) :
    Set L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule ⁻¹'
    Set.Icc (-(m : ℝ)) (m : ℝ)

theorem measurableSet_horizontalRawSOFiberHaarBoundSpanningSet
    (L : PositiveDefiniteIntegralLattice (r + 2)) (m : ℕ) :
    MeasurableSet (L.horizontalRawSOFiberHaarBoundSpanningSet m) := by
  exact measurableSet_Icc.preimage
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable

/-- The bounded logarithmic strips cover the entire quotient. -/
theorem iUnion_horizontalRawSOFiberHaarBoundSpanningSet
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    ⋃ m : ℕ, L.horizontalRawSOFiberHaarBoundSpanningSet m = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨m, hm⟩ := exists_nat_ge
    |L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z|
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  constructor <;> linarith [le_abs_self
    (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z),
    neg_abs_le
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)]

/-- Indicator cutoff of one bounded logarithmic strip. -/
def horizontalRawSOFiberHaarBoundLogCutoff (m : ℕ) : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => 1)

theorem measurable_horizontalRawSOFiberHaarBoundLogCutoff (m : ℕ) :
    Measurable (horizontalRawSOFiberHaarBoundLogCutoff m) := by
  exact measurable_const.indicator measurableSet_Icc

theorem lintegral_horizontalRawSOFiberHaarBoundLogCutoff_ne_top (m : ℕ) :
    (∫⁻ t : ℝ, horizontalRawSOFiberHaarBoundLogCutoff m t) ≠ ⊤ := by
  rw [show horizontalRawSOFiberHaarBoundLogCutoff m =
      Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ))
        (fun _ : ℝ => (1 : ℝ≥0∞)) by rfl,
    lintegral_indicator measurableSet_Icc]
  simp

/-- Every bounded logarithmic strip has finite mass in the actual lattice
raw-`SO` fiber-Haar bind. -/
theorem horizontalRawSOFiberHaarBoundSpanningSet_measure_lt_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (m : ℕ) :
    L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv)
        (L.horizontalRawSOFiberHaarBoundSpanningSet m) < ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L hn inst hP hconv
  let f := horizontalRawSOFiberHaarBoundLogCutoff m
  have hf : Measurable f := measurable_horizontalRawSOFiberHaarBoundLogCutoff m
  have hcertificate :=
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate.of_massLocalInverseProductTendsTo
      L inst hP hconv
  have hSOtop : D.specialOrthogonalData.tamagawaNumberENNReal ≠ ⊤ := by
    change
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal ≠ ⊤
    exact hcertificate.tamagawaNumberENNReal_ne_top
  have hreal : (∫⁻ t : ℝ, f t) ≠ ⊤ :=
    lintegral_horizontalRawSOFiberHaarBoundLogCutoff_ne_top m
  have hidele : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤ := by
    rw [rationalIdeleClassLogCutoffLIntegral_eq_real f hf]
    exact ENNReal.mul_ne_top rationalIdeleClassLogHaarScalar_ne_top hreal
  have hhalf : (2 : ℝ≥0∞)⁻¹ * rationalIdeleClassLogCutoffLIntegral f ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hidele
  have hcrossed :
      D.horizontalCrossedLogCutoffLIntegral V
          (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
          f ≠ ⊤ := by
    rw [D.horizontalCrossedLogCutoffLIntegral_eq V
      (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
      f hf,
      V.horizontalFiberLogCutoffLIntegral_one f hf]
    change rationalIdeleClassLogCutoffLIntegral (fun t => f (2 * t)) *
        D.specialOrthogonalData.tamagawaNumberENNReal ≠ ⊤
    rw [rationalIdeleClassLogCutoffLIntegral_two_mul f hf]
    exact ENNReal.mul_ne_top hhalf hSOtop
  have hmeasure :
      L.horizontalRawSOFiberHaarBoundMeasure inst D
          (L.horizontalRawSOFiberHaarBoundSpanningSet m) =
        ∫⁻ z, f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z) ∂
            L.horizontalRawSOFiberHaarBoundMeasure inst D := by
    rw [← setLIntegral_one]
    rw [← lintegral_indicator
      (L.measurableSet_horizontalRawSOFiberHaarBoundSpanningSet m)]
    apply lintegral_congr
    intro z
    change
      (L.horizontalRawSOFiberHaarBoundSpanningSet m).indicator
          (fun _ => (1 : ℝ≥0∞)) z =
        f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
    by_cases hz :
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z ∈
          Set.Icc (-(m : ℝ)) (m : ℝ)
    · rw [Set.indicator_of_mem]
      · dsimp [f, V, horizontalRawSOFiberHaarBoundLogCutoff]
        rw [Set.indicator_of_mem hz]
      · exact hz
    · rw [Set.indicator_of_notMem]
      · dsimp [f, V, horizontalRawSOFiberHaarBoundLogCutoff]
        rw [Set.indicator_of_notMem hz]
      · exact hz
  rw [hmeasure,
    L.horizontalRawSOFiberHaarBoundMeasure_lintegral_logCutoff inst D f hf]
  exact hcrossed.lt_top

/-- The concrete lattice raw-`SO` fiber-Haar bind is nonzero.  The unit
logarithmic cutoff detects it as the product of three literal nonzero factors:
the inverse-two squaring modulus, the rational idele-class cutoff mass, and
the certified raw `SO` quotient mass. -/
theorem horizontalRawSOFiberHaarBoundMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv) ≠ 0 := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L hn inst hP hconv
  let f := rationalIdeleClassUnitLogCutoff
  have hf : Measurable f := measurable_rationalIdeleClassUnitLogCutoff
  have hcertificate :=
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate.of_massLocalInverseProductTendsTo
      L inst hP hconv
  have hSOzero : D.specialOrthogonalData.tamagawaNumberENNReal ≠ 0 := by
    change
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal ≠ 0
    exact hcertificate.tamagawaNumberENNReal_ne_zero
  intro hzero
  have hintegral :
      ∫⁻ z, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z) ∂
          L.horizontalRawSOFiberHaarBoundMeasure inst D = 0 := by
    rw [hzero]
    simp
  rw [L.horizontalRawSOFiberHaarBoundMeasure_lintegral_logCutoff inst D f hf,
    D.horizontalCrossedLogCutoffLIntegral_eq V
      (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
      f hf,
    V.horizontalFiberLogCutoffLIntegral_one f hf] at hintegral
  change rationalIdeleClassLogCutoffLIntegral (fun t => f (2 * t)) *
      D.specialOrthogonalData.tamagawaNumberENNReal = 0 at hintegral
  rw [rationalIdeleClassLogCutoffLIntegral_two_mul f hf] at hintegral
  exact (mul_ne_zero
    (mul_ne_zero (by norm_num)
      rationalIdeleClassLogCutoffLIntegral_unit_ne_zero)
    hSOzero) hintegral

/-- The concrete lattice raw-`SO` fiber-Haar bind is sigma-finite. -/
theorem horizontalRawSOFiberHaarBoundMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    SigmaFinite
      (L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv)) := by
  apply Measure.sigmaFinite_of_countable (Set.countable_range
    (fun m : ℕ => L.horizontalRawSOFiberHaarBoundSpanningSet m))
  · intro A hA
    rcases hA with ⟨m, rfl⟩
    exact L.horizontalRawSOFiberHaarBoundSpanningSet_measure_lt_top
      hn inst hP hconv m
  · rw [Set.sUnion_range]
    exact L.iUnion_horizontalRawSOFiberHaarBoundSpanningSet

end PositiveDefiniteIntegralLattice
