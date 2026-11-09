import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOneShellCutoff
import SMSFormula.RationalCliffordGeneralSpinRelativeUnitCutoff

/-!
# Calibrating the weighted one-shell theta orbit

The rational periodization of the weighted one-shell quotient measure is
already the retained vertical scalar times the complete weighted rational
shell-coset kernel.  This file packages the latter bind as the ambient
theta-orbit measure and upgrades that integral identity to an equality
of measures on the block full-adelic `GSpin` carrier.

For the lattice raw datum, the horizontal--vertical
periodization calibration replaces the vertical scalar by the concrete
horizontal scalar.  The complete theta coset sum remains inside the ambient
measure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Rational-diagonal periodization is injective on measures on the existing
left quotient.  Restriction to the fixed exact fundamental domain recovers
the section lift, and mapping that lift back to the quotient recovers the
original measure. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_injective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Injective V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift := by
  intro μ ν hμν
  have hrestrict := congrArg
    (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup =>
      ρ.restrict V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain)
    hμν
  change
    (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ).restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift ν).restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain at hrestrict
  rw [V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift,
    V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift] at hrestrict
  have hmap := congrArg
    (Measure.map V.fullAdelicCliffordGeneralSpinLeftQuotientMap) hrestrict
  rw [V.map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift,
    V.map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift] at hmap
  exact hmap

noncomputable local instance oneShellCalibrationTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance oneShellCalibrationTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The complete weighted theta-orbit measure on the block ambient
`GSpin` carrier.  Its kernel includes every rational shell-coset summand. -/
noncomputable def fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞) :
    Measure ((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :=
  ((W.fullAdelicNonisotropicLastShellMeasure a ha).withDensity phi).bind
    (W.fullAdelicNonisotropicLastShellRawCosetSumKernel a ha)

/-- Periodization of the weighted crossed quotient measure is exactly the
retained vertical scalar times the complete weighted theta-orbit measure. -/
theorem
    periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_smul_weightedRawCosetSum
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
          L hn a ha D hsurj phi) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        W.fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
          a ha phi := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let q := D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj
  let rho := W.fullAdelicNonisotropicLastShellRawCosetSumKernel a ha
  let muX := W.fullAdelicNonisotropicLastShellMeasure a ha
  dsimp only
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_smul_measure]
  rw [fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure]
  rw [Measure.lintegral_bind rho.aemeasurable hF.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul muX hphi hF.lintegral_kernel]
  rw [lintegral_periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
    L hn a ha D hsurj phi hphi F hF]
  simp only [W, rho, muX, Pi.mul_apply, smul_eq_mul]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

noncomputable local instance oneShellCalibrationLatticeTargetMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance oneShellCalibrationLatticeTargetBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- For the actual lattice raw datum, the weighted one-shell periodization is
the concrete horizontal scalar times the complete weighted theta-orbit
measure.  This is the authorized horizontal--vertical calibration on the
common block ambient carrier; it performs no cancellation. -/
theorem
    periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_horizontal_smul_weightedRawCosetSum_of_lattice
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
          L (by omega) a ha D
            (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
              (by omega)) phi) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          (by omega) inst hP hconv •
        W.fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
          a ha phi := by
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let hsurj :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  dsimp only
  rw [periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_smul_weightedRawCosetSum
    L (by omega) a ha D hsurj phi hphi]
  rw [L.periodizedVerticalSpinFiberHaarBoundRightHaarScalar_eq_horizontal_of_lattice
    hr inst hP hconv]

/-- Any target quotient cutoff whose periodization is the calibrated
horizontal scalar times the complete weighted theta-orbit measure is exactly
the weighted one-shell quotient measure.  Thus the remaining target-rank
seam is only the displayed periodization identity; no representative or
additional quotient normalization can intervene. -/
theorem
    fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_of_periodized_eq_horizontal_smul_weightedRawCosetSum
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (targetCutoff : Measure
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinLeftQuotient))
    (htarget :
      let W := L.rationalQuadraticSpaceMatrix
      let V := W.nonisotropicLastExtension a ha
      V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift targetCutoff =
        L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
            (by omega) inst hP hconv •
          W.fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
            a ha phi) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    targetCutoff =
      fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
        L (by omega) a ha D
          (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
            (by omega)) phi := by
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  apply V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_injective
  calc
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift targetCutoff =
        L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
            (by omega) inst hP hconv •
          W.fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
            a ha phi := htarget
    _ = V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
          L (by omega) a ha D
            (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
              (by omega)) phi) :=
      (L.periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_horizontal_smul_weightedRawCosetSum_of_lattice
        hr inst hP hconv a ha phi hphi).symm

end PositiveDefiniteIntegralLattice

end
