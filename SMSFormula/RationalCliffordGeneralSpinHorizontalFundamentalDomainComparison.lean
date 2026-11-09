import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberHaarScale
import SMSFormula.RationalCliffordGeneralSpinHorizontalBoundPeriodizedHaar

/-!
# Horizontal comparison on the exact rational GSpin fundamental domain

The calibrated ambient differential central-fiber bind is already known
globally as an explicit positive finite multiple of fixed horizontal adelic
`GSpin` Haar.  This file packages that literal ambient measure, rather than a
surrogate copy, into measurable-Weil data on the exact rational `GSpin`
quotient.  The quotient measure is consequently the exact pushforward of the
ambient bind restricted to the established measurable fundamental domain.

The lattice-dependent version restores the raw differential `SO` finite-
stabilizer volume as a separate outer scalar.  Independently, restricting the
existing periodized raw `SO`/idele-class horizontal bind to the same exact
fundamental domain identifies that concrete bind with its already certified
common horizontal quotient scale.

No quotient scalar is set to one, no chart infrastructure is introduced, and
no vertical or singular quotient source is compared.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

namespace CliffordGeneralSpinMeasurableWeilMeasureData

/-- Simultaneous rescaling by an arbitrary `ENNReal` preserves the measurable
left Weil identity.  This form is needed for the lattice stabilizer volume. -/
theorem isMeasurableWeilQuotientMeasure_ennreal_smul
    (D : V.CliffordGeneralSpinMeasurableWeilMeasureData)
    (c : ℝ≥0∞) :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (c • D.adelicMeasure) (c • D.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    rw [lintegral_smul_measure, lintegral_smul_measure,
      D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf]

end CliffordGeneralSpinMeasurableWeilMeasureData

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

/-! ## The normalized calibrated ambient quotient -/

/-- Measurable-Weil data whose ambient measure is literally the
carrier-independent normalized differential central-fiber bind. -/
noncomputable def
    fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinMeasurableWeilMeasureData := by
  let V := L.rationalQuadraticSpaceMatrix
  let a := L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S
  exact
    { adelicMeasure :=
        L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure
      quotientMeasure :=
        a •
          V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
      isMeasurableWeilQuotientMeasure := by
        rw [L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure_eq_scalar_smul_horizontal
          S]
        exact
          V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
            |>.isMeasurableWeilQuotientMeasure_smul a }

@[simp]
theorem
    fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData_adelicMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData S
      ).adelicMeasure =
      L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure :=
  rfl

@[simp]
theorem
    fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData_quotientMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData S
      ).quotientMeasure =
      L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure :=
  rfl

/-- The normalized ambient quotient is literally the pushforward of the
normalized ambient bind restricted to the exact rational `GSpin`
fundamental domain. -/
theorem
    fullAdelicInvariantDifferentialCentralFiberQuotientMeasure_eq_fundamentalDomain
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData S
      ).quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        L.fullAdelicInvariantDifferentialCentralFiberBoundMeasure
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  exact
    (L.fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData S
      ).quotientMeasure_eq_fundamentalDomain L.rationalQuadraticSpaceMatrix

/-! ## Restoring the lattice differential scale -/

/-- Measurable-Weil data whose ambient measure is the literal lattice
`P`-dependent differential central-fiber bind.  The finite stabilizer volume
remains a separate outer scalar on the normalized quotient. -/
noncomputable def fullAdelicDifferentialCentralFiberMeasurableWeilData
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinMeasurableWeilMeasureData := by
  let D :=
    L.fullAdelicInvariantDifferentialCentralFiberMeasurableWeilData S
  let t := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  exact
    { adelicMeasure := L.fullAdelicDifferentialCentralFiberBoundMeasure P
      quotientMeasure := t • D.quotientMeasure
      isMeasurableWeilQuotientMeasure := by
        rw [L.fullAdelicDifferentialCentralFiberBoundMeasure_eq_stabilizerVolume_smul
          hP]
        exact D.isMeasurableWeilQuotientMeasure_ennreal_smul
          L.rationalQuadraticSpaceMatrix t }

@[simp]
theorem fullAdelicDifferentialCentralFiberMeasurableWeilData_adelicMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
      ).adelicMeasure =
      L.fullAdelicDifferentialCentralFiberBoundMeasure P :=
  rfl

@[simp]
theorem fullAdelicDifferentialCentralFiberMeasurableWeilData_quotientMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
      ).quotientMeasure =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S •
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure) :=
  rfl

/-- The literal lattice ambient bind restricts to the exact rational `GSpin`
fundamental domain and pushes to its scale-explicit common quotient measure. -/
theorem fullAdelicDifferentialCentralFiberQuotientMeasure_eq_fundamentalDomain
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hP : 0 < P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
      ).quotientMeasure =
      leftQuotientFundamentalDomainMeasure
        L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (L.fullAdelicDifferentialCentralFiberBoundMeasure P)
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  exact
    (L.fullAdelicDifferentialCentralFiberMeasurableWeilData hP S
      ).quotientMeasure_eq_fundamentalDomain L.rationalQuadraticSpaceMatrix

/-! ## Recovering the concrete horizontal bind from its periodization -/

/-- Restriction of the existing periodized raw horizontal bind to the same
exact fundamental domain identifies the concrete quotient bind with the
certified common horizontal quotient measure at its literal positive finite
periodization scalar. -/
theorem horizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          hn inst hP hconv •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := L.horizontalRawSOFiberHaarBoundMeasure inst
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv)
  let c := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    hn inst hP hconv
  let F := V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
  have hperiodized :=
    L.periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontal
      hn inst hP hconv
  have hrestrict :
      (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ).restrict F =
        (c • V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure).restrict F := by
    simpa only [V, μ, c, F] using congrArg
      (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ.restrict F)
      hperiodized
  rw [V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ,
    Measure.restrict_smul] at hrestrict
  have hmap := congrArg
    (Measure.map V.fullAdelicCliffordGeneralSpinLeftQuotientMap) hrestrict
  rw [V.map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift μ,
    Measure.map_smul] at hmap
  rw [V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_quotientMeasure_eq_fundamentalDomain]
  simpa only [leftQuotientFundamentalDomainMeasure_eq_map_restrict] using hmap

end PositiveDefiniteIntegralLattice
