import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalAssembly
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOuterCarrierRestriction
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedBaseOuterCylinderOrder
import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientHaar
import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberHaarScale

/-!
# Restrict the periodized vertical lift to the retained identity cylinder

The ambient positive-idèle orbital assembly is unrestricted.  This file first
inserts the measurable identity-carrier indicator, then uses the
outer carrier measure equality to replace the full orbital bind by its
retained-base restriction.  The retained-cylinder endpoint then evaluates the
result.  No representative or additional normalization coefficient occurs.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance retainedPeriodizedRestrictionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedPeriodizedRestrictionFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance retainedPeriodizedRestrictionFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance retainedPeriodizedRestrictionFiniteAdeleT2 :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance retainedPeriodizedRestrictionInfiniteAdeleT2 :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance retainedPeriodizedRestrictionAdeleT2 : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

local instance retainedPeriodizedRestrictionFullGSpinT2
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    T2Space L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinIntrinsicPointT2Space RationalAdele

/-- Global periodized form of `(V)` on the certified identity carrier.  Its
coefficient is exactly the idèle-class/differential-Weil conversion times the
unique raw retained Spin-block coefficient. -/
theorem
    lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_restrict_identityChart_eq_conversion_mul_block_mul_horizontalCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
    let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
    (∫⁻ x, f x
        ∂(V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L (by omega) hsurj)).restrict C) =
      (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        (c * ∫⁻ x, f x
          ∂L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
            S) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let A := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialRetainedBaseCarrier B
  let κ := L.positiveSpinOrbitalKernel hr D
  let η := L.positiveSpinOrbitalKernelRestrictIdentityChart hr D S
  let μ := RationalQuadraticSpaceMatrix.positiveRationalIdeleDifferentialHaarMeasure
  let ξ :=
    L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S
  let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
  have hC : MeasurableSet C :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  have hbind : (κ ∘ₘ μ).restrict C = η ∘ₘ μ.restrict A := by
    simpa only [V, E, B, C, A, κ, η, μ] using
      L.positiveSpinOrbitalKernel_comp_positiveHaar_restrict_identityChart_eq_comp_restrict_retainedBaseCarrier
        hr D S
  rw [← lintegral_indicator hC f]
  rw [D.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveSpinOrbital
    L hr hsurj (C.indicator f) (hf.indicator hC)]
  refine congrArg
    (fun t : ENNReal =>
      (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) * t) ?_
  calc
    (∫⁻ a, ∫⁻ x, C.indicator f x ∂κ a ∂μ) =
        ∫⁻ x, C.indicator f x ∂(κ ∘ₘ μ) := by
      simpa only [Function.comp_apply] using
        (Measure.lintegral_bind (m := μ) (μ := κ) κ.aemeasurable
          ((hf.indicator hC).aemeasurable)).symm
    _ = ∫⁻ x, f x ∂(κ ∘ₘ μ).restrict C :=
      lintegral_indicator hC f
    _ = ∫⁻ x, f x ∂(η ∘ₘ μ.restrict A) := by rw [hbind]
    _ = ∫⁻ a, ∫⁻ x, f x ∂η a ∂μ.restrict A := by
      simpa only [Function.comp_apply] using
        Measure.lintegral_bind (m := μ.restrict A) (μ := η) η.aemeasurable
          hf.aemeasurable
    _ = c * ∫⁻ x, f x ∂ξ := by
      simpa only [V, E, B, A, η, μ, ξ, c] using
        L.lintegral_positiveSpinOrbitalKernelRestrictIdentityChart_retainedBase_eq_block_mul_horizontalCylinder
          hr D S f hf

/-- Measure form of the global retained-cylinder comparison. -/
theorem
    periodizedVerticalSpinFiberHaarBoundMeasure_restrict_identityChart_eq_conversion_mul_block_smul_horizontalCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
    let c : ℝ≥0∞ :=
      (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ((D.spinFiniteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B)
    (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L (by omega) hsurj)).restrict C =
      c • L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure
        S := by
  dsimp only
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_smul_measure]
  rw [L.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_restrict_identityChart_eq_conversion_mul_block_mul_horizontalCylinder
    hr D hsurj S f hf]
  simp only [smul_eq_mul, mul_assoc]

/-- The vertical ambient-Haar scalar is determined by the horizontal
differential-cylinder scale and the retained raw block. -/
theorem
    horizontalCylinderScale_mul_periodizedVerticalSpinFiberHaarBoundRightHaarScalar_eq_conversion_mul_block
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S *
        D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L (by omega) hsurj =
      (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ((D.spinFiniteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let C := V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E
  let μp := V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (D.verticalSpinFiberHaarBoundMeasure L (by omega) hsurj)
  let ν := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let ξ :=
    L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S
  let d : ℝ≥0∞ :=
    L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale S
  let q : ℝ≥0∞ :=
    D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L (by omega) hsurj
  let a : ℝ≥0∞ :=
    (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
      ((D.spinFiniteScale : ℝ≥0∞) *
        V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B)
  letI : Measure.IsHaarMeasure ν :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  have hp := D.periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_horizontal
    L (by omega) hsurj
  have hpC : μp.restrict C = q • ν.restrict C := by
    have := congrArg (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ.restrict C) hp
    simpa only [μp, q, ν, Measure.restrict_smul] using this
  have hr :=
    L.periodizedVerticalSpinFiberHaarBoundMeasure_restrict_identityChart_eq_conversion_mul_block_smul_horizontalCylinder
      hr D hsurj S
  have hretained : μp.restrict C = a • ξ := by
    simpa only [V, E, B, C, μp, ξ, a] using hr
  have hcylinder : d • ξ = ν.restrict C := by
    simpa only [V, E, C, d, ξ, ν] using
      L.cliffordGeneralSpinHorizontalDifferentialCylinderScale_smul_fullAdelicCylinderMeasure_eq_haar_restrict
        S
  have hmeasure : (d * q) • ν.restrict C = a • ν.restrict C := by
    calc
      (d * q) • ν.restrict C = d • (q • ν.restrict C) := by rw [smul_smul]
      _ = d • μp.restrict C := by rw [hpC]
      _ = d • (a • ξ) := by rw [hretained]
      _ = a • (d • ξ) := by simp only [smul_smul, mul_comm]
      _ = a • ν.restrict C := by rw [hcylinder]
  obtain ⟨K, hK, hKint, hKC⟩ :=
    L.exists_compact_nonemptyInterior_subset_identityChart S
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hmass := congrArg (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ K) hmeasure
  have hν0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν hKint).ne'
  have hνtop : ν K ≠ ∞ := hK.measure_ne_top
  have hcancel : (d * q) * ν K = a * ν K := by
    change ((d * q) • ν.restrict C) K = (a • ν.restrict C) K at hmass
    rw [Measure.smul_apply, Measure.restrict_apply hKmeas,
      Measure.smul_apply, Measure.restrict_apply hKmeas] at hmass
    rw [Set.inter_eq_left.mpr hKC] at hmass
    simpa only [ENNReal.smul_def, smul_eq_mul] using hmass
  apply (ENNReal.mul_right_inj hν0 hνtop).mp
  simpa only [mul_comm] using hcancel

end PositiveDefiniteIntegralLattice

end
