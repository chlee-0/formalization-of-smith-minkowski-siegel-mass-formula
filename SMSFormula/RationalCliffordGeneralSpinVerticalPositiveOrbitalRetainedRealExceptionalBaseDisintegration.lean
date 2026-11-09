import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailSimilitudeDisintegration
import SMSFormula.RationalRealUnitSquareBranchChangeOfVariables

/-!
# Disintegrate the retained real and exceptional idelic base

The good integral tail has already been disintegrated through the normalized
`SO` central fiber.  This file treats the complementary exposed coordinates.
On each chosen square branch, ambient differential Haar maps under squaring
with the inverse local square modulus.  The real inverse modulus and the
finite exceptional inverse modulus multiply to one because the retained set
contains the dyadic place.

The result is stated on the square source and target subtypes.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedRealExceptionalBaseDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedRealExceptionalBasePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

private theorem smul_measure_injective_of_ne_zero_ne_top
    {α : Type*} [MeasurableSpace α] {c : ℝ≥0∞} {μ ν : Measure α}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (h : c • μ = c • ν) : μ = ν := by
  ext s hs
  have h' := congrArg (fun m : Measure α => m s) h
  change c * μ s = c * ν s at h'
  apply (ENNReal.mul_left_inj hc0 hct).mp
  simpa only [mul_comm] using h'

/-- On the retained real branch, squaring ambient differential Haar gives
the target restriction with the inverse real square modulus. -/
theorem map_realUnitSquareIdentityChartAmbientSourceMeasure_sq :
    Measure.map
        (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
        realUnitSquareIdentityChartAmbientSourceMeasure =
      ((rationalIdeleRealSquareModulus : ℝ≥0∞)⁻¹) •
        realUnitSquareIdentityChartTargetMeasure := by
  let chart := Rat.unitSquareIdentityChart ℝ
  let c : ℝ≥0∞ := rationalIdeleRealSquareModulus
  let μ := realUnitSquareIdentityChartAmbientSourceMeasure
  let ν := realUnitSquareIdentityChartTargetMeasure
  have hc0 : c ≠ 0 := by simp [c]
  have hct : c ≠ ⊤ := by simp [c]
  have hbranch : realUnitSquareIdentityChartSourceMeasure = c • μ := by
    simpa only [c, μ] using realUnitSquareBranchChangeOfVariables
  have hmap : ν = c • Measure.map chart.toHomeomorphSourceTarget μ := by
    calc
      ν = Measure.map chart.toHomeomorphSourceTarget
          realUnitSquareIdentityChartSourceMeasure :=
        map_realUnitSquareIdentityChartSourceMeasure.symm
      _ = Measure.map chart.toHomeomorphSourceTarget (c • μ) := by rw [hbranch]
      _ = c • Measure.map chart.toHomeomorphSourceTarget μ := by
        rw [Measure.map_smul]
  apply smul_measure_injective_of_ne_zero_ne_top hc0 hct
  calc
    c • Measure.map chart.toHomeomorphSourceTarget μ = ν := hmap.symm
    _ = c • (c⁻¹ • ν) := by
      rw [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]

/-- Differential Haar restricted to the local square target. -/
def padicUnitSquareIdentityChartDifferentialTargetMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).target :=
  Measure.comap Subtype.val (rationalPadicIdeleDifferentialHaarMeasure v)

private theorem rationalIdeleFinitePlaceSquareModulus_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalIdeleFinitePlaceSquareModulus v ≠ 0 := by
  by_cases hv : v = rationalIdeleDyadicPlace
  · subst v
    rw [rationalIdeleFinitePlaceSquareModulus_dyadic]
    norm_num
  · rw [rationalIdeleFinitePlaceSquareModulus_eq_one_of_ne_dyadic v hv]
    norm_num

/-- At every retained finite place, squaring ambient differential Haar gives
the local differential target restriction with the inverse p-adic square
modulus. -/
theorem map_padicUnitSquareIdentityChartAmbientSourceMeasure_sq
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let p := (Rat.HeightOneSpectrum.primesEquiv v).1
    Measure.map
        (Rat.unitSquareIdentityChart ℚ_[p]).toHomeomorphSourceTarget
        (padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v) =
      ((rationalIdeleFinitePlaceSquareModulus v : ℝ≥0∞)⁻¹) •
        padicUnitSquareIdentityChartDifferentialTargetMeasure v := by
  dsimp only
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let chart := Rat.unitSquareIdentityChart ℚ_[p]
  let c : ℝ≥0∞ := rationalIdeleFinitePlaceSquareModulus v
  let μMath := padicUnitSquareIdentityChartAmbientSourceMeasure p
  let νMath := padicUnitSquareIdentityChartTargetMeasure p
  let μ := padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v
  let ν := padicUnitSquareIdentityChartDifferentialTargetMeasure v
  let k : ℝ≥0∞ := rationalPadicMathlibHaarToDifferentialScalar v
  have hc0 : c ≠ 0 := by
    by_cases hv : v = rationalIdeleDyadicPlace
    · subst v
      simp [c]
    · simp [c, rationalIdeleFinitePlaceSquareModulus_eq_one_of_ne_dyadic _ hv]
  have hct : c ≠ ⊤ := by simp [c]
  have hk0 : k ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr
      (rationalPadicMathlibHaarToDifferentialScalar_ne_zero v)
  have hkt : k ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hbranch : padicUnitSquareIdentityChartSourceMeasure p = c • μMath := by
    simpa only [c, μMath, rationalIdeleFinitePlaceSquareModulus] using
      (padicUnitSquareBranchChangeOfVariables p)
  have hmapMath : Measure.map chart.toHomeomorphSourceTarget μMath = c⁻¹ • νMath := by
    have hmap : νMath = c • Measure.map chart.toHomeomorphSourceTarget μMath := by
      calc
        νMath = Measure.map chart.toHomeomorphSourceTarget
            (padicUnitSquareIdentityChartSourceMeasure p) :=
          map_padicUnitSquareIdentityChartSourceMeasure p |>.symm
        _ = Measure.map chart.toHomeomorphSourceTarget (c • μMath) := by rw [hbranch]
        _ = c • Measure.map chart.toHomeomorphSourceTarget μMath := by
          rw [Measure.map_smul]
    apply smul_measure_injective_of_ne_zero_ne_top hc0 hct
    calc
      c • Measure.map chart.toHomeomorphSourceTarget μMath = νMath := hmap.symm
      _ = c • (c⁻¹ • νMath) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
  have hsource : μMath = k • μ :=
    padicUnitSquareIdentityChartAmbientSourceMeasure_eq_smul_differential v
  have htarget : νMath = k • ν := by
    unfold νMath ν padicUnitSquareIdentityChartTargetMeasure
      padicUnitSquareIdentityChartDifferentialTargetMeasure
    rw [rationalPadicMathlibHaar_eq_smul_differentialHaar v]
    change Measure.comap Subtype.val
        ((rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) •
          rationalPadicIdeleDifferentialHaarMeasure v) =
      (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) •
        Measure.comap Subtype.val (rationalPadicIdeleDifferentialHaarMeasure v)
    rw [Measure.comap_smul]
  apply smul_measure_injective_of_ne_zero_ne_top hk0 hkt
  calc
    k • Measure.map chart.toHomeomorphSourceTarget μ =
        Measure.map chart.toHomeomorphSourceTarget μMath := by
      rw [hsource, Measure.map_smul]
    _ = c⁻¹ • νMath := hmapMath
    _ = k • (c⁻¹ • ν) := by rw [htarget, smul_smul, smul_smul, mul_comm k]

/-- Product of the local square targets over the retained finite
exceptional set. -/
abbrev RationalIdeleDifferentialExceptionalSquareChartTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).target

/-- Product of restricted differential Haar on the local square targets. -/
def rationalIdeleDifferentialExceptionalSquareChartTargetMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialExceptionalSquareChartTarget S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialTargetMeasure v.1

/-- Apply the local square homeomorphism at every retained
exceptional place. -/
def rationalIdeleDifferentialExceptionalSquareChartToTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialExceptionalSquareChartSource S →
      RationalIdeleDifferentialExceptionalSquareChartTarget S :=
  fun a v =>
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).toHomeomorphSourceTarget (a v)

theorem measurable_rationalIdeleDifferentialExceptionalSquareChartToTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (rationalIdeleDifferentialExceptionalSquareChartToTarget S) :=
  measurable_pi_lambda _ fun v =>
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).toHomeomorphSourceTarget.measurable.comp
        (measurable_pi_apply v)

/-- The finite exceptional square map has precisely the inverse product of
the exposed local square moduli. -/
theorem map_rationalIdeleDifferentialExceptionalSquareChartToTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIdeleDifferentialExceptionalSquareChartToTarget S)
        (rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S) =
      ((rationalIdeleFiniteExceptionalSquareModulus S : ℝ≥0∞)⁻¹) •
        rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S := by
  let f := fun v : {v // v ∈ S} =>
    (Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).toHomeomorphSourceTarget
  let μ := fun v : {v // v ∈ S} =>
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1
  let ν := fun v : {v // v ∈ S} =>
    padicUnitSquareIdentityChartDifferentialTargetMeasure v.1
  have hlocal (v : {v // v ∈ S}) :
      Measure.map (f v) (μ v) =
        ((rationalIdeleFinitePlaceSquareModulus v.1 : ℝ≥0∞)⁻¹) • ν v :=
    map_padicUnitSquareIdentityChartAmbientSourceMeasure_sq v.1
  letI (v : {v // v ∈ S}) : SigmaFinite (ν v) := by
    unfold ν padicUnitSquareIdentityChartDifferentialTargetMeasure
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet]
    infer_instance
  letI (v : {v // v ∈ S}) : SigmaFinite (Measure.map (f v) (μ v)) := by
    letI : SigmaFinite (μ v) := by
      unfold μ padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [map_comap_subtype_coe
        (Rat.unitSquareIdentityChart
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_source.measurableSet]
      infer_instance
    exact
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).toHomeomorphSourceTarget
          |>.toMeasurableEquiv.sigmaFinite_map
  have hpi :
      Measure.map (fun a v => f v (a v)) (Measure.pi μ) =
        Measure.pi fun v => Measure.map (f v) (μ v) :=
    Measure.pi_map_pi fun v => (f v).measurable.aemeasurable
  change
    Measure.map (fun a v => f v (a v)) (Measure.pi μ) =
      ((rationalIdeleFiniteExceptionalSquareModulus S : ℝ≥0∞)⁻¹) • Measure.pi ν
  rw [hpi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi _ s]
  simp_rw [hlocal]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [show
    (rationalIdeleFiniteExceptionalSquareModulus S : ℝ≥0∞)⁻¹ =
        ∏ v : {v // v ∈ S},
          (rationalIdeleFinitePlaceSquareModulus v.1 : ℝ≥0∞)⁻¹ by
      simp only [rationalIdeleFiniteExceptionalSquareModulus]
      calc
        ((↑(∏ a ∈ S, rationalIdeleFinitePlaceSquareModulus a) : ℝ≥0∞))⁻¹ =
            ↑((∏ a ∈ S, rationalIdeleFinitePlaceSquareModulus a)⁻¹) :=
          (ENNReal.coe_inv (Finset.prod_ne_zero_iff.mpr fun v _ =>
            rationalIdeleFinitePlaceSquareModulus_ne_zero v)).symm
        _ = ↑(∏ v : {v // v ∈ S},
              (rationalIdeleFinitePlaceSquareModulus v.1)⁻¹) := by
          rw [Finset.prod_inv_distrib]
          rw [Finset.prod_subtype S (fun _ => Iff.rfl)
            rationalIdeleFinitePlaceSquareModulus]
        _ = ∏ v : {v // v ∈ S},
              (rationalIdeleFinitePlaceSquareModulus v.1 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.coe_finset_prod]
          apply Finset.prod_congr rfl
          intro v hv
          exact ENNReal.coe_inv
            (rationalIdeleFinitePlaceSquareModulus_ne_zero v.1)
    ]
  exact Finset.prod_mul_distrib.symm

/-- Real and retained exceptional square changes of variables have total
coefficient one.  This is the exposed base disintegration complementary to
the normalized good-tail theorem. -/
theorem map_retainedRealExceptionalSquareChartToTarget
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : rationalIdeleDyadicPlace ∈ S) :
    Measure.map
        (Prod.map
          (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
          (rationalIdeleDifferentialExceptionalSquareChartToTarget S))
        (realUnitSquareIdentityChartAmbientSourceMeasure.prod
          (rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S)) =
      realUnitSquareIdentityChartTargetMeasure.prod
        (rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S) := by
  let cR : ℝ≥0∞ := rationalIdeleRealSquareModulus
  let cE : ℝ≥0∞ := rationalIdeleFiniteExceptionalSquareModulus S
  let μR := realUnitSquareIdentityChartAmbientSourceMeasure
  let μE := rationalIdeleDifferentialExceptionalSquareChartSourceMeasure S
  let νR := realUnitSquareIdentityChartTargetMeasure
  let νE := rationalIdeleDifferentialExceptionalSquareChartTargetMeasure S
  have hR : Measure.map
      (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget μR = cR⁻¹ • νR :=
    map_realUnitSquareIdentityChartAmbientSourceMeasure_sq
  have hE : Measure.map
      (rationalIdeleDifferentialExceptionalSquareChartToTarget S) μE = cE⁻¹ • νE :=
    map_rationalIdeleDifferentialExceptionalSquareChartToTarget S
  have hc : cR⁻¹ * cE⁻¹ = 1 := by
    have hcprod : cR * cE = 1 := by
      dsimp only [cR, cE]
      exact_mod_cast
        rationalIdeleReal_mul_finiteExceptionalSquareModulus_eq_one S hS
    have hcR0 : cR ≠ 0 := by
      dsimp only [cR]
      exact ENNReal.coe_ne_zero.mpr (by
        rw [rationalIdeleRealSquareModulus_eq_two]
        norm_num)
    have hcRtop : cR ≠ ⊤ := by
      dsimp only [cR]
      exact ENNReal.coe_ne_top
    have hcE : cE = cR⁻¹ := by
      apply (ENNReal.mul_left_inj hcR0 hcRtop).mp
      calc
        cE * cR = cR * cE := mul_comm _ _
        _ = 1 := hcprod
        _ = cR⁻¹ * cR := (ENNReal.inv_mul_cancel hcR0 hcRtop).symm
    rw [hcE, inv_inv, ENNReal.inv_mul_cancel hcR0 hcRtop]
  letI : SigmaFinite μR := by
    unfold μR realUnitSquareIdentityChartAmbientSourceMeasure
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  letI : SigmaFinite μE := by
    unfold μE
    infer_instance
  letI : SigmaFinite νR := by
    unfold νR realUnitSquareIdentityChartTargetMeasure
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart ℝ).open_target.measurableSet]
    infer_instance
  letI : SigmaFinite νE := by
    unfold νE rationalIdeleDifferentialExceptionalSquareChartTargetMeasure
    letI (v : {v // v ∈ S}) : SigmaFinite
        (padicUnitSquareIdentityChartDifferentialTargetMeasure v.1) := by
      unfold padicUnitSquareIdentityChartDifferentialTargetMeasure
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [map_comap_subtype_coe
        (Rat.unitSquareIdentityChart
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_target.measurableSet]
      infer_instance
    infer_instance
  calc
    Measure.map
        (Prod.map
          (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
          (rationalIdeleDifferentialExceptionalSquareChartToTarget S))
        (μR.prod μE) =
        (Measure.map (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget μR).prod
          (Measure.map (rationalIdeleDifferentialExceptionalSquareChartToTarget S) μE) :=
      (Measure.map_prod_map μR μE
        (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.measurable
        (measurable_rationalIdeleDifferentialExceptionalSquareChartToTarget S)).symm
    _ = (cR⁻¹ • νR).prod (cE⁻¹ • νE) := by rw [hR, hE]
    _ = (cR⁻¹ * cE⁻¹) • (νR.prod νE) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = νR.prod νE := by rw [hc, one_smul]

end RationalQuadraticSpaceMatrix

end
