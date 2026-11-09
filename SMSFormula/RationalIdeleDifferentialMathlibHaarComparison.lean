import SMSFormula.RationalCliffordGeneralSpinLocalDifferentialSquareFactor
import SMSFormula.RationalIdeleDifferentialLocalFactor
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Comparing Mathlib's local Haar choice with differential idele Haar

The horizontal `GSpin` identity charts were fixed using Mathlib's opaque
`Measure.haar` on each p-adic multiplicative group.  Differential rational
idele Haar instead uses the Haar measure normalized to give integral units
mass one.  These measures are not definitionally equal.  This file records
their exact positive finite comparison scalar and its finite exceptional-place
product.

This is the normalization conversion exposed by the ambient central-fiber
calibration.  It does not identify the scalar with one, form an Euler product,
or compare idele-class quotient measures.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

local instance differentialMathlibHaarComparisonPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance differentialMathlibHaarComparisonUnitMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance differentialMathlibHaarComparisonUnitBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance differentialMathlibHaarComparisonUnitSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-! ## One finite place -/

/-- Mathlib's selected Haar has finite mass on the integral-unit compact. -/
private theorem rationalPadicMathlibHaar_integralUnits_ne_top
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
  (Measure.haar :
      Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 :
      Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) ≠ ⊤ := by
  let μ := (Measure.haar :
    Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
  letI : Measure.IsHaarMeasure μ := by infer_instance
  exact
    (isCompact_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).measure_lt_top.ne

/-- The literal conversion scalar from Mathlib's opaque local multiplicative
Haar choice to the compact-normalized differential Haar choice. -/
def rationalPadicMathlibHaarToDifferentialScalar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0 :=
  ((Measure.haar :
      Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1 :
      Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)).toNNReal

@[simp]
theorem coe_rationalPadicMathlibHaarToDifferentialScalar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) =
      (Measure.haar :
        Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 :
          Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) := by
  exact ENNReal.coe_toNNReal
    (rationalPadicMathlibHaar_integralUnits_ne_top v)

/-- Mathlib's selected local multiplicative Haar is exactly its integral-unit
mass times differential Haar.  The coefficient is deliberately opaque. -/
theorem rationalPadicMathlibHaar_eq_smul_differentialHaar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (Measure.haar :
        Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) =
      rationalPadicMathlibHaarToDifferentialScalar v •
        rationalPadicIdeleDifferentialHaarMeasure v := by
  let μ := (Measure.haar :
    Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
  letI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  letI : Measure.IsMulLeftInvariant μ := by infer_instance
  change μ = _
  rw [Measure.haarMeasure_unique μ
    (rationalPadicIdeleIntegralPositiveCompacts v)]
  change (Measure.haar :
      Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 :
          Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) •
      Measure.haarMeasure (rationalPadicIdeleIntegralPositiveCompacts v) =
    (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) •
      rationalPadicIdeleDifferentialHaarMeasure v
  rw [← coe_rationalPadicMathlibHaarToDifferentialScalar v]
  rfl

/-- The local conversion scalar is nonzero. -/
theorem rationalPadicMathlibHaarToDifferentialScalar_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalPadicMathlibHaarToDifferentialScalar v ≠ 0 := by
  let μ := (Measure.haar :
    Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
  letI : Measure.IsHaarMeasure μ := by infer_instance
  rw [rationalPadicMathlibHaarToDifferentialScalar,
    ENNReal.toNNReal_ne_zero]
  exact ⟨
    (isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).measure_pos μ
        ⟨1, Subgroup.one_mem _⟩ |>.ne',
    rationalPadicMathlibHaar_integralUnits_ne_top v⟩

/-- Differential local Haar comapped to the chosen square-source branch. -/
def padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).source :=
  Measure.comap Subtype.val (rationalPadicIdeleDifferentialHaarMeasure v)

/-- The square-source measure used in the horizontal chart is the differential
measure scaled by the same opaque local conversion scalar. -/
theorem padicUnitSquareIdentityChartAmbientSourceMeasure_eq_smul_differential
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    padicUnitSquareIdentityChartAmbientSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1 =
      rationalPadicMathlibHaarToDifferentialScalar v •
        padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v := by
  unfold padicUnitSquareIdentityChartAmbientSourceMeasure
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
  rw [rationalPadicMathlibHaar_eq_smul_differentialHaar v]
  change Measure.comap Subtype.val
      ((rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) •
        rationalPadicIdeleDifferentialHaarMeasure v) =
    (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) •
      Measure.comap Subtype.val (rationalPadicIdeleDifferentialHaarMeasure v)
  rw [Measure.comap_smul]

/-! ## Finite exceptional products -/

/-- The finite product of local Mathlib-to-differential Haar conversion
scalars.  This is not an Euler product. -/
def rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  ∏ v : {v // v ∈ S}, rationalPadicMathlibHaarToDifferentialScalar v.1

/-- The finite exceptional conversion scalar is nonzero. -/
theorem rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar S ≠ 0 := by
  unfold rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    rationalPadicMathlibHaarToDifferentialScalar_ne_zero v.1

/-- The finite product of differential local Haar measures restricted to the
same square-source branches used by the horizontal chart. -/
def rationalIdeleFiniteExceptionalSquareChartDifferentialMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure ((v : {v // v ∈ S}) →
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1

/-- On a finite exceptional square chart, the existing Mathlib-Haar product
is the literal finite conversion scalar times the differential-Haar product.
No coefficient is silently identified with one. -/
theorem finiteExceptionalSquareChartAmbientMeasure_eq_smul_differential
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (Measure.pi fun v : {v // v ∈ S} ↦
        padicUnitSquareIdentityChartAmbientSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) =
      rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar S •
        rationalIdeleFiniteExceptionalSquareChartDifferentialMeasure S := by
  let base := fun v : {v // v ∈ S} ↦
    padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1
  letI (v : {v // v ∈ S}) : SigmaFinite (base v) := by
    unfold base padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).open_source.measurableSet]
    infer_instance
  unfold rationalIdeleFiniteExceptionalSquareChartDifferentialMeasure
    rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
  simp_rw [padicUnitSquareIdentityChartAmbientSourceMeasure_eq_smul_differential]
  change Measure.pi (fun v ↦
      rationalPadicMathlibHaarToDifferentialScalar v.1 • base v) =
    (∏ v : {v // v ∈ S}, rationalPadicMathlibHaarToDifferentialScalar v.1) •
      Measure.pi base
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi _ s]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.coe_finset_prod, Finset.prod_mul_distrib]

end RationalQuadraticSpaceMatrix
