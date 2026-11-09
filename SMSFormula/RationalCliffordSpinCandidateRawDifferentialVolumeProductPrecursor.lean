import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDifferentialScale
import SMSFormula.RationalCliffordSpinCandidateCoherentQuotientMeasure

/-!
# Raw differential-volume product precursor for the Clifford--Spin candidate

The coherent finite-adelic Spin measure is the restricted product in which
every good integral factor has probability mass one.  Passing back to the raw
placewise differential scale therefore requires the product of the literal
good integral volumes.  This file defines its natural prime cutoffs and
isolates convergence to a positive finite scalar as an explicit certificate.

Conditional on such a certificate, the same scalar multiplies the coherent
finite-adelic measure, the coherent full-adelic measure, and its measurable-
Weil quotient measure.  All transport formulas are proved exactly.  No
convergence theorem, local-volume evaluation, condition (K), Ono comparison,
or Tamagawa-volume statement is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 600000

local instance rawSpinDifferentialVolumeProductDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rawSpinDifferentialVolumeProductFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance rawSpinDifferentialVolumeProductFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-! ## Natural height-one cutoffs and their volume products -/

/-- The height-one places of `ℚ` whose underlying rational prime is at most
`N`. -/
def cliffordSpinCandidateRationalHeightOnePlacesUpTo (N : ℕ) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (rationalPrimesUpTo N).map
    Rat.HeightOneSpectrum.primesEquiv.symm.toEmbedding

@[simp]
theorem mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff
    (N : ℕ) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v ∈ cliffordSpinCandidateRationalHeightOnePlacesUpTo N ↔
      (Rat.HeightOneSpectrum.primesEquiv v).1 ≤ N := by
  simp only [cliffordSpinCandidateRationalHeightOnePlacesUpTo,
    Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨q, hq, hqv⟩
    have hqv' : q = Rat.HeightOneSpectrum.primesEquiv v := by
      simpa using congrArg Rat.HeightOneSpectrum.primesEquiv hqv
    subst q
    exact (mem_rationalPrimesUpTo_iff N _).1 hq
  · intro hv
    refine ⟨Rat.HeightOneSpectrum.primesEquiv v, ?_, ?_⟩
    · exact (mem_rationalPrimesUpTo_iff N _).2 hv
    · simp

/-- The finite product of the Spin differential volumes at places up
to `N` outside the fixed coordinate-presentation bad set.  The fixed bad
places are omitted because the coherent empty block already contains their raw
local Haar factors. -/
def cliffordSpinCandidateIntegralVolumePartialProduct
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) : ℝ≥0∞ :=
  ∏ v ∈
      cliffordSpinCandidateRationalHeightOnePlacesUpTo N \
        V.cliffordSpinCandidateAdmissibleBadPlaces,
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v

/-- The finite product of reciprocal integral volumes at the same good-place
cutoff.  This is the form naturally visible in the coherent block weights. -/
def cliffordSpinCandidateIntegralInverseVolumePartialProduct
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) : ℝ≥0∞ :=
  ∏ v ∈
      cliffordSpinCandidateRationalHeightOnePlacesUpTo N \
        V.cliffordSpinCandidateAdmissibleBadPlaces,
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹

/-- The reciprocal-volume cutoff is exactly the coherent weight of the
corresponding cutoff block. -/
theorem cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_blockWeight
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
        (cliffordSpinCandidateRationalHeightOnePlacesUpTo N) := by
  simpa only [cliffordSpinCandidateIntegralInverseVolumePartialProduct] using
    (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces
      (cliffordSpinCandidateRationalHeightOnePlacesUpTo N)).symm

/-- Every raw integral-volume cutoff is nonzero. -/
theorem cliffordSpinCandidateIntegralVolumePartialProduct_ne_zero
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralVolumePartialProduct N ≠ 0 := by
  unfold cliffordSpinCandidateIntegralVolumePartialProduct
  exact Finset.prod_ne_zero_iff.mpr fun v hv =>
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
      ∅ ⟨v, by
        simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
          Finset.empty_union] using (Finset.mem_sdiff.mp hv).2⟩

/-- Every raw integral-volume cutoff is finite. -/
theorem cliffordSpinCandidateIntegralVolumePartialProduct_ne_top
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralVolumePartialProduct N ≠ ⊤ := by
  unfold cliffordSpinCandidateIntegralVolumePartialProduct
  exact ENNReal.prod_ne_top fun v _ =>
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v

/-- Every reciprocal-volume cutoff is nonzero. -/
theorem cliffordSpinCandidateIntegralInverseVolumePartialProduct_ne_zero
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N ≠ 0 := by
  rw [V.cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_blockWeight]
  exact
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero
      (cliffordSpinCandidateRationalHeightOnePlacesUpTo N)

/-- Every reciprocal-volume cutoff is finite. -/
theorem cliffordSpinCandidateIntegralInverseVolumePartialProduct_ne_top
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N ≠ ⊤ := by
  rw [V.cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_blockWeight]
  exact
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top
      (cliffordSpinCandidateRationalHeightOnePlacesUpTo N)

/-- Convergence of the good-place reciprocal-volume cutoffs to the reciprocal
of a specified raw finite scale. -/
def CliffordSpinCandidateIntegralInverseVolumeProductTendsTo
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
    Filter.atTop (nhds (finiteScale : ℝ≥0∞)⁻¹)

/-- The analytic input for the raw Spin differential scale: the
good-place volume products converge to a strictly positive finite scalar.
Finiteness is encoded by `finiteScale : ℝ≥0`; positivity is a
separate field because zero scaling would destroy Haar normalization. -/
structure CliffordSpinCandidateRawDifferentialVolumeProductCertificate
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) : Prop where
  finiteScale_pos : 0 < finiteScale
  inverseVolumeProduct_tendsto :
    V.CliffordSpinCandidateIntegralInverseVolumeProductTendsTo finiteScale

namespace CliffordSpinCandidateRawDifferentialVolumeProductCertificate

theorem finiteScale_ne_zero
    {V : RationalQuadraticSpaceMatrix n} {finiteScale : ℝ≥0}
    (C : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      finiteScale) :
    finiteScale ≠ 0 :=
  ne_of_gt C.finiteScale_pos

end CliffordSpinCandidateRawDifferentialVolumeProductCertificate

/-! ## Conditional raw finite and full-adelic measures -/

/-- The raw finite-adelic differential scale associated with a proposed
positive finite limit. -/
noncomputable def finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    Measure V.FiniteAdelicCliffordSpinCandidateGroup :=
  (finiteScale : ℝ≥0∞) •
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

/-- The raw full-adelic differential scale associated with the same proposed
finite-place limit. -/
noncomputable def fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    Measure V.FullAdelicCliffordSpinCandidateGroup :=
  (finiteScale : ℝ≥0∞) •
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure

/-- The raw full measure splits as the completed real differential Haar
factor times the raw-scaled coherent finite factor. -/
theorem map_fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    Measure.map
        V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph
        (V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          finiteScale) =
      V.realCliffordSpinCandidateChartGluedMeasure.prod
        (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          finiteScale) := by
  letI : SigmaFinite
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
  letI : SFinite
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
    infer_instance
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  rw [Measure.map_smul,
    V.map_fullAdelicCliffordSpinCandidateCoherentGroupMeasure_realFinite,
    Measure.prod_smul_right]

/-- At a certified positive scale, the raw full measure is Haar. -/
theorem fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0)
    (C : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      finiteScale) :
    Measure.IsHaarMeasure
      (V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        finiteScale) := by
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  exact Measure.IsHaarMeasure.smul _
    (ENNReal.coe_ne_zero.mpr C.finiteScale_ne_zero) ENNReal.coe_ne_top

/-- The raw full measure is the product of the proposed raw finite scale and
the already explicit coherent-to-reference Haar scalar. -/
theorem fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_eq_smul_referenceHaar
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale =
      ((finiteScale : ℝ≥0∞) *
          (V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar :
            ℝ≥0∞)) •
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure := by
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  rw [V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_eq_smul_referenceHaar]
  change
    (finiteScale : ℝ≥0∞) •
        ((V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar :
          ℝ≥0∞) •
          V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure) = _
  rw [smul_smul]

/-! ## Conditional quotient normalization -/

/-- The measurable-Weil datum at the proposed raw differential scale.  The
ambient and quotient measures are scaled together, so the measurable Weil
identity is inherited without a new quotient construction. -/
noncomputable def
    fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    V.CliffordSpinCandidateMeasurableWeilMeasureData :=
  V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.smul finiteScale

@[simp]
theorem
    fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_adelicMeasure
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).adelicMeasure =
      V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        finiteScale := by
  unfold fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
    fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  change
    finiteScale •
        V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.adelicMeasure =
      (finiteScale : ℝ≥0∞) •
        V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure
  rw [V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData_adelicMeasure]
  rfl

@[simp]
theorem
    fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_smul_coherent
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).quotientVolumeENNReal =
      (finiteScale : ℝ≥0∞) *
        V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientVolumeENNReal := by
  exact
    V.fullAdelicCliffordSpinCandidateCoherentMeasurableWeilData.quotientVolumeENNReal_smul
      finiteScale

/-- The conditionally raw quotient volume is the mass of the completed
fundamental domain in the conditionally raw full-adelic measure. -/
theorem
    fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_domainMass
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).quotientVolumeENNReal =
      V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  rw [V.fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_smul_coherent,
    V.fullAdelicCliffordSpinCandidateCoherentQuotientVolume_eq_domainMass]
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]

/-- The conditionally raw quotient scale relative to the original reference
datum is the product of the raw finite scale and the coherent Haar-comparison
scalar. -/
theorem
    fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_smul_reference
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale).quotientVolumeENNReal =
      (finiteScale : ℝ≥0∞) *
        (V.fullAdelicCliffordSpinCandidateCoherentToReferenceHaarScalar :
          ℝ≥0∞) *
        V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.referenceQuotientVolumeENNReal := by
  rw [V.fullAdelicCliffordSpinCandidateRawDifferentialQuotientVolume_eq_smul_coherent,
    V.fullAdelicCliffordSpinCandidateCoherentQuotientVolume_eq_smul_reference]
  rw [mul_assoc]

/-! ## Raw normalization from the cutoff-product certificate -/

/-- The conditionally constructed datum has the raw differential
normalization precisely when supplied with the positive-finite cutoff-product
certificate.  This structure records the analytic input and its exact ambient
measure without duplicating the stored measurable Weil identity. -/
structure IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale
    (V : RationalQuadraticSpaceMatrix n)
    (finiteScale : ℝ≥0)
    (D : V.CliffordSpinCandidateMeasurableWeilMeasureData) : Prop where
  volumeProductCertificate :
    V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate finiteScale
  adelicMeasure_eq :
    D.adelicMeasure =
      V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale

/-- A positive-finite cutoff-product certificate inhabits the raw
normalization structure for the simultaneously scaled coherent datum. -/
def
    fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0)
    (C : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      finiteScale) :
    V.IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale
      finiteScale
      (V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
        finiteScale) :=
  ⟨C,
    V.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_adelicMeasure
      finiteScale⟩

end RationalQuadraticSpaceMatrix
