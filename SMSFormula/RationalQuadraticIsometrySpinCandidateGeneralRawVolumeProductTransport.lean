import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralIntegralSupport
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor

/-!
# Raw Spin volume-product transport across an arbitrary rational isometry

A certified arbitrary-isometry support already gives equality of the literal
Spin integral volumes outside a finite set. The raw inverse-volume products
omit coordinate-dependent admissible bad sets on their two sides. This file
adjoins both such sets to that support, splits both cutoff products into their
exceptional factors and one common tail, and retains the resulting positive
finite correction exactly.

Consequently a raw inverse-volume-product certificate on the target matrix
transports to the source matrix with its finite scale divided by that explicit
correction, and conversely. No correction is asserted to be one, and no
complement lattice, new chart, quotient measure, or Tamagawa value is
introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped BigOperators ENNReal NNReal

namespace QuadraticMap.IsometryEquiv

open RationalQuadraticSpaceMatrix

variable {m : ℕ}
variable {W Z : RationalQuadraticSpaceMatrix (m + 1)}
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

local instance rawSpinRationalIsometryVolumeDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The finite exceptional set used to compare the two raw Spin products: a
certified rational-isometry support together with both coordinate-admissible bad
sets. -/
def spinCandidateRawRationalIsometryBadPlaces
    (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  S ∪ W.cliffordSpinCandidateAdmissibleBadPlaces ∪
    Z.cliffordSpinCandidateAdmissibleBadPlaces ∪
      rationalPadicNormSupportPlaces
        (rationalIsometrySkewAdjointDetScalar W Z e)

/-- A natural-prime cutoff containing the full raw isometry bad set. -/
def spinCandidateRawRationalIsometryBadPlacesCutoff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℕ :=
  (e.spinCandidateRawRationalIsometryBadPlaces  S).sup fun v =>
    (Rat.HeightOneSpectrum.primesEquiv v).1

theorem spinCandidateRawRationalIsometryBadPlaces_subset_cutoff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.spinCandidateRawRationalIsometryBadPlaces  S ⊆
      cliffordSpinCandidateRationalHeightOnePlacesUpTo
        (e.spinCandidateRawRationalIsometryBadPlacesCutoff  S) := by
  intro v hv
  rw [mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff]
  unfold spinCandidateRawRationalIsometryBadPlacesCutoff
  exact Finset.le_sup
    (f := fun w : IsDedekindDomain.HeightOneSpectrum ℤ =>
      (Rat.HeightOneSpectrum.primesEquiv w).1) hv

/-- The source-side exceptional factor remaining after its admissible bad
places have already been omitted from the raw product. -/
def sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v ∈ e.spinCandidateRawRationalIsometryBadPlaces  S \
      W.cliffordSpinCandidateAdmissibleBadPlaces,
    (W
      |>.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹

/-- The target-side exceptional factor remaining after its admissible bad
places have already been omitted from the raw product. -/
def targetSpinCandidateRawRationalIsometryExceptionalInverseVolume
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v ∈ e.spinCandidateRawRationalIsometryBadPlaces  S \
      Z.cliffordSpinCandidateAdmissibleBadPlaces,
    (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹

/-- The exact finite scalar converting the eventual target reciprocal-volume
cutoff into the source cutoff. -/
def spinCandidateRawRationalIsometryInverseVolumeCorrection
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
    (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S)⁻¹

theorem sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S ≠ 0 := by
  unfold sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    ENNReal.inv_ne_zero.mpr
      (W
        |>.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v)

theorem sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_top
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S ≠ ⊤ := by
  unfold sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume
  exact ENNReal.prod_ne_top fun v hv =>
    ENNReal.inv_ne_top.mpr
      (W
        |>.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
          ∅ ⟨v, by
            simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
              Finset.empty_union] using (Finset.mem_sdiff.mp hv).2⟩)

theorem targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S ≠ 0 := by
  unfold targetSpinCandidateRawRationalIsometryExceptionalInverseVolume
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    ENNReal.inv_ne_zero.mpr
      (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v)

theorem targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_top
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S ≠ ⊤ := by
  unfold targetSpinCandidateRawRationalIsometryExceptionalInverseVolume
  exact ENNReal.prod_ne_top fun v hv =>
    ENNReal.inv_ne_top.mpr
      (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
        ∅ ⟨v, by
          simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
            Finset.empty_union] using (Finset.mem_sdiff.mp hv).2⟩)

theorem spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S ≠ 0 := by
  exact mul_ne_zero
    (e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_zero  S)
    (ENNReal.inv_ne_zero.mpr
      (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_top  S))

theorem spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_top  S)
    (ENNReal.inv_ne_top.mpr
      (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_zero  S))

/-- Beyond the common exceptional cutoff, the two raw Spin reciprocal-volume
products differ by exactly the finite rational-isometry correction. -/
theorem
    source_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_of_cutoff_le
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    {N : ℕ} (hN : e.spinCandidateRawRationalIsometryBadPlacesCutoff  S ≤ N) :
    W.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S *
        Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N := by
  classical
  let places := cliffordSpinCandidateRationalHeightOnePlacesUpTo N
  let badB := W.cliffordSpinCandidateAdmissibleBadPlaces
  let badA := Z.cliffordSpinCandidateAdmissibleBadPlaces
  let exceptional := e.spinCandidateRawRationalIsometryBadPlaces  S
  have hExceptional : exceptional ⊆ places := by
    exact Finset.Subset.trans
      (e.spinCandidateRawRationalIsometryBadPlaces_subset_cutoff  S)
      (fun v hv =>
        (mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff N v).2
          (le_trans
            ((mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff
              (e.spinCandidateRawRationalIsometryBadPlacesCutoff  S) v).1 hv)
            hN))
  have hBadB : badB ⊆ exceptional := by
    intro v hv
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hBadA : badA ⊆ exceptional := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hblockSet :
      places \ badB = (exceptional \ badB) ∪ (places \ exceptional) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hvPlaces, hvBad⟩
      by_cases hvExceptional : v ∈ exceptional
      · exact Or.inl ⟨hvExceptional, hvBad⟩
      · exact Or.inr ⟨hvPlaces, hvExceptional⟩
    · rintro (⟨hvExceptional, hvBad⟩ | ⟨hvPlaces, hvExceptional⟩)
      · exact ⟨hExceptional hvExceptional, hvBad⟩
      · exact ⟨hvPlaces, fun hvBad => hvExceptional (hBadB hvBad)⟩
  have hambientSet :
      places \ badA = (exceptional \ badA) ∪ (places \ exceptional) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hvPlaces, hvBad⟩
      by_cases hvExceptional : v ∈ exceptional
      · exact Or.inl ⟨hvExceptional, hvBad⟩
      · exact Or.inr ⟨hvPlaces, hvExceptional⟩
    · rintro (⟨hvExceptional, hvBad⟩ | ⟨hvPlaces, hvExceptional⟩)
      · exact ⟨hExceptional hvExceptional, hvBad⟩
      · exact ⟨hvPlaces, fun hvBad => hvExceptional (hBadA hvBad)⟩
  have hdisjB : Disjoint (exceptional \ badB) (places \ exceptional) := by
    exact Finset.disjoint_left.mpr fun v hvE hvP =>
      (Finset.mem_sdiff.mp hvP).2 (Finset.mem_sdiff.mp hvE).1
  have hdisjA : Disjoint (exceptional \ badA) (places \ exceptional) := by
    exact Finset.disjoint_left.mpr fun v hvE hvP =>
      (Finset.mem_sdiff.mp hvP).2 (Finset.mem_sdiff.mp hvE).1
  have htail :
      (∏ v ∈ places \ exceptional,
          (W
            |>.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) =
        ∏ v ∈ places \ exceptional,
          (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
    apply Finset.prod_congr rfl
    intro v hv
    have hvExceptional := (Finset.mem_sdiff.mp hv).2
    have hvS : v ∉ S := by
      intro hvS
      exact hvExceptional
        (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hvS)))
    rw [hS.integralVolume_eq W Z e v hvS]
  have hblock :
      W.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
        e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
          (∏ v ∈ places \ exceptional,
            (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) := by
    unfold cliffordSpinCandidateIntegralInverseVolumePartialProduct
      sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume
    change (∏ v ∈ places \ badB,
        (W
          |>.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) = _
    rw [hblockSet, Finset.prod_union hdisjB, htail]
  have hambient :
      Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
        e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
          (∏ v ∈ places \ exceptional,
            (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) := by
    unfold cliffordSpinCandidateIntegralInverseVolumePartialProduct
      targetSpinCandidateRawRationalIsometryExceptionalInverseVolume
    change (∏ v ∈ places \ badA,
        (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) = _
    rw [hambientSet, Finset.prod_union hdisjA]
  rw [hblock, hambient]
  unfold spinCandidateRawRationalIsometryInverseVolumeCorrection
  have hcancel :
      (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S)⁻¹ *
          e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S = 1 :=
    ENNReal.inv_mul_cancel
      (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_zero  S)
      (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume_ne_top  S)
  calc
    e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
        ∏ v ∈ places \ exceptional,
          (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ =
      e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S * 1 *
        ∏ v ∈ places \ exceptional,
          (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
        rw [mul_one]
    _ = e.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
        (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S)⁻¹ *
          (e.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume  S *
            ∏ v ∈ places \ exceptional,
              (Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) := by
      rw [← hcancel]
      ac_rfl

/-- The same eventual product identity solved in the target direction. -/
theorem
    target_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_inv_correction_mul_of_cutoff_le
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    {N : ℕ} (hN : e.spinCandidateRawRationalIsometryBadPlacesCutoff  S ≤ N) :
    Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S)⁻¹ *
        W.cliffordSpinCandidateIntegralInverseVolumePartialProduct N := by
  have hproduct :=
    e.source_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_of_cutoff_le
       hS hN
  have hcancel :
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S)⁻¹ *
          e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S = 1 :=
    ENNReal.inv_mul_cancel
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero  S)
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top  S)
  calc
    Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
        1 * Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N := by
      rw [one_mul]
    _ = (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S)⁻¹ *
        e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S *
          Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N := by
      rw [hcancel]
    _ = (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S)⁻¹ *
        (W
          |>.cliffordSpinCandidateIntegralInverseVolumePartialProduct N) := by
      rw [hproduct]
      ac_rfl

/-- The positive finite rational-isometry correction as an `NNReal`, suitable for
transporting the certified raw finite scale. -/
noncomputable def spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S).toNNReal

theorem coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S : ℝ≥0∞) =
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S := by
  unfold spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal
  exact ENNReal.coe_toNNReal
    (e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top  S)

theorem spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    0 < e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S := by
  unfold spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal
  exact ENNReal.toNNReal_pos
    (e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero  S)
    (e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top  S)

/-- Although its definition uses a certified finite support, the exact raw
rational-isometry correction is independent of that support. -/
theorem spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_of_supports
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hT : IsHorizontalIntegralTailRationalIsometrySupport W Z e T) :
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S =
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T := by
  let N := max (e.spinCandidateRawRationalIsometryBadPlacesCutoff  S)
    (e.spinCandidateRawRationalIsometryBadPlacesCutoff  T)
  let a := Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N
  have hSN :=
    e.source_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_of_cutoff_le
       hS (show e.spinCandidateRawRationalIsometryBadPlacesCutoff  S ≤ N by
        exact le_max_left _ _)
  have hTN :=
    e.source_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_of_cutoff_le
       hT (show e.spinCandidateRawRationalIsometryBadPlacesCutoff  T ≤ N by
        exact le_max_right _ _)
  have heq :
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S * a =
        e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T * a := by
    exact hSN.symm.trans hTN
  have ha0 : a ≠ 0 :=
    Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct_ne_zero N
  have haTop : a ≠ ⊤ :=
    Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct_ne_top N
  have hcancel : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 haTop
  calc
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S =
        e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S * 1 := by
      rw [mul_one]
    _ = e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S *
        (a * a⁻¹) := by rw [hcancel]
    _ = (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S * a) *
        a⁻¹ := by ac_rfl
    _ = (e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T * a) *
        a⁻¹ := by rw [heq]
    _ = e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T *
        (a * a⁻¹) := by ac_rfl
    _ = e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T * 1 := by
      rw [hcancel]
    _ = e.spinCandidateRawRationalIsometryInverseVolumeCorrection  T := by
      rw [mul_one]

theorem spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal_eq_of_supports
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hT : IsHorizontalIntegralTailRationalIsometrySupport W Z e T) :
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S =
      e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  T := by
  apply ENNReal.coe_injective
  rw [e.coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S,
    e.coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  T]
  exact e.spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_of_supports
     hS hT

/-- A target raw volume-product certificate transports to the source matrix.
The scale is divided by the exact positive finite exceptional correction. -/
theorem transport_target_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_toSource
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    {finiteScale : ℝ≥0}
    (C : Z.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      finiteScale) :
    W.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      (finiteScale /
        e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S) := by
  let correction := e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S
  let correctionNN :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S
  have hcorrection0 : correction ≠ 0 :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero  S
  have hcorrectionTop : correction ≠ ⊤ :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top  S
  have hcorrectionNNPos : 0 < correctionNN :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal_pos  S
  have hcorrectionNN0 : correctionNN ≠ 0 := ne_of_gt hcorrectionNNPos
  have hcoe : (correctionNN : ℝ≥0∞) = correction :=
    e.coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S
  refine
    { finiteScale_pos := div_pos C.finiteScale_pos hcorrectionNNPos
      inverseVolumeProduct_tendsto := ?_ }
  unfold CliffordSpinCandidateIntegralInverseVolumeProductTendsTo
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ => correction *
          Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop
        (nhds (correction * (finiteScale : ℝ≥0∞)⁻¹)) :=
    ENNReal.Tendsto.const_mul C.inverseVolumeProduct_tendsto
      (Or.inr hcorrectionTop)
  have htransport :
      Filter.Tendsto
        (fun N : ℕ =>
          W
            |>.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop
        (nhds (correction * (finiteScale : ℝ≥0∞)⁻¹)) := by
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [Filter.eventually_ge_atTop
      (e.spinCandidateRawRationalIsometryBadPlacesCutoff  S)] with N hN
    exact
      (e.source_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_of_cutoff_le
         hS hN).symm
  have hlimit :
      ((finiteScale / correctionNN : ℝ≥0) : ℝ≥0∞)⁻¹ =
        correction * (finiteScale : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_div hcorrectionNN0]
    rw [ENNReal.inv_div (Or.inl ENNReal.coe_ne_top)
      (Or.inl (ENNReal.coe_ne_zero.mpr hcorrectionNN0))]
    rw [ENNReal.div_eq_inv_mul, mul_comm, hcoe]
  change Filter.Tendsto
    (fun N : ℕ =>
      W
        |>.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
    Filter.atTop (nhds (((finiteScale / correctionNN : ℝ≥0) : ℝ≥0∞)⁻¹))
  rw [hlimit]
  exact htransport

/-- A source raw volume-product certificate transports to the target matrix.
The scale is multiplied by the exact positive finite exceptional correction. -/
theorem transport_source_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_toTarget
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    {finiteScale : ℝ≥0}
    (C : W
      |>.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
        finiteScale) :
    Z.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S *
        finiteScale) := by
  let correction := e.spinCandidateRawRationalIsometryInverseVolumeCorrection  S
  let correctionNN :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S
  have hcorrection0 : correction ≠ 0 :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero  S
  have hcorrectionTop : correction ≠ ⊤ :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top  S
  have hcorrectionNNPos : 0 < correctionNN :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal_pos  S
  have hcorrectionNN0 : correctionNN ≠ 0 := ne_of_gt hcorrectionNNPos
  have hcoe : (correctionNN : ℝ≥0∞) = correction :=
    e.coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal  S
  refine
    { finiteScale_pos := mul_pos hcorrectionNNPos C.finiteScale_pos
      inverseVolumeProduct_tendsto := ?_ }
  unfold CliffordSpinCandidateIntegralInverseVolumeProductTendsTo
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ => correction⁻¹ *
          W.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop
        (nhds (correction⁻¹ * (finiteScale : ℝ≥0∞)⁻¹)) :=
    ENNReal.Tendsto.const_mul C.inverseVolumeProduct_tendsto
      (Or.inr (ENNReal.inv_ne_top.mpr hcorrection0))
  have htransport :
      Filter.Tendsto
        (fun N : ℕ =>
          Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop
        (nhds (correction⁻¹ * (finiteScale : ℝ≥0∞)⁻¹)) := by
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [Filter.eventually_ge_atTop
      (e.spinCandidateRawRationalIsometryBadPlacesCutoff  S)] with N hN
    exact
      (e.target_cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_inv_correction_mul_of_cutoff_le
         hS hN).symm
  have hlimit :
      ((correctionNN * finiteScale : ℝ≥0) : ℝ≥0∞)⁻¹ =
        correction⁻¹ * (finiteScale : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_mul]
    rw [ENNReal.mul_inv
      (Or.inl (ENNReal.coe_ne_zero.mpr hcorrectionNN0))
      (Or.inl ENNReal.coe_ne_top)]
    rw [hcoe]
  change Filter.Tendsto
    (fun N : ℕ =>
      Z.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
    Filter.atTop
    (nhds (((correctionNN * finiteScale : ℝ≥0) : ℝ≥0∞)⁻¹))
  rw [hlimit]
  exact htransport

end QuadraticMap.IsometryEquiv

end
