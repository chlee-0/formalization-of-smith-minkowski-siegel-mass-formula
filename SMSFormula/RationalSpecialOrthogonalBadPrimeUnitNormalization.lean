import SMSFormula.RationalSpecialOrthogonalRealArchimedeanNormalization

/-!
# Reduction of raw differential normalization to bad-prime gauge defects

The Tamagawa chain reduces the ordinary mass product formula to a
unit normalization for the real differential mass times the finite local
correction product.  The real determinant and rational p-adic norm
calculations rewrite that unit normalization as one explicit finite product
over the Schulze--Pillot bad primes.

This module keeps the two unevaluated bad-prime ingredients as explicit
factors: the intrinsic coordinate-normalization correction and the
selected-density fiber correction.
-/

noncomputable section

open Matrix
open scoped BigOperators ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The product of intrinsic coordinate-normalization corrections over the
literal Schulze--Pillot bad-prime set. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialBadCoordinateCorrectionProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  ∏ q ∈ massBadPrimeSet L,
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialCoordinateNormalizationCorrection
      q.1

/-- The product of selected-density fiber corrections over the literal
Schulze--Pillot bad-prime set. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialBadFiberCorrectionProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  ∏ q ∈ massBadPrimeSet L,
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    L.localPadicSpecialOrthogonalDifferentialDensityFiberCorrection q.1

/-- The rational basis-comparison norm product over every bad prime.  Factors
outside the rational comparison support are equal to one. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  ∏ q ∈ massBadPrimeSet L,
    Rat.padicNormENNRealAtPrime c q

/-- The pointwise bad-prime gauge defect: local differential correction divided
by the rational basis-comparison norm. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  ∏ q ∈ massBadPrimeSet L,
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
      (Rat.padicNormENNRealAtPrime c q)⁻¹

/-- The real/finite unit normalization is exactly the explicit bad-prime unit
identity left after the real determinant and rational norm product formulas. -/
theorem globalDifferentialUnitNormalization_iff_badPrimeUnitIdentity
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
        1 ↔
      ENNReal.ofReal
            ((2 : ℝ) ^ n *
              (Real.sqrt
                |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
          (L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
            L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹) =
        1 := by
  rw [L.realDifferentialMass_mul_archimedean_mul_localCorrection_eq_formFactor_mul_badPrimeRatio]

/-- The bad-prime correction product splits literally into its intrinsic
coordinate and selected-fiber correction products. -/
theorem localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct_eq_coordinate_mul_fiber
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct =
      L.localPadicSpecialOrthogonalDifferentialBadCoordinateCorrectionProduct *
        L.localPadicSpecialOrthogonalDifferentialBadFiberCorrectionProduct := by
  unfold localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct
  unfold localPadicSpecialOrthogonalDifferentialBadCoordinateCorrectionProduct
  unfold localPadicSpecialOrthogonalDifferentialBadFiberCorrectionProduct
  simp only [localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime,
    localPadicSpecialOrthogonalDifferentialLocalCorrection,
    Finset.prod_mul_distrib]

/-- Extending the comparison-norm product from the support intersection to all
bad primes adds only factors equal to one. -/
theorem localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct_eq_badComparisonNormProduct
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct =
      L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct := by
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let B := massBadPrimeSet L
  let S := skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  have hunion : B = (B ∩ S) ∪ (B \ S) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (B ∩ S) (B \ S) := by
    rw [Finset.disjoint_left]
    intro q hqBS hqBnotS
    exact (Finset.mem_sdiff.mp hqBnotS).2 (Finset.mem_inter.mp hqBS).2
  unfold localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct
  unfold localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
  change (∏ q ∈ B, Rat.padicNormENNRealAtPrime c q) =
    ∏ q ∈ B ∩ S, Rat.padicNormENNRealAtPrime c q
  calc
    (∏ q ∈ B, Rat.padicNormENNRealAtPrime c q) =
        ∏ q ∈ (B ∩ S) ∪ (B \ S),
          Rat.padicNormENNRealAtPrime c q := by rw [← hunion]
    _ = (∏ q ∈ B ∩ S, Rat.padicNormENNRealAtPrime c q) *
        ∏ q ∈ B \ S, Rat.padicNormENNRealAtPrime c q :=
      Finset.prod_union hdisj
    _ = ∏ q ∈ B ∩ S, Rat.padicNormENNRealAtPrime c q := by
      have hdiff :
          (∏ q ∈ B \ S, Rat.padicNormENNRealAtPrime c q) = 1 := by
        apply Finset.prod_eq_one
        intro q hq
        have hqS : q ∉ S := (Finset.mem_sdiff.mp hq).2
        letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
        change
          (↑‖algebraMap ℚ ℚ_[q.1]
              (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ :
            ℝ≥0∞) = 1
        exact_mod_cast
          nnnorm_skewAdjointFixedFormElementaryDetScalar_eq_one_of_not_mem
            F hF hdet q hqS
      rw [hdiff, mul_one]

/-- The pointwise bad gauge-defect product is exactly the
bad correction divided by the supported bad comparison norms. -/
theorem localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_badCorrection_mul_inv_badComparisonNorm
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct =
      L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
        L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹ := by
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  let B := massBadPrimeSet L
  have hinv :
      (∏ q ∈ B, Rat.padicNormENNRealAtPrime c q)⁻¹ =
        ∏ q ∈ B, (Rat.padicNormENNRealAtPrime c q)⁻¹ := by
    symm
    apply ENNReal.eq_inv_of_mul_eq_one_left
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q hq
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    apply ENNReal.inv_mul_cancel
    · simpa only [Rat.padicNormENNRealAtPrime] using
        ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_zero
          q.1 F hF hdet
    · simpa only [Rat.padicNormENNRealAtPrime] using
        ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_top
          q.1 F hF hdet
  unfold localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct
  rw [Finset.prod_mul_distrib, ← hinv]
  change
    L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
        L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct⁻¹ =
      _
  rw [L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct_eq_badComparisonNormProduct]

/-- Expanding every bad gauge defect exposes the two exact unevaluated local
factors and no others. -/
theorem localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_coordinate_mul_fiber_mul_inv_comparison
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct =
      L.localPadicSpecialOrthogonalDifferentialBadCoordinateCorrectionProduct *
        (L.localPadicSpecialOrthogonalDifferentialBadFiberCorrectionProduct *
          L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct⁻¹) := by
  rw [L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_badCorrection_mul_inv_badComparisonNorm]
  rw [L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct_eq_coordinate_mul_fiber]
  rw [L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct_eq_badComparisonNormProduct]
  ac_rfl

/-- The remaining unit normalization, stated entirely as the closed real form
factor times the product of pointwise bad-prime gauge defects. -/
theorem badPrimeUnitIdentity_iff_formFactor_mul_badGaugeDefectProduct_eq_one
    (L : PositiveDefiniteIntegralLattice n) :
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
          L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹) =
      1 ↔
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct =
      1 := by
  rw [L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_badCorrection_mul_inv_badComparisonNorm]

/-- The bad-prime unit identity as a finite-product condition: it holds if and
only if the closed real form factor cancels the products of the intrinsic
coordinate correction, selected-fiber correction, and inverse comparison
norm. -/
theorem badPrimeUnitIdentity_iff_formFactor_mul_coordinate_mul_fiber_mul_inv_comparison_eq_one
    (L : PositiveDefiniteIntegralLattice n) :
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
          L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹) =
      1 ↔
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (L.localPadicSpecialOrthogonalDifferentialBadCoordinateCorrectionProduct *
          (L.localPadicSpecialOrthogonalDifferentialBadFiberCorrectionProduct *
            L.localPadicSpecialOrthogonalDifferentialAllBadComparisonNormProduct⁻¹)) =
      1 := by
  rw [← L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_badCorrection_mul_inv_badComparisonNorm]
  rw [L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_coordinate_mul_fiber_mul_inv_comparison]

end PositiveDefiniteIntegralLattice
