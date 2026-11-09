import SMSFormula.SkewAdjointRealDeterminantResidualAssembly
import SMSFormula.RationalPadicNormProductFormula
import SMSFormula.PadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct

/-!
# Product formula for the finite p-adic differential correction

The finite local-correction support is the union of the
Schulze--Pillot bad-prime set and the rational fixed/form basis-comparison
support.  This module splits that union into bad primes and comparison-support
primes outside the bad set.  At the latter primes the correction is the p-adic
norm of the single rational comparison scalar.

The rational norm product formula then cancels exactly those good-prime norms
against the real absolute value.  Correction/norm ratios at bad primes remain
explicit.
-/

noncomputable section

open Matrix
open scoped BigOperators ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal product of local differential corrections over all
Schulze--Pillot bad primes. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  ∏ q ∈ massBadPrimeSet L,
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q

/-- The comparison-norm product on the rational basis-comparison support
outside the Schulze--Pillot bad-prime set. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  ∏ q ∈ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet \
      massBadPrimeSet L,
    Rat.padicNormENNRealAtPrime c q

/-- The comparison-norm product on the intersection of the bad-prime set and
the rational basis-comparison support. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
    (L : PositiveDefiniteIntegralLattice n) : ℝ≥0∞ :=
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  ∏ q ∈ massBadPrimeSet L ∩
      skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet,
    Rat.padicNormENNRealAtPrime c q

/-- The canonical finite correction product is the bad-prime correction
product times the comparison norms on the remaining comparison support. -/
theorem
    localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_eq_badPrime_mul_goodComparisonNorm
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct =
      L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
        L.localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct := by
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let B := massBadPrimeSet L
  let S := skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet
  have hunion : B ∪ S = B ∪ (S \ B) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint B (S \ B) := by
    rw [Finset.disjoint_left]
    intro q hqB hqS
    exact (Finset.mem_sdiff.mp hqS).2 hqB
  unfold localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  unfold localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport
  unfold localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct
  unfold localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct
  change
    (∏ q ∈ B ∪ S,
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q) =
      (∏ q ∈ B,
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q) *
        ∏ q ∈ S \ B,
          Rat.padicNormENNRealAtPrime
            (skewAdjointFixedFormElementaryDetScalar F hF hdet) q
  rw [hunion, Finset.prod_union hdisj]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  have hqGood : q ∉ massBadPrimeSet L :=
    (Finset.mem_sdiff.mp hq).2
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime,
    Rat.padicNormENNRealAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialLocalCorrection_eq_comparisonNorm_of_not_mem_massBadPrimeSet
      q hqGood

/-- The full comparison-norm product splits into the bad-support intersection
and the comparison support outside the bad-prime set. -/
theorem
    prod_skewAdjointFixedFormElementaryDet_padicNorm_eq_badComparison_mul_goodComparison
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ skewAdjointFixedFormElementaryDetPrimeSupport
          L.rationalFormMatrix
          (L.form_symm.map (algebraMap ℤ ℚ))
          L.rationalFormMatrix_det_ne_zero,
        Rat.padicNormENNRealAtPrime
          (skewAdjointFixedFormElementaryDetScalar
            L.rationalFormMatrix
            (L.form_symm.map (algebraMap ℤ ℚ))
            L.rationalFormMatrix_det_ne_zero) q) =
      L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct *
        L.localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct := by
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let B := massBadPrimeSet L
  let S := skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  have hunion : S = (B ∩ S) ∪ (S \ B) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (B ∩ S) (S \ B) := by
    rw [Finset.disjoint_left]
    intro q hqBS hqSB
    exact (Finset.mem_sdiff.mp hqSB).2 (Finset.mem_inter.mp hqBS).1
  unfold localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
  unfold localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct
  change (∏ q ∈ S, Rat.padicNormENNRealAtPrime c q) =
    (∏ q ∈ B ∩ S, Rat.padicNormENNRealAtPrime c q) *
      ∏ q ∈ S \ B, Rat.padicNormENNRealAtPrime c q
  calc
    (∏ q ∈ S, Rat.padicNormENNRealAtPrime c q) =
        ∏ q ∈ (B ∩ S) ∪ (S \ B),
          Rat.padicNormENNRealAtPrime c q :=
      congrArg (fun T ↦ ∏ q ∈ T, Rat.padicNormENNRealAtPrime c q) hunion
    _ = (∏ q ∈ B ∩ S, Rat.padicNormENNRealAtPrime c q) *
        ∏ q ∈ S \ B, Rat.padicNormENNRealAtPrime c q :=
      Finset.prod_union hdisj

/-- The bad-prime comparison-norm product is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct_ne_zero
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct ≠ 0 := by
  unfold localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [Rat.padicNormENNRealAtPrime] using
    Matrix.ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_zero
      q.1 L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- The bad-prime comparison-norm product is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct_ne_top
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct ≠ ⊤ := by
  unfold localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
  apply ENNReal.prod_ne_top
  intro q hq
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [Rat.padicNormENNRealAtPrime] using
    Matrix.ENNReal_coe_nnnorm_skewAdjointFixedFormElementaryDetScalar_ne_top
      q.1 L.rationalFormMatrix
      (L.form_symm.map (algebraMap ℤ ℚ))
      L.rationalFormMatrix_det_ne_zero

/-- The rational product formula cancels every comparison norm outside the
bad-prime set.  The correction/norm quotient on bad primes remains literal. -/
theorem
    ofReal_abs_skewAdjointFixedFormElementaryDetScalar_mul_localCorrectionFiniteProduct_eq_badPrimeCorrection_mul_inv_badComparisonNorm
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    ENNReal.ofReal
          |((skewAdjointFixedFormElementaryDetScalar
              L.rationalFormMatrix
              (L.form_symm.map (algebraMap ℤ ℚ))
              L.rationalFormMatrix_det_ne_zero : ℚ) : ℝ)| *
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct =
      L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct *
        L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct⁻¹ := by
  let F := L.rationalFormMatrix
  let hF := L.form_symm.map (algebraMap ℤ ℚ)
  let hdet := L.rationalFormMatrix_det_ne_zero
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  let A : ℝ≥0∞ := ENNReal.ofReal |(c : ℝ)|
  let C : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let Cbad : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialBadPrimeCorrectionProduct
  let Nbad : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct
  let Ngood : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialGoodComparisonNormProduct
  have hC : C = Cbad * Ngood :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_eq_badPrime_mul_goodComparisonNorm
  have hN :
      (∏ q ∈ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet,
        Rat.padicNormENNRealAtPrime c q) = Nbad * Ngood :=
    L.prod_skewAdjointFixedFormElementaryDet_padicNorm_eq_badComparison_mul_goodComparison
  have hunit : A * (Nbad * Ngood) = 1 := by
    rw [← hN]
    exact Matrix.ofReal_abs_skewAdjointFixedFormElementaryDetScalar_mul_prod_padicNorm_eq_one
      F hF hdet
  have hNbad0 : Nbad ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct_ne_zero
  have hNbadTop : Nbad ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialBadComparisonNormProduct_ne_top
  have hgood : A * Ngood = Nbad⁻¹ := by
    calc
      A * Ngood = (A * Ngood) * 1 := by rw [mul_one]
      _ = (A * Ngood) * (Nbad * Nbad⁻¹) := by
        rw [ENNReal.mul_inv_cancel hNbad0 hNbadTop]
      _ = (A * (Nbad * Ngood)) * Nbad⁻¹ := by ac_rfl
      _ = Nbad⁻¹ := by rw [hunit, one_mul]
  change A * C = Cbad * Nbad⁻¹
  rw [hC]
  calc
    A * (Cbad * Ngood) = Cbad * (A * Ngood) := by ac_rfl
    _ = Cbad * Nbad⁻¹ := by rw [hgood]

end PositiveDefiniteIntegralLattice
