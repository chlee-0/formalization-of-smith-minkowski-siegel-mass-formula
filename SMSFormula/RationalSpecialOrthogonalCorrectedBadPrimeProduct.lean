import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicCorrectedGaugeFactor
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDenominatorCongruenceQuotientCardinality
import SMSFormula.RationalSpecialOrthogonalBadPrimeUnitNormalization

/-!
# The corrected bad-prime gauge product

The odd-prime gauge factors retain the original explicit two/Gram value,
while the dyadic factor acquires the inverse Cayley tangent modulus certified
by the finite correspondence.  This module packages that pointwise split and
evaluates its finite product by separating the dyadic member of the
Schulze--Pillot bad-prime set.
-/

noncomputable section

open Matrix
open scoped BigOperators ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The corrected explicit factor on prime subtypes: the newly proved dyadic
factor at two and the original factor at every odd prime. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  if q.1 = 2 then
    L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor
  else
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
      q

/-- At the dyadic prime the corrected primewise factor is the corrected
dyadic factor literally. -/
theorem
    localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_two
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime =
      L.localPadicSpecialOrthogonalDifferentialCorrectedDyadicGaugeFactor := by
  simp [localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime]

/-- At every odd prime the corrected primewise factor remains the original
explicit two/Gram factor. -/
theorem
    localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq2 : q.1 ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime q =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        q := by
  simp [localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime,
    hq2]

/-- Every primewise gauge defect equals the corrected factor: the completed
dyadic theorem handles two and the completed denominator-quotient theorem
handles every odd prime. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedGaugeFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime q)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime q := by
  by_cases hq2 : q.1 = 2
  · have hq : q = localPadicSpecialOrthogonalDifferentialDyadicPrime :=
      Subtype.ext hq2
    subst q
    rw [L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_two]
    exact
      L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedDyadicGaugeFactor
  · rw [L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_of_ne_two
      q hq2]
    exact
      L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_of_ne_two
        q hq2

/-- The corrected factor differs from the original factor pointwise by the
inverse dyadic tangent modulus at two and by one elsewhere. -/
theorem
    localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_eq_if_mul_explicit
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime q =
      (if q.1 = 2 then
          (↑(‖LinearMap.det
              (skewAdjointPadicCayleyTangentFactor
                L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
        else 1) *
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q := by
  by_cases hq2 : q.1 = 2
  · have hq : q = localPadicSpecialOrthogonalDifferentialDyadicPrime :=
      Subtype.ext hq2
    subst q
    rfl
  · simp [
      L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_of_ne_two
        q hq2,
      hq2]

/-- The product of the indicator carrying the dyadic tangent modulus over the
literal bad-prime set is exactly that one dyadic modulus. -/
theorem
    prod_bad_if_two_inv_dyadicCayleyTangentModulus
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
      if q.1 = 2 then
        (↑(‖LinearMap.det
            (skewAdjointPadicCayleyTangentFactor
              L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
      else 1) =
      (↑(‖LinearMap.det
          (skewAdjointPadicCayleyTangentFactor
            L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹ := by
  let qtwo : {p : ℕ // Nat.Prime p} :=
    localPadicSpecialOrthogonalDifferentialDyadicPrime
  let T : ℝ≥0∞ :=
    (↑(‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor
          L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
  have hmem : qtwo ∈ massBadPrimeSet L := by
    exact (mem_massBadPrimeSet_iff L qtwo).2 (Or.inl rfl)
  change (∏ q ∈ massBadPrimeSet L,
      if q.1 = 2 then T else 1) = T
  rw [Finset.prod_eq_single qtwo]
  · simp [qtwo]
  · intro q hq hne
    have hq2 : q.1 ≠ 2 := by
      intro h
      exact hne (Subtype.ext h)
    simp [hq2]
  · intro hnot
    exact (hnot hmem).elim

/-- The corrected bad-prime factor product is the inverse dyadic Cayley
tangent modulus times the product of the original explicit factors. -/
theorem
    prod_correctedGaugeFactorAtPrime_bad_eq_inv_dyadicCayleyTangentModulus_mul_prod_explicit
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
        L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
          q) =
      (↑(‖LinearMap.det
          (skewAdjointPadicCayleyTangentFactor
            L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹ *
        ∏ q ∈ massBadPrimeSet L,
          L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q := by
  calc
    (∏ q ∈ massBadPrimeSet L,
        L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
          q) =
      ∏ q ∈ massBadPrimeSet L,
        ((if q.1 = 2 then
            (↑(‖LinearMap.det
                (skewAdjointPadicCayleyTangentFactor
                  L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
          else 1) *
          L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q) := by
        apply Finset.prod_congr rfl
        intro q hq
        exact
          L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime_eq_if_mul_explicit
            q
    _ =
      (∏ q ∈ massBadPrimeSet L,
          if q.1 = 2 then
            (↑(‖LinearMap.det
                (skewAdjointPadicCayleyTangentFactor
                  L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
          else 1) *
        ∏ q ∈ massBadPrimeSet L,
          L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
            q := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      rw [L.prod_bad_if_two_inv_dyadicCayleyTangentModulus]

/-- The existing bad gauge-defect product is exactly the corrected explicit
factor product, by the completed pointwise theorems. -/
theorem
    localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_prod_correctedGaugeFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct =
      ∏ q ∈ massBadPrimeSet L,
        L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
          q := by
  unfold localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct
  apply Finset.prod_congr rfl
  intro q hq
  simpa only [localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime,
    Rat.padicNormENNRealAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_correctedGaugeFactorAtPrime
      q

/-- The real Schulze--Pillot two coefficient with the prime instance installed
from the prime subtype. -/
noncomputable def twoPadicNormInvPowRealAtPrime
    (n : ℕ) (q : {p : ℕ // Nat.Prime p}) : ℝ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  ((twoPadicNormInvPow q.1 n : ℚ) : ℝ)

/-- The original explicit factor separates into the reciprocal dyadic
Schulze--Pillot coefficient and reciprocal Gram factor in `ENNReal`. -/
theorem
    localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_eq_inv_twoCoefficient_mul_inv_gram
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        q =
      ENNReal.ofReal
          (twoPadicNormInvPowRealAtPrime n q)⁻¹ *
        ENNReal.ofReal
          (gramDetPadicNormFactorAtPrime L q)⁻¹ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have htwo :
      0 < (((twoPadicNormInvPow q.1 n : ℚ) : ℝ)) := by
    exact_mod_cast twoPadicNormInvPow_pos q.1 n
  have hgram : 0 < gramDetPadicNormFactor L q.1 := by
    exact gramDetPadicNormFactor_pos L q.1
  change
    (ENNReal.ofReal
      ((((twoPadicNormInvPow q.1 n : ℚ) : ℝ) *
        gramDetPadicNormFactor L q.1)))⁻¹ =
      ENNReal.ofReal
          (((twoPadicNormInvPow q.1 n : ℚ) : ℝ))⁻¹ *
        ENNReal.ofReal
          (gramDetPadicNormFactor L q.1)⁻¹
  rw [ENNReal.ofReal_mul htwo.le]
  rw [ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr htwo))
    (Or.inl ENNReal.ofReal_ne_top)]
  rw [ENNReal.ofReal_inv_of_pos htwo, ENNReal.ofReal_inv_of_pos hgram]

/-- Over the bad-prime set the reciprocal Schulze--Pillot two coefficient has
only its literal dyadic contribution. -/
theorem
    prod_bad_inv_twoCoefficient_eq_inv_two_pow
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
      ENNReal.ofReal
        (twoPadicNormInvPowRealAtPrime n q)⁻¹) =
      (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ := by
  let qtwo : {p : ℕ // Nat.Prime p} :=
    localPadicSpecialOrthogonalDifferentialDyadicPrime
  have hmem : qtwo ∈ massBadPrimeSet L := by
    exact (mem_massBadPrimeSet_iff L qtwo).2 (Or.inl rfl)
  rw [Finset.prod_eq_single qtwo]
  · dsimp only [qtwo, localPadicSpecialOrthogonalDifferentialDyadicPrime]
    unfold twoPadicNormInvPowRealAtPrime
    rw [twoPadicNormInvPow_eq_two_pow]
    rw [show (((((2 : ℚ) ^ n : ℚ) : ℝ))) = (2 : ℝ) ^ n by norm_num]
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  · intro q hq hne
    have hq2 : q.1 ≠ 2 := by
      intro h
      exact hne (Subtype.ext h)
    unfold twoPadicNormInvPowRealAtPrime
    rw [twoPadicNormInvPow_eq_one_of_ne_two hq2]
    norm_num
  · intro hnot
    exact (hnot hmem).elim

/-- The finite product of reciprocal Gram factors commutes with `ofReal`
because every factor is positive. -/
theorem
    prod_bad_ENNReal_ofReal_inv_gram_eq_ofReal_prod_inv_gram
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
      ENNReal.ofReal
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ENNReal.ofReal
        (∏ q ∈ massBadPrimeSet L,
          (gramDetPadicNormFactorAtPrime L q)⁻¹) := by
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro q hq
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  exact (inv_pos.mpr
    (by
      unfold gramDetPadicNormFactorAtPrime
      exact gramDetPadicNormFactor_pos L q.1)).le

/-- The original explicit-factor product is the reciprocal dyadic rank
coefficient times the `ofReal` of the reciprocal Gram-factor product. -/
theorem
    prod_explicitTwoGramGaugeFactorAtPrime_bad
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q) =
      (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ *
        ENNReal.ofReal
          (∏ q ∈ massBadPrimeSet L,
            (gramDetPadicNormFactorAtPrime L q)⁻¹) := by
  calc
    (∏ q ∈ massBadPrimeSet L,
        L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
          q) =
      ∏ q ∈ massBadPrimeSet L,
        (ENNReal.ofReal
            (twoPadicNormInvPowRealAtPrime n q)⁻¹ *
          ENNReal.ofReal
            (gramDetPadicNormFactorAtPrime L q)⁻¹) := by
        apply Finset.prod_congr rfl
        intro q hq
        exact
          L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime_eq_inv_twoCoefficient_mul_inv_gram
            q
    _ =
      (∏ q ∈ massBadPrimeSet L,
          ENNReal.ofReal
            (twoPadicNormInvPowRealAtPrime n q)⁻¹) *
        ∏ q ∈ massBadPrimeSet L,
          ENNReal.ofReal
            (gramDetPadicNormFactorAtPrime L q)⁻¹ := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      rw [L.prod_bad_inv_twoCoefficient_eq_inv_two_pow,
        L.prod_bad_ENNReal_ofReal_inv_gram_eq_ofReal_prod_inv_gram]

/-- The closed real form factor cancels the corrected bad-prime explicit
factor product.  The rank-`n` binary coefficient cancels its reciprocal first;
the remaining real/Gram factor then cancels the inverse dyadic Cayley tangent
modulus by the completed binary-residual theorem. -/
theorem
    ENNReal_ofReal_two_pow_mul_rationalForm_sqrt_det_pow_mul_prod_correctedGaugeFactorAtPrime_bad_eq_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        (∏ q ∈ massBadPrimeSet L,
          L.localPadicSpecialOrthogonalDifferentialCorrectedGaugeFactorAtPrime
            q) =
      1 := by
  let R : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ n)
  let F : ℝ≥0∞ :=
    ENNReal.ofReal
      ((Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1))
  let G : ℝ≥0∞ :=
    ENNReal.ofReal
      (∏ q ∈ massBadPrimeSet L,
        (gramDetPadicNormFactorAtPrime L q)⁻¹)
  let T : ℝ≥0∞ :=
    (↑(‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor
          L.rationalFormMatrix 2).toLinearMap‖₊ : ℝ≥0∞))⁻¹
  have hR0 : R ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hRtop : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hFG :
      F * G =
        ENNReal.ofReal
          ((Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1) *
            (∏ q ∈ massBadPrimeSet L,
              (gramDetPadicNormFactorAtPrime L q)⁻¹)) := by
    unfold F G
    rw [ENNReal.ofReal_mul]
    positivity
  rw [L.prod_correctedGaugeFactorAtPrime_bad_eq_inv_dyadicCayleyTangentModulus_mul_prod_explicit]
  rw [L.prod_explicitTwoGramGaugeFactorAtPrime_bad]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
  change (R * F) * (T * (R⁻¹ * G)) = 1
  calc
    (R * F) * (T * (R⁻¹ * G)) =
        (R * R⁻¹) * (F * G * T) := by ac_rfl
    _ = F * G * T := by
      rw [ENNReal.mul_inv_cancel hR0 hRtop, one_mul]
    _ = 1 := by
      rw [hFG]
      exact
        L.ENNReal_ofReal_rationalForm_sqrt_det_pow_mul_prod_inv_gram_mul_inv_dyadicCayleyTangentModulus_eq_one

/-- The closed real form factor times the actual bad gauge-defect product is
one.  Pointwise local mathematics enters only through the explicit corrected
factor equality above. -/
theorem
    ENNReal_ofReal_two_pow_mul_rationalForm_sqrt_det_pow_mul_badGaugeDefectProduct_eq_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    ENNReal.ofReal
          ((2 : ℝ) ^ n *
            (Real.sqrt
              |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) *
        L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct =
      1 := by
  rw [L.localPadicSpecialOrthogonalDifferentialBadGaugeDefectProduct_eq_prod_correctedGaugeFactorAtPrime]
  exact
    L.ENNReal_ofReal_two_pow_mul_rationalForm_sqrt_det_pow_mul_prod_correctedGaugeFactorAtPrime_bad_eq_one

/-- The global real differential factor and finite local correction product
have unit product, with every mass-specific local calculation internal. -/
theorem globalDifferentialUnitNormalization
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
      1 := by
  apply
    (L.globalDifferentialUnitNormalization_iff_badPrimeUnitIdentity).2
  apply
    (L.badPrimeUnitIdentity_iff_formFactor_mul_badGaugeDefectProduct_eq_one).2
  exact
    L.ENNReal_ofReal_two_pow_mul_rationalForm_sqrt_det_pow_mul_badGaugeDefectProduct_eq_one

end PositiveDefiniteIntegralLattice
