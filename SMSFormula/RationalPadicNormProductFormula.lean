import SMSFormula.RationalPadicNorm
import SMSFormula.SkewAdjointComparisonPrimeSupport

/-!
# The rational absolute-value and p-adic norm product formula

For a nonzero rational number, only the primes dividing its numerator or
denominator contribute a nontrivial p-adic norm.  This file packages that
literal finite support and proves the finite product formula directly from
natural-number prime factorization.

The final statement is ENNReal-valued so it can be used without distributing
`ENNReal.toReal` in the differential mass calculation.  No adelic quotient,
mass formula, or reference Haar measure is imported.
-/

noncomputable section

open scoped BigOperators ENNReal Matrix NNReal

namespace Rat

/-- Prime subtypes occurring in the prime factorization of a natural number. -/
def primeDivisorFinset (m : ℕ) : Finset {p : ℕ // Nat.Prime p} :=
  (m.primeFactors.attach).map
    ⟨fun p ↦ ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩, by
      intro p q hpq
      exact Subtype.ext
        (show p.1 = q.1 from
          congrArg (fun r : {p : ℕ // Nat.Prime p} ↦ r.1) hpq)⟩

/-- Membership in `primeDivisorFinset` is literal divisibility. -/
theorem mem_primeDivisorFinset_iff {m : ℕ} (hm : m ≠ 0)
    (q : {p : ℕ // Nat.Prime p}) :
    q ∈ primeDivisorFinset m ↔ q.1 ∣ m := by
  simp only [primeDivisorFinset, Finset.mem_map, Finset.mem_attach]
  constructor
  · rintro ⟨r, _hr, hrq⟩
    have hrdvd : r.1 ∣ m := (Nat.mem_primeFactors.mp r.2).2.1
    have hrval : r.1 = q.1 :=
      congrArg (fun s : {p : ℕ // Nat.Prime p} ↦ s.1) hrq
    simpa [hrval] using hrdvd
  · intro hq
    exact
      ⟨⟨q.1, Nat.mem_primeFactors.mpr ⟨q.2, hq, hm⟩⟩,
        trivial, Subtype.ext rfl⟩

/-- The finite set of rational primes dividing the numerator or denominator
of a rational number. -/
def padicNormPrimeSupport (c : ℚ) : Finset {p : ℕ // Nat.Prime p} :=
  primeDivisorFinset c.num.natAbs ∪ primeDivisorFinset c.den

/-- Membership in the rational p-adic norm support is literal divisibility of
the numerator or denominator. -/
theorem mem_padicNormPrimeSupport_iff {c : ℚ} (hc : c ≠ 0)
    (q : {p : ℕ // Nat.Prime p}) :
    q ∈ padicNormPrimeSupport c ↔
      q.1 ∣ c.num.natAbs ∨ q.1 ∣ c.den := by
  have hnum : c.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hc
  have hden : c.den ≠ 0 := c.den_nz
  rw [padicNormPrimeSupport, Finset.mem_union,
    mem_primeDivisorFinset_iff hnum,
    mem_primeDivisorFinset_iff hden]

/-- Outside the numerator/denominator support, a nonzero rational number has
p-adic valuation zero. -/
theorem padicValRat_eq_zero_of_not_mem_padicNormPrimeSupport
    {c : ℚ} (hc : c ≠ 0) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ padicNormPrimeSupport c) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    padicValRat q.1 c = 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hsupp : ¬(q.1 ∣ c.num.natAbs ∨ q.1 ∣ c.den) := by
    intro h
    exact hq ((mem_padicNormPrimeSupport_iff hc q).mpr h)
  have hnum : ¬q.1 ∣ c.num.natAbs := fun h => hsupp (Or.inl h)
  have hden : ¬q.1 ∣ c.den := fun h => hsupp (Or.inr h)
  rw [padicValRat_def, padicValInt,
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1),
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1),
    Nat.factorization_eq_zero_of_not_dvd hnum,
    Nat.factorization_eq_zero_of_not_dvd hden]
  norm_num

/-- Outside the numerator/denominator support, the p-adic norm of a nonzero
rational number is one. -/
theorem nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
    {c : ℚ} (hc : c ≠ 0) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ padicNormPrimeSupport c) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ‖algebraMap ℚ ℚ_[q.1] c‖₊ = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  have hcp : (c : ℚ_[q.1]) ≠ 0 := by
    exact_mod_cast hc
  have hval : padicValRat q.1 c = 0 :=
    padicValRat_eq_zero_of_not_mem_padicNormPrimeSupport hc q hq
  apply NNReal.eq
  change ‖(c : ℚ_[q.1])‖ = (1 : ℝ)
  rw [Padic.norm_eq_zpow_neg_valuation hcp,
    Padic.valuation_ratCast, hval]
  norm_num

/-- The p-adic norm of a nonzero rational number, written directly through
the prime-factorization exponents of its denominator and numerator. -/
theorem padicNorm_eq_factorization_div {c : ℚ} (hc : c ≠ 0)
    (q : {p : ℕ // Nat.Prime p}) :
    padicNorm q.1 c =
      (q.1 : ℚ) ^ (c.den.factorization q.1) /
        (q.1 : ℚ) ^ (c.num.natAbs.factorization q.1) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [padicNorm.eq_zpow_of_nonzero hc, padicValRat_def, padicValInt,
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1),
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1)]
  rw [neg_sub, zpow_sub₀]
  · simp
  · exact_mod_cast q.2.ne_zero

/-- The prime-factorization product of a nonzero natural number remains the
same over any larger finite prime set. -/
theorem prod_pow_factorization_eq_nat_of_primeDivisorFinset_subset
    (m : ℕ) (hm : m ≠ 0)
    (s : Finset {p : ℕ // Nat.Prime p})
    (hsub : primeDivisorFinset m ⊆ s) :
    ∏ q ∈ s, (q.1 : ℚ) ^ (m.factorization q.1) = (m : ℚ) := by
  rw [← show (∏ q ∈ primeDivisorFinset m,
      (q.1 : ℚ) ^ (m.factorization q.1)) = (m : ℚ) from by
    exact_mod_cast (show ∏ q ∈ primeDivisorFinset m,
      q.1 ^ (m.factorization q.1) = m by
      have hnat : ∏ p ∈ m.primeFactors,
          p ^ m.factorization p = m := by
        simpa [Nat.prod_factorization_eq_prod_primeFactors] using
          Nat.factorization_prod_pow_eq_self hm
      simp only [primeDivisorFinset, Finset.prod_map]
      change ∏ p ∈ m.primeFactors.attach,
        p.1 ^ m.factorization p.1 = m
      rw [Finset.prod_attach m.primeFactors
        (fun p ↦ p ^ m.factorization p)]
      exact hnat)]
  symm
  apply Finset.prod_subset hsub
  intro q hqs hqnot
  have hnotdvd : ¬q.1 ∣ m := by
    intro hdvd
    exact hqnot ((mem_primeDivisorFinset_iff hm q).2 hdvd)
  rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, pow_zero]

/-- The finite product of the rational p-adic norms is the denominator divided
by the absolute numerator. -/
theorem prod_padicNorm_padicNormPrimeSupport (c : ℚ) (hc : c ≠ 0) :
    ∏ q ∈ padicNormPrimeSupport c, padicNorm q.1 c =
      (c.den : ℚ) / (c.num.natAbs : ℚ) := by
  have hnum : c.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hc
  have hden : c.den ≠ 0 := c.den_nz
  simp_rw [padicNorm_eq_factorization_div hc]
  rw [Finset.prod_div_distrib]
  congr 1
  · exact prod_pow_factorization_eq_nat_of_primeDivisorFinset_subset
      c.den hden (padicNormPrimeSupport c)
      (by exact Finset.subset_union_right)
  · exact prod_pow_factorization_eq_nat_of_primeDivisorFinset_subset
      c.num.natAbs hnum (padicNormPrimeSupport c)
      (by exact Finset.subset_union_left)

/-- The rational absolute value times the supported finite product of p-adic
norms is one. -/
theorem abs_mul_prod_padicNorm_padicNormPrimeSupport (c : ℚ) (hc : c ≠ 0) :
    |c| * ∏ q ∈ padicNormPrimeSupport c, padicNorm q.1 c = 1 := by
  rw [prod_padicNorm_padicNormPrimeSupport c hc]
  rw [Rat.abs_def, Rat.divInt_eq_div]
  simp only [Int.cast_natCast]
  change ((c.num.natAbs : ℚ) / c.den) *
    ((c.den : ℚ) / c.num.natAbs) = 1
  field_simp [Rat.den_nz,
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hc)]

/-- The ENNReal p-adic norm of a rational scalar at a prime subtype.  The
primality instance is installed directly from the subtype proof. -/
def padicNormENNRealAtPrime (c : ℚ)
    (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  (‖algebraMap ℚ ℚ_[q.1] c‖₊ : ℝ≥0∞)

/-- The finite rational product formula in the ENNReal normalization used by
the differential mass calculation. -/
theorem ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one
    (c : ℚ) (hc : c ≠ 0) :
    ENNReal.ofReal |(c : ℝ)| *
      ∏ q ∈ padicNormPrimeSupport c, padicNormENNRealAtPrime c q = 1 := by
  have hreal :
      |(c : ℝ)| * ∏ q ∈ padicNormPrimeSupport c,
        ((padicNorm q.1 c : ℚ) : ℝ) = 1 := by
    exact_mod_cast abs_mul_prod_padicNorm_padicNormPrimeSupport c hc
  have hofReal := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_mul (abs_nonneg (c : ℝ)), ENNReal.ofReal_one,
    ENNReal.ofReal_prod_of_nonneg] at hofReal
  · rw [← hofReal]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    simp only [padicNormENNRealAtPrime]
    rw [ENNReal.coe_nnreal_eq]
    congr 1
    exact Padic.eq_padicNorm c
  · intro q hq
    exact_mod_cast padicNorm.nonneg c

end Rat

namespace Matrix

variable {n : ℕ}

/-- The general rational support specializes exactly to the support of the
fixed/form-adapted skew-adjoint determinant comparison. -/
theorem padicNormPrimeSupport_skewAdjointFixedFormElementaryDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Rat.padicNormPrimeSupport
        (skewAdjointFixedFormElementaryDetScalar F hF hdet) =
      skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet := by
  apply Finset.ext
  intro q
  rw [Rat.mem_padicNormPrimeSupport_iff
      (skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet) q,
    mem_skewAdjointFixedFormElementaryDetPrimeSupport_iff]

/-- The rational product formula specialized to the skew-adjoint
basis-comparison determinant and its prime support. -/
theorem
    ofReal_abs_skewAdjointFixedFormElementaryDetScalar_mul_prod_padicNorm_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    ENNReal.ofReal
        |((skewAdjointFixedFormElementaryDetScalar F hF hdet : ℚ) : ℝ)| *
      ∏ q ∈ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet,
        Rat.padicNormENNRealAtPrime
          (skewAdjointFixedFormElementaryDetScalar F hF hdet) q = 1 := by
  rw [← padicNormPrimeSupport_skewAdjointFixedFormElementaryDetScalar F hF hdet]
  exact Rat.ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one
    (skewAdjointFixedFormElementaryDetScalar F hF hdet)
    (skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet)

end Matrix
