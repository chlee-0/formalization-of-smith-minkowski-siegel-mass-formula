import SMSFormula.RationalSpecialOrthogonalDyadicGlobalBinaryFactor
import SMSFormula.RationalPadicNormProductFormula

/-!
# Finite product of the Schulze--Pillot Gram factors

This module evaluates the finite product of the local real-power factors
attached to the bilinear discriminant.  It first keeps the product over the
literal rational p-adic norm support, so the dyadic contribution from
`polarDeterminant = 2^n * pairingDeterminant` remains visible.
-/

noncomputable section

open scoped BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral discriminant norm at a prime subtype, with its primality
instance installed locally. -/
noncomputable def polarDeterminantPadicIntNormAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  ‖(L.polarDeterminant : ℤ_[q.1])‖

/-- The local Schulze--Pillot Gram factor at a prime subtype. -/
noncomputable def gramDetPadicNormFactorAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  gramDetPadicNormFactor L q.1

/-- The rational p-adic norm support of the positive integral discriminant is
exactly its prime-divisor support. -/
theorem mem_padicNormPrimeSupport_polarDeterminant_iff
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ) ↔
      q.1 ∣ L.polarDeterminant.natAbs := by
  rw [Rat.mem_padicNormPrimeSupport_iff]
  · norm_num
    intro hq_one
    exact (q.2.ne_one hq_one).elim
  · exact_mod_cast (ne_of_gt L.polarDeterminant_pos)

/-- The integral discriminant norm used by the local Gram factor is the
rational p-adic norm used by the finite product formula. -/
theorem polarDeterminant_padicInt_norm_eq_padicNorm
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    polarDeterminantPadicIntNormAtPrime L q =
      ((padicNorm q.1 (L.polarDeterminant : ℚ) : ℚ) : ℝ) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold polarDeterminantPadicIntNormAtPrime
  simpa using (Padic.eq_padicNorm (p := q.1) (L.polarDeterminant : ℚ))

/-- The finite product of the positive integral discriminant norms over its
exact rational support is the reciprocal real discriminant. -/
theorem polarDeterminant_mul_prod_padicInt_norm_padicNormPrimeSupport_eq_one
    (L : PositiveDefiniteIntegralLattice n) :
    (L.polarDeterminant : ℝ) *
        ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
          polarDeterminantPadicIntNormAtPrime L q =
      1 := by
  have hdisc_ne : (L.polarDeterminant : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.polarDeterminant_pos)
  have hrat :=
    Rat.abs_mul_prod_padicNorm_padicNormPrimeSupport
      (L.polarDeterminant : ℚ) hdisc_ne
  have hreal :
      |((L.polarDeterminant : ℚ) : ℝ)| *
          ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
            ((padicNorm q.1 (L.polarDeterminant : ℚ) : ℚ) : ℝ) =
        1 := by
    exact_mod_cast hrat
  rw [abs_of_pos (by exact_mod_cast L.polarDeterminant_pos)] at hreal
  calc
    (L.polarDeterminant : ℝ) *
          ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
            polarDeterminantPadicIntNormAtPrime L q =
        (L.polarDeterminant : ℝ) *
          ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
            ((padicNorm q.1 (L.polarDeterminant : ℚ) : ℚ) : ℝ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro q hq
      exact L.polarDeterminant_padicInt_norm_eq_padicNorm q
    _ = 1 := hreal

/-- Equivalently, the supported product of integral discriminant norms is the
reciprocal real discriminant. -/
theorem prod_padicInt_norm_padicNormPrimeSupport_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
        polarDeterminantPadicIntNormAtPrime L q) =
      (L.polarDeterminant : ℝ)⁻¹ := by
  have hdisc : (L.polarDeterminant : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.polarDeterminant_pos)
  apply mul_left_cancel₀ hdisc
  rw [mul_inv_cancel₀ hdisc]
  exact L.polarDeterminant_mul_prod_padicInt_norm_padicNormPrimeSupport_eq_one

/-- Outside the exact rational support, the integral discriminant norm is
one. -/
theorem polarDeterminantPadicIntNormAtPrime_eq_one_of_not_mem_padicNormPrimeSupport
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ)) :
    polarDeterminantPadicIntNormAtPrime L q = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  rw [L.polarDeterminant_padicInt_norm_eq_padicNorm q]
  have hdisc_ne : (L.polarDeterminant : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.polarDeterminant_pos)
  have hval : padicValRat q.1 (L.polarDeterminant : ℚ) = 0 :=
    Rat.padicValRat_eq_zero_of_not_mem_padicNormPrimeSupport
      hdisc_ne q hq
  rw [padicNorm.eq_zpow_of_nonzero hdisc_ne, hval]
  norm_num

/-- Outside the exact discriminant support, the local Gram factor is one. -/
theorem gramDetPadicNormFactorAtPrime_eq_one_of_not_mem_padicNormPrimeSupport
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ)) :
    gramDetPadicNormFactorAtPrime L q = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  unfold gramDetPadicNormFactorAtPrime
  unfold gramDetPadicNormFactor
  rw [show ‖(L.polarDeterminant : ℤ_[q.1])‖ = 1 by
    simpa [polarDeterminantPadicIntNormAtPrime] using
      L.polarDeterminantPadicIntNormAtPrime_eq_one_of_not_mem_padicNormPrimeSupport q hq]
  exact Real.one_rpow _

/-- The exact discriminant support is contained in the Schulze--Pillot bad
prime set. -/
theorem padicNormPrimeSupport_polarDeterminant_subset_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) :
    Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ) ⊆
      massBadPrimeSet L := by
  intro q hq
  exact (mem_massBadPrimeSet_iff L q).2
    (Or.inr ((L.mem_padicNormPrimeSupport_polarDeterminant_iff q).1 hq))

/-- Extending the inverse Gram-factor product from exact discriminant support
to all Schulze--Pillot bad primes adds only factors equal to one. -/
theorem prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_support
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
        (gramDetPadicNormFactorAtPrime L q)⁻¹ := by
  symm
  apply Finset.prod_subset
    (L.padicNormPrimeSupport_polarDeterminant_subset_massBadPrimeSet)
  intro q hqbad hqsupp
  rw [L.gramDetPadicNormFactorAtPrime_eq_one_of_not_mem_padicNormPrimeSupport
    q hqsupp, inv_one]

/-- The inverse Gram-factor product over exact support is the positive
reciprocal discriminant raised to `(n-1)/2`. -/
theorem prod_inv_gramDetPadicNormFactorAtPrime_support
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((L.polarDeterminant : ℝ)⁻¹) ^ (((n : ℝ) - 1) / 2) := by
  let a : ℝ := ((1 : ℝ) - (n : ℝ)) / 2
  have hnonneg : ∀ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
      0 ≤ polarDeterminantPadicIntNormAtPrime L q := by
    intro q hq
    exact norm_nonneg _
  calc
    (∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
          (gramDetPadicNormFactorAtPrime L q)⁻¹) =
        ∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
          (polarDeterminantPadicIntNormAtPrime L q) ^ (-a) := by
      apply Finset.prod_congr rfl
      intro q hq
      letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
      unfold gramDetPadicNormFactorAtPrime
        gramDetPadicNormFactor
      change (‖(L.polarDeterminant : ℤ_[q.1])‖ ^ a)⁻¹ =
        ‖(L.polarDeterminant : ℤ_[q.1])‖ ^ (-a)
      rw [Real.rpow_neg (norm_nonneg _) a]
    _ = (∏ q ∈ Rat.padicNormPrimeSupport (L.polarDeterminant : ℚ),
          polarDeterminantPadicIntNormAtPrime L q) ^ (-a) := by
      exact Real.finset_prod_rpow _ _ hnonneg (-a)
    _ = ((L.polarDeterminant : ℝ)⁻¹) ^ (((n : ℝ) - 1) / 2) := by
      rw [L.prod_padicInt_norm_padicNormPrimeSupport_polarDeterminant]
      congr 1
      dsimp [a]
      ring

/-- The inverse Gram-factor product over the full bad-prime set has the same
closed reciprocal-discriminant value. -/
theorem prod_inv_gramDetPadicNormFactorAtPrime_bad
    (L : PositiveDefiniteIntegralLattice n) :
    (∏ q ∈ massBadPrimeSet L,
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((L.polarDeterminant : ℝ)⁻¹) ^ (((n : ℝ) - 1) / 2) := by
  rw [L.prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_support,
    L.prod_inv_gramDetPadicNormFactorAtPrime_support]

/-- In positive rank, the closed Gram-factor product is the reciprocal of the
ordinary `(n-1)`st power of the square root of the bilinear discriminant. -/
theorem prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_inv_sqrt_polarDeterminant_pow
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    (∏ q ∈ massBadPrimeSet L,
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((Real.sqrt (L.polarDeterminant : ℝ)) ^ (n - 1))⁻¹ := by
  rw [L.prod_inv_gramDetPadicNormFactorAtPrime_bad]
  have hdisc_nonneg : 0 ≤ (L.polarDeterminant : ℝ) := by
    exact_mod_cast (le_of_lt L.polarDeterminant_pos)
  rw [Real.inv_rpow hdisc_nonneg]
  rw [Real.rpow_div_two_eq_sqrt ((n : ℝ) - 1)
    hdisc_nonneg]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast, Real.rpow_natCast]

/-- Separating `polarDeterminant = 2^n * pairingDeterminant` makes the dyadic square-root layer in
the Gram-factor product explicit. -/
theorem prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_inv_sqrt_two_mul_pairingDeterminant_pow
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    (∏ q ∈ massBadPrimeSet L,
        (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (L.pairingDeterminant : ℝ)) ^
        (n - 1))⁻¹ := by
  rw [L.prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_inv_sqrt_polarDeterminant_pow]
  congr 2
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant]
  norm_num only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- Multiplying the inverse local Gram-factor product by the closed real
`pairingDeterminant` square-root factor cancels only the form determinant.  The dyadic
square-root layer remains literally. -/
theorem sqrt_pairingDeterminant_pow_mul_prod_inv_gramDetPadicNormFactorAtPrime_bad
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    (Real.sqrt (L.pairingDeterminant : ℝ)) ^ (n - 1) *
        (∏ q ∈ massBadPrimeSet L,
          (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1))⁻¹ := by
  rw [L.prod_inv_gramDetPadicNormFactorAtPrime_bad_eq_inv_sqrt_two_mul_pairingDeterminant_pow]
  rw [mul_pow]
  have hform : (Real.sqrt (L.pairingDeterminant : ℝ)) ^ (n - 1) ≠ 0 := by
    apply pow_ne_zero
    exact (Real.sqrt_pos.2 (by exact_mod_cast L.pairingDeterminant_pos)).ne'
  have htwo : (Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1) ≠ 0 := by
    positivity
  field_simp

/-- The previous cancellation in the exact determinant notation used by the
closed real differential theorem. -/
theorem rationalForm_sqrt_det_pow_mul_prod_inv_gramDetPadicNormFactorAtPrime_bad
    (L : PositiveDefiniteIntegralLattice n) [NeZero n] :
    (Real.sqrt |((L.rationalFormMatrix.det : ℚ) : ℝ)|) ^ (n - 1) *
        (∏ q ∈ massBadPrimeSet L,
          (gramDetPadicNormFactorAtPrime L q)⁻¹) =
      ((Real.sqrt ((2 : ℝ) ^ n)) ^ (n - 1))⁻¹ := by
  have hdet : L.rationalFormMatrix.det = (L.pairingDeterminant : ℚ) := by
    simpa [rationalFormMatrix, pairingDeterminant] using
      (RingHom.map_det (Int.castRingHom ℚ) L.pairingMatrix).symm
  rw [hdet]
  norm_num only [Rat.cast_intCast]
  rw [abs_of_pos (by exact_mod_cast L.pairingDeterminant_pos)]
  exact L.sqrt_pairingDeterminant_pow_mul_prod_inv_gramDetPadicNormFactorAtPrime_bad

end PositiveDefiniteIntegralLattice
