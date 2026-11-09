import SMSFormula.IntegralQuadraticFormOddPrimeDualQuotient

/-!
# Direct local factors of the integral quadratic form at odd primes

For an integral quadratic form `H`, this file defines the odd-prime fixed-depth
factor directly from the `Q_H` solution-family count in the intrinsic
`A`-dual quotient and from the p-adic norm of `det(A)`.  It then proves that
this direct expression equals the source-normalized local factor of the scaled
integral integral model.  The proof uses that two is a unit only under the explicit
hypothesis `p ≠ 2`.

No definition or comparison at the dyadic prime is made here.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Direct determinant and fixed-depth factors -/

/-- The determinant factor for the direct bilinear Gram matrix of the integral quadratic form
`A`, with the same visible real exponent as Schulze--Pillot's normalization. -/
noncomputable def polarGramDetPadicNormFactor
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  ‖(H.polarDeterminant : ℤ_[p])‖ ^ (((1 : ℝ) - (n : ℝ)) / 2)

/-- The direct odd-prime fixed-depth rational count factor.  Its count is
formed from `Q_H` on the intrinsic `A`-dual quotient.  The proof argument keeps
this API unavailable as an asserted dyadic normalization. -/
noncomputable def oddPrimeDirectFixedKDensityFactor
    (p k : ℕ) [Fact (Nat.Prime p)] (_hp_two : p ≠ 2) : ℚ :=
  (1 / 2 : ℚ) *
    ((p : ℚ) ^ PositiveDefiniteIntegralLattice.localDensityDenominatorExponent n k)⁻¹ *
    (H.polarDualQuotientCount p k : ℚ)

/-- The direct odd-prime fixed-depth density including the norm of `det(A)`. -/
noncomputable def oddPrimeDirectFixedKDensityWithPolarDetFactor
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) : ℝ :=
  (H.oddPrimeDirectFixedKDensityFactor p k hp_two : ℝ) *
    H.polarGramDetPadicNormFactor p

/-- At an odd prime, scaling `A` to the integral model Gram matrix `2A` does not
change its p-adic determinant norm. -/
theorem polarDeterminant_padicNorm_eq_latticeOfPolarForm_polarDeterminant_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖(H.polarDeterminant : ℤ_[p])‖ =
      ‖(H.latticeOfPolarForm.polarDeterminant : ℤ_[p])‖ := by
  rw [H.latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant]
  push_cast
  rw [norm_mul, norm_pow]
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    intro hp_dvd
    have hp_eq_two : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hp_dvd |>.resolve_left
        (Fact.out : Nat.Prime p).ne_one
    exact hp_two hp_eq_two
  have hcoprime : Nat.Coprime p 2 :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_not_dvd_two
  have htwo : ‖(2 : ℤ_[p])‖ = 1 :=
    (PadicInt.norm_natCast_eq_one_iff (p := p)).2 hcoprime
  change ‖(H.polarDeterminant : ℤ_[p])‖ =
    ‖(2 : ℤ_[p])‖ ^ n * ‖(H.polarDeterminant : ℤ_[p])‖
  rw [htwo, one_pow, one_mul]

/-- Consequently the direct `det(A)` factor equals the integral model's source
bilinear-Gram determinant factor at every odd prime. -/
theorem polarGramDetPadicNormFactor_eq_latticeOfPolarForm_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarGramDetPadicNormFactor p =
      PositiveDefiniteIntegralLattice.gramDetPadicNormFactor
        H.latticeOfPolarForm p := by
  unfold polarGramDetPadicNormFactor
    PositiveDefiniteIntegralLattice.gramDetPadicNormFactor
  rw [H.polarDeterminant_padicNorm_eq_latticeOfPolarForm_polarDeterminant_of_ne_two
    p hp_two]

/-! ## Comparison with the scaled integral model -/

/-- The direct rational fixed-depth factor equals the scaled integral model's
source-normalized factor at an odd prime. -/
theorem oddPrimeDirectFixedKDensityFactor_eq_latticeOfPolarForm
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.oddPrimeDirectFixedKDensityFactor p k hp_two =
      PositiveDefiniteIntegralLattice.fixedKDensityFactor
        H.latticeOfPolarForm p k := by
  rw [PositiveDefiniteIntegralLattice.fixedKDensityFactor_eq_localDualQuotientCount,
    PositiveDefiniteIntegralLattice.dualCountNormalizationFactor_eq_one_of_ne_two
      hp_two,
    PositiveDefiniteIntegralLattice.twoPadicNormInvPow_eq_one_of_ne_two hp_two,
    ← PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientCount_eq_current_of_ne_two
      H.latticeOfPolarForm p k hp_two,
    ← H.polarDualQuotientCount_eq_latticeOfPolarForm_associated_of_ne_two
      p k hp_two]
  unfold oddPrimeDirectFixedKDensityFactor
  ring

/-- The complete direct fixed-depth local factor equals the corresponding
scaled-integral model factor at every odd prime. -/
theorem oddPrimeDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.oddPrimeDirectFixedKDensityWithPolarDetFactor p k hp_two =
      PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor
        H.latticeOfPolarForm p k := by
  unfold oddPrimeDirectFixedKDensityWithPolarDetFactor
    PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor
  rw [H.oddPrimeDirectFixedKDensityFactor_eq_latticeOfPolarForm p k hp_two,
    H.polarGramDetPadicNormFactor_eq_latticeOfPolarForm_of_ne_two p hp_two]

/-- The direct odd-prime local density at the canonical stable exponent.  The
value is still built from the direct `Q_H` count and `det(A)` factor. -/
noncomputable def oddPrimeNormalizedLocalDensity
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) : ℝ :=
  H.oddPrimeDirectFixedKDensityWithPolarDetFactor p
    (PositiveDefiniteIntegralLattice.localDensityHenselExponent H.latticeOfPolarForm p)
    hp_two

/-- The direct odd-prime density equals the established local density of the
scaled integral model.  This theorem does not assert anything at `p=2`. -/
theorem oddPrimeNormalizedLocalDensity_eq_latticeOfPolarForm
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.oddPrimeNormalizedLocalDensity p hp_two =
      PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm p := by
  rw [oddPrimeNormalizedLocalDensity,
    H.oddPrimeDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm
      p (PositiveDefiniteIntegralLattice.localDensityHenselExponent H.latticeOfPolarForm p)
        hp_two]
  rfl

/-- Every source-valid integral model Hensel depth evaluates the same direct
odd-prime density.  This is the direct finite-count form of depth
independence, transported only after the fixed-depth comparison is proved. -/
theorem oddPrimeNormalizedLocalDensity_eq_fixedK
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hk : PositiveDefiniteIntegralLattice.IsLocalDensityHenselExponent
      H.latticeOfPolarForm p k) :
    H.oddPrimeNormalizedLocalDensity p hp_two =
      H.oddPrimeDirectFixedKDensityWithPolarDetFactor p k hp_two := by
  calc
    H.oddPrimeNormalizedLocalDensity p hp_two =
        PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm p :=
      H.oddPrimeNormalizedLocalDensity_eq_latticeOfPolarForm p hp_two
    _ = PositiveDefiniteIntegralLattice.normalizedLocalDensityAtExponent
        H.latticeOfPolarForm p k hk.admissible :=
      PositiveDefiniteIntegralLattice.normalizedLocalDensity_eq_fixedK
        H.latticeOfPolarForm p k hk
    _ = PositiveDefiniteIntegralLattice.fixedKDensityWithGramDetFactor
        H.latticeOfPolarForm p k := rfl
    _ = H.oddPrimeDirectFixedKDensityWithPolarDetFactor p k hp_two :=
      (H.oddPrimeDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm
        p k hp_two).symm

/-! ## Even-rank determinant square class -/

private theorem exists_sq_eq_sq_mul_iff
    {K : Type*} [Field K] (a x : K) (ha : a ≠ 0) :
    (∃ t : K, t ^ 2 = a ^ 2 * x) ↔ ∃ t : K, t ^ 2 = x := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / a, ?_⟩
    rw [div_pow, ht]
    field_simp [ha]
  · rintro ⟨t, ht⟩
    refine ⟨a * t, ?_⟩
    rw [mul_pow, ht]

/-- In dimension `2s`, the scaled integral model character target differs from the
direct polar-discriminant target by the displayed square `(2^s)^2`. -/
theorem evenCharacterTarget_latticeOfPolarForm_eq_square_mul_polar
    (s p : ℕ) [Fact (Nat.Prime p)] (H : PositiveDefiniteIntegralQuadraticForm (2 * s)) :
    ((-1 : ZMod p) ^ s) *
        ((H.latticeOfPolarForm.polarDeterminant : ℤ) : ZMod p) =
      ((2 : ZMod p) ^ s) ^ 2 *
        (((-1 : ZMod p) ^ s) * (H.polarDeterminant : ZMod p)) := by
  rw [H.latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant]
  push_cast
  have hpow : (2 : ZMod p) ^ (2 * s) = ((2 : ZMod p) ^ s) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [hpow]
  ring

/-- At an odd prime, the direct and scaled-integral model even character targets have
exactly the same square class.  Both implications retain explicit square-root
witnesses; the reverse direction divides only by the proved nonzero `2^s`. -/
theorem exists_sq_evenCharacterTarget_latticeOfPolarForm_iff_polar_of_ne_two
    (s p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (H : PositiveDefiniteIntegralQuadraticForm (2 * s)) :
    (∃ t : ZMod p,
        t ^ 2 = ((-1 : ZMod p) ^ s) *
          ((H.latticeOfPolarForm.polarDeterminant : ℤ) : ZMod p)) ↔
      ∃ t : ZMod p,
        t ^ 2 = ((-1 : ZMod p) ^ s) *
          (H.polarDeterminant : ZMod p) := by
  rw [H.evenCharacterTarget_latticeOfPolarForm_eq_square_mul_polar s p]
  apply exists_sq_eq_sq_mul_iff
  exact pow_ne_zero _ (by
    intro htwo
    have hp_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp htwo
    exact hp_two
      ((Nat.dvd_prime Nat.prime_two).mp hp_dvd |>.resolve_left
        (Fact.out : Nat.Prime p).ne_one))

/-- Nonsquareness of the even character target is likewise unchanged by the
integral model scaling at odd primes. -/
theorem forall_sq_ne_evenCharacterTarget_latticeOfPolarForm_iff_polar_of_ne_two
    (s p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (H : PositiveDefiniteIntegralQuadraticForm (2 * s)) :
    (∀ t : ZMod p,
        t ^ 2 ≠ ((-1 : ZMod p) ^ s) *
          ((H.latticeOfPolarForm.polarDeterminant : ℤ) : ZMod p)) ↔
      ∀ t : ZMod p,
        t ^ 2 ≠ ((-1 : ZMod p) ^ s) *
          (H.polarDeterminant : ZMod p) := by
  simpa only [not_exists] using not_congr
    (H.exists_sq_evenCharacterTarget_latticeOfPolarForm_iff_polar_of_ne_two
      s p hp_two)

end PositiveDefiniteIntegralQuadraticForm

end
