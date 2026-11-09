import SMSFormula.Genus
import Mathlib.Data.Nat.Factorization.Basic

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Taking determinants in one local isometry equation gives the expected
relation between Schulze--Pillot determinants over `ℤ_[p]`. -/
lemma pairingDeterminant_eq_det_sq_mul_of_local_isometry_matrix
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (U : Matrix (Fin n) (Fin n) ℤ_[p])
    (hU : Uᵀ * L'.pairingMatrix_padic p * U = L.pairingMatrix_padic p) :
    (L.pairingDeterminant : ℤ_[p]) = U.det ^ 2 * (L'.pairingDeterminant : ℤ_[p]) := by
  have hdet := congrArg Matrix.det hU
  have hdet' :
      (L.pairingDeterminant : ℤ_[p]) = U.det * (L'.pairingDeterminant : ℤ_[p]) * U.det := by
    simpa [pairingDeterminant, pairingMatrix_padic, Matrix.det_mul, Matrix.det_transpose,
      ← Int.cast_det]
      using hdet.symm
  calc
    (L.pairingDeterminant : ℤ_[p]) = U.det * (L'.pairingDeterminant : ℤ_[p]) * U.det := hdet'
    _ = U.det ^ 2 * (L'.pairingDeterminant : ℤ_[p]) := by ring

/-- A local isometry at `p` gives equality of determinants up to the square of
a `p`-adic unit. -/
lemma pairingDeterminant_eq_unit_sq_mul_of_isLocallyIsometricAt
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt L' p) :
    ∃ u : ℤ_[p], IsUnit u ∧
      (L.pairingDeterminant : ℤ_[p]) = u ^ 2 * (L'.pairingDeterminant : ℤ_[p]) := by
  obtain ⟨U, hU_unit, hU⟩ := h
  refine ⟨U.det, ?_, pairingDeterminant_eq_det_sq_mul_of_local_isometry_matrix L L' p U hU⟩
  rwa [Matrix.isUnit_iff_isUnit_det] at hU_unit

/-- Multiplying a Schulze--Pillot determinant by the square of a `p`-adic unit
does not change its `p`-adic integer norm. -/
lemma pairingDeterminant_padic_norm_eq_of_unit_sq_mul
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (u : ℤ_[p])
    (hu : IsUnit u)
    (hdet : (L.pairingDeterminant : ℤ_[p]) = u ^ 2 * (L'.pairingDeterminant : ℤ_[p])) :
    ‖(L.pairingDeterminant : ℤ_[p])‖ = ‖(L'.pairingDeterminant : ℤ_[p])‖ := by
  have hu_norm : ‖u ^ 2‖ = 1 := by
    rw [norm_pow, PadicInt.isUnit_iff.mp hu]
    norm_num
  rw [hdet, norm_mul, hu_norm, one_mul]

/-- Multiplying a Schulze--Pillot determinant by a square of a `p`-adic unit
preserves divisibility by every power of `p`. -/
lemma pairingDeterminant_prime_pow_dvd_iff_of_unit_sq_mul
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (u : ℤ_[p])
    (hu : IsUnit u)
    (hdet : (L.pairingDeterminant : ℤ_[p]) = u ^ 2 * (L'.pairingDeterminant : ℤ_[p])) (k : ℕ) :
    (p ^ k : ℤ) ∣ L.pairingDeterminant ↔ (p ^ k : ℤ) ∣ L'.pairingDeterminant := by
  have hnorm := pairingDeterminant_padic_norm_eq_of_unit_sq_mul L L' p u hu hdet
  rw [← PadicInt.norm_int_le_pow_iff_dvd, ← PadicInt.norm_int_le_pow_iff_dvd]
  rw [hnorm]

/-- A local isometry at `p` preserves the `p`-adic norm of the
Schulze--Pillot determinant. -/
lemma pairingDeterminant_padic_norm_eq_of_isLocallyIsometricAt
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt L' p) :
    ‖(L.pairingDeterminant : ℤ_[p])‖ = ‖(L'.pairingDeterminant : ℤ_[p])‖ := by
  obtain ⟨u, hu, hdet⟩ := pairingDeterminant_eq_unit_sq_mul_of_isLocallyIsometricAt L L' p h
  exact pairingDeterminant_padic_norm_eq_of_unit_sq_mul L L' p u hu hdet

/-- A local isometry at `p` preserves the `p`-adic norm of the bilinear Gram
determinant used in the Schulze--Pillot local-density factor. -/
lemma polarDeterminant_padic_norm_eq_of_isLocallyIsometricAt
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt L' p) :
    ‖(L.polarDeterminant : ℤ_[p])‖ = ‖(L'.polarDeterminant : ℤ_[p])‖ := by
  rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant, L'.polarDeterminant_eq_two_pow_mul_pairingDeterminant]
  rw [Int.cast_mul, Int.cast_mul, norm_mul, norm_mul]
  rw [pairingDeterminant_padic_norm_eq_of_isLocallyIsometricAt L L' p h]

/-- A local isometry at `p` preserves whether the bilinear Gram determinant is
a `p`-adic unit. -/
lemma polarDeterminant_padic_isUnit_iff_of_isLocallyIsometricAt
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt L' p) :
    IsUnit (L.polarDeterminant : ℤ_[p]) ↔ IsUnit (L'.polarDeterminant : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.isUnit_iff,
    polarDeterminant_padic_norm_eq_of_isLocallyIsometricAt L L' p h]

/-- A local isometry at `p` preserves the exact `p`-power divisibility profile
of the Schulze--Pillot determinant. -/
lemma pairingDeterminant_prime_pow_dvd_iff_of_isLocallyIsometricAt
    (L L' : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt L' p) (k : ℕ) :
    (p ^ k : ℤ) ∣ L.pairingDeterminant ↔ (p ^ k : ℤ) ∣ L'.pairingDeterminant := by
  obtain ⟨u, hu, hdet⟩ := pairingDeterminant_eq_unit_sq_mul_of_isLocallyIsometricAt L L' p h
  exact pairingDeterminant_prime_pow_dvd_iff_of_unit_sq_mul L L' p u hu hdet k

/-- Lattices in the same genus have the same `p`-power divisibility profile
for the Schulze--Pillot determinant at every prime `p`. -/
lemma pairingDeterminant_prime_pow_dvd_iff_of_isSameGenus
    (L L' : PositiveDefiniteIntegralLattice n) (h : L.IsSameGenus L')
    (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ) :
    (p ^ k : ℤ) ∣ L.pairingDeterminant ↔ (p ^ k : ℤ) ∣ L'.pairingDeterminant := by
  exact pairingDeterminant_prime_pow_dvd_iff_of_isLocallyIsometricAt L L' p (h.1 p) k

/-- If two nonzero integers have the same prime-power divisibility profile,
then their absolute values are equal. -/
lemma int_natAbs_eq_of_prime_pow_dvd_iff
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpow : ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ),
      (p ^ k : ℤ) ∣ a ↔ (p ^ k : ℤ) ∣ b) :
    a.natAbs = b.natAbs := by
  apply Nat.eq_of_factorization_eq (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
  intro p
  by_cases hp : Nat.Prime p
  · haveI : Fact (Nat.Prime p) := ⟨hp⟩
    apply le_antisymm
    · rw [← hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hb)]
      apply Int.natCast_dvd.mp
      exact (hpow p (a.natAbs.factorization p)).mp
        (Int.natCast_dvd.mpr
          ((hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr ha)).2 le_rfl))
    · rw [← hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr ha)]
      apply Int.natCast_dvd.mp
      exact (hpow p (b.natAbs.factorization p)).mpr
        (Int.natCast_dvd.mpr
          ((hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hb)).2 le_rfl))
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

/-- Local isometry at every prime gives equality of absolute
Schulze-Pillot determinants.

**Proof sketch** (Schulze-Pillot, lines 5312–5318): If `L, L'` are locally
isometric at every prime `p`, then `det(F_p) = det(U_p)² det(F'_p)` with
`det(U_p)` a `p`-adic unit for all `p`.  Hence `det(F) / det(F')` is a
rational number that is a `p`-adic unit for all primes, so equals `±1`. -/
theorem abs_pairingDeterminant_eq_of_isSameGenus (L L' : PositiveDefiniteIntegralLattice n)
    (h : L.IsSameGenus L') : |L.pairingDeterminant| = |L'.pairingDeterminant| := by
  have hpow_dvd :
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ),
        (p ^ k : ℤ) ∣ L.pairingDeterminant ↔ (p ^ k : ℤ) ∣ L'.pairingDeterminant := by
    intro p hp k
    exact pairingDeterminant_prime_pow_dvd_iff_of_isSameGenus L L' h p k
  have hnat :=
    int_natAbs_eq_of_prime_pow_dvd_iff L.pairingDeterminant L'.pairingDeterminant
      (ne_of_gt L.pairingDeterminant_pos) (ne_of_gt L'.pairingDeterminant_pos) hpow_dvd
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast hnat

/-- Lattices in the same genus have equal Schulze-Pillot determinant `det_B`.

This is the positive-definite sign step after the local arithmetic argument
`abs_pairingDeterminant_eq_of_isSameGenus`: both determinants are positive by
`PositiveDefiniteIntegralLattice.pairingDeterminant_pos`, so equality up to sign is equality. -/
theorem pairingDeterminant_eq_of_isSameGenus (L L' : PositiveDefiniteIntegralLattice n)
    (h : L.IsSameGenus L') : L.pairingDeterminant = L'.pairingDeterminant := by
  have h_abs := abs_pairingDeterminant_eq_of_isSameGenus L L' h
  simpa [abs_of_pos (L.pairingDeterminant_pos), abs_of_pos (L'.pairingDeterminant_pos)] using h_abs

end PositiveDefiniteIntegralLattice

end
