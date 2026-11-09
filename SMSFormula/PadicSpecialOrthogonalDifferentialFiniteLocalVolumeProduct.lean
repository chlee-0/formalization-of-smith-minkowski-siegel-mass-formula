import SMSFormula.PadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct

/-!
# Finite products of the corrected p-adic stabilizer volumes

The internally constructed corrected special-stabilizer volume at every prime
is the combined local correction times `ENNReal.ofReal normalizedLocalDensity`.
This module installs the local prime instance through the rational-prime
subtype and multiplies that pointwise identity over an arbitrary finite set.

When the finite set contains the explicit correction support, its correction
factor is replaced by the canonical finite correction product.  All products
remain direct `ENNReal` products.  No inverse or restricted product, real
place, reference Haar comparison, or Tamagawa theorem is used.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The corrected differential special-stabilizer volume indexed by the
subtype of rational primes. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  L.localPadicSpecialOrthogonalDifferentialStabilizerVolume q.1

/-- The `ENNReal` Schulze--Pillot local density indexed by the subtype of
rational primes. -/
noncomputable def
    normalizedLocalDensityENNRealAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  ENNReal.ofReal (normalizedLocalDensity L q.1)

/-- Every subtype-indexed corrected stabilizer volume is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q ≠ 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime] using
    (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_pos q.1).ne'

/-- Every subtype-indexed corrected stabilizer volume is finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q ≠ ⊤ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime] using
    (L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_lt_top q.1).ne

/-- Every subtype-indexed `ENNReal` Schulze--Pillot alpha is nonzero. -/
theorem normalizedLocalDensityENNRealAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.normalizedLocalDensityENNRealAtPrime q ≠ 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [normalizedLocalDensityENNRealAtPrime] using
    ENNReal.ofReal_ne_zero_iff.mpr (normalizedLocalDensity_pos L q.1)

/-- Every subtype-indexed `ENNReal` Schulze--Pillot alpha is finite. -/
theorem normalizedLocalDensityENNRealAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.normalizedLocalDensityENNRealAtPrime q ≠ ⊤ := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [normalizedLocalDensityENNRealAtPrime] using
    (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (normalizedLocalDensity L q.1) ≠ ⊤)

/-- The exact corrected local stabilizer-volume identity with all prime
instances hidden behind subtype-indexed factors. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_localCorrection_mul_normalizedLocalDensityENNRealAtPrime
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
        L.normalizedLocalDensityENNRealAtPrime q := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime,
    localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime,
    normalizedLocalDensityENNRealAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolume_eq_localCorrection_mul_ENNReal_ofReal_normalizedLocalDensity
      q.1

/-- A finite product of subtype-indexed corrected stabilizer volumes is
nonzero. -/
theorem
    prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) ≠
      0 := by
  exact Finset.prod_ne_zero_iff.mpr fun q _hq ↦
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero q

/-- A finite product of subtype-indexed corrected stabilizer volumes is
finite. -/
theorem
    prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) ≠
      ⊤ := by
  exact ENNReal.prod_ne_top fun q _hq ↦
    L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top q

/-- A finite product of subtype-indexed `ENNReal` Schulze--Pillot alpha
factors is nonzero. -/
theorem prod_normalizedLocalDensityENNRealAtPrime_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun q _hq ↦
    L.normalizedLocalDensityENNRealAtPrime_ne_zero q

/-- A finite product of subtype-indexed `ENNReal` Schulze--Pillot alpha
factors is finite. -/
theorem prod_normalizedLocalDensityENNRealAtPrime_ne_top
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q) ≠ ⊤ := by
  exact ENNReal.prod_ne_top fun q _hq ↦
    L.normalizedLocalDensityENNRealAtPrime_ne_top q

/-- Over an arbitrary finite prime set, the product of corrected
special-stabilizer volumes factors into the product of local corrections and
the product of `ENNReal` Schulze--Pillot alpha factors. -/
theorem
    prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_prod_localCorrection_mul_prod_normalizedLocalDensityENNRealAtPrime
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (S : Finset {p : ℕ // Nat.Prime p}) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) =
      (∏ q ∈ S,
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q) *
      ∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q := by
  calc
    (∏ q ∈ S,
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) =
        ∏ q ∈ S,
          (L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q *
            L.normalizedLocalDensityENNRealAtPrime q) := by
              apply Finset.prod_congr rfl
              intro q _hq
              exact
                L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_localCorrection_mul_normalizedLocalDensityENNRealAtPrime
                  q
    _ =
        (∏ q ∈ S,
          L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime q) *
        ∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q := by
          rw [Finset.prod_mul_distrib]

/-- Once a finite prime set contains the explicit correction support, the
finite corrected stabilizer-volume product has the canonical correction
product as its first factor. -/
theorem
    prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_localCorrectionFiniteProduct_mul_prod_normalizedLocalDensityENNRealAtPrime_of_subset
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (S : Finset {p : ℕ // Nat.Prime p})
    (hSupport :
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionPrimeSupport ⊆
        S) :
    (∏ q ∈ S,
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct *
        ∏ q ∈ S, L.normalizedLocalDensityENNRealAtPrime q := by
  rw [
    L.prod_localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_eq_prod_localCorrection_mul_prod_normalizedLocalDensityENNRealAtPrime
      S,
    L.prod_localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime_eq_finiteProduct_of_subset
      S hSupport]

end PositiveDefiniteIntegralLattice
