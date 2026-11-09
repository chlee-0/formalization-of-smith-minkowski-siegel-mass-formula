import SMSFormula.LocalDensityDefinitions
import SMSFormula.StandardAxiomsGuard

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite-prime Schulze--Pillot local factor used in the mass formula. -/
def massLocalFactor (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  normalizedLocalDensity L p

/-- The inverse local factor that appears in the product side of the ordinary
mass formula. -/
def massLocalInverseFactor (L : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  (massLocalFactor L p)⁻¹

/-- The same local factor indexed by the subtype of rational primes, convenient
for future prime-indexed products. -/
def massLocalFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  massLocalFactor L p.1

/-- The inverse local factor indexed by the subtype of rational primes. -/
def massLocalInverseFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (massLocalFactorAtPrime L p)⁻¹

/-- The finite product of inverse Schulze--Pillot local factors over a chosen
finite set of rational primes. -/
def massFinitePrimeInverseProduct (L : PositiveDefiniteIntegralLattice n)
    (S : Finset {p : ℕ // Nat.Prime p}) : ℝ :=
  S.prod fun p => massLocalInverseFactorAtPrime L p

/-- The finite set of rational primes bounded by a natural cutoff. -/
def rationalPrimesUpTo (N : ℕ) : Finset {p : ℕ // Nat.Prime p} :=
  ((Finset.range (N + 1)).filter Nat.Prime).attach.map
    ⟨fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩,
      by
        intro p q hpq
        have hpq_val : p.1 = q.1 :=
          congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hpq
        exact Subtype.ext hpq_val⟩

lemma mem_rationalPrimesUpTo_iff
    (N : ℕ) (q : {p : ℕ // Nat.Prime p}) :
    q ∈ rationalPrimesUpTo N ↔ q.1 ≤ N := by
  rw [rationalPrimesUpTo, Finset.mem_map]
  constructor
  · rintro ⟨p, _hp_attach, hpq⟩
    have hp_mem :
        p.1 ∈ (Finset.range (N + 1)).filter Nat.Prime := p.2
    have hp_lt : p.1 < N + 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hp_mem).1
    have hp_val : p.1 = q.1 :=
      congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hpq
    simpa [hp_val, Nat.lt_succ_iff] using hp_lt
  · intro hp
    let p :
        {x // x ∈ (Finset.range (N + 1)).filter Nat.Prime} :=
      ⟨q.1,
        Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp), q.2⟩⟩
    exact ⟨p, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The cutoff partial inverse product over rational primes `p ≤ N`. -/
def massPartialPrimeInverseProduct
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) : ℝ :=
  massFinitePrimeInverseProduct L (rationalPrimesUpTo N)

/-- The statement that the finite cutoff products of inverse local
Schulze--Pillot mass factors converge to the local product value used in the
adelic mass formula. -/
def massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => massPartialPrimeInverseProduct L N)
    Filter.atTop (nhds P)

#assert_standard_axioms massLocalFactor
#assert_standard_axioms massLocalInverseFactor
#assert_standard_axioms massLocalFactorAtPrime
#assert_standard_axioms massLocalInverseFactorAtPrime
#assert_standard_axioms massFinitePrimeInverseProduct
#assert_standard_axioms rationalPrimesUpTo
#assert_standard_axioms mem_rationalPrimesUpTo_iff
#assert_standard_axioms massPartialPrimeInverseProduct
#assert_standard_axioms massLocalInverseProductTendsTo

end PositiveDefiniteIntegralLattice
