import SMSFormula.ExactConductorFrequencies
import SMSFormula.RationalAdeleFiniteLocalTruncation

/-!
# The conductor filtration of the finite adeles

Three measure-theoretic items stand between the conductor-indexed summability and the finite-adelic
`L^1` integral.  Two of them are really structural, and this file settles that structure: which
frequencies clear a given conductor, that every frequency clears one, and that the exact conductor
-- when it exists -- is unique, so `the conductor of t` is a well-defined notion and not a choice.

The stratum is a dilate, exactly: `t` clears `m` precisely when `t = (1/m) s` for an integral `s`,
so the conductor-`m` frequencies are exactly `m^(-1) Zhat`, with the reciprocal frequency as the
dilating factor.  Both directions are one line, because `m` is a unit in the finite adeles.

The family is a filtration: clearing `m` implies clearing every multiple of `m`, so the strata are
directed along divisibility; and exhaustive, since the repository's own
`exists_natScale_mem_integral` gives every finite adele a natural denominator.  So the finite adeles
are the union of the `m^(-1) Zhat`, at the level of membership.

And exactness is exactly injectivity, an equivalence rather than the one implication recorded
before: the converse is immediate from the character's exact kernel, since a cleared `r` has
residue character value one, hence residue zero, hence is an `m`-multiple.  With it the exact
conductor is unique -- two exact conductors divide each other -- so no representative is chosen.

Negative scope.  No measure is computed: nothing evaluates the mass of a stratum, and nothing
identifies the local integral with the finite factor of the repository's adelic Bruhat coefficient.
Existence of an exact conductor is not proved either -- only its uniqueness and its equivalence with
injectivity.  No new object is introduced: the strata are described, not defined.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent Matrix

/-! ## The stratum is a dilate -/

/-- Clearing `m` is being an `m`-TH dilate of an integral element: the conductor-`m` frequencies
are exactly `m^(-1) Zhat`.  Both directions use only that `m` is a unit in the finite adeles. -/
theorem mul_natCast_mem_integral_iff (t : RationalFiniteAdele) (m : ℕ) (hm : m ≠ 0) :
    t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ↔
      ∃ s ∈ integralFiniteAdeleSubring, t = reciprocalFrequency m * s := by
  constructor
  · intro h
    refine ⟨t * (m : RationalFiniteAdele), h, ?_⟩
    symm
    calc reciprocalFrequency m * (t * (m : RationalFiniteAdele))
        = (reciprocalFrequency m * (m : RationalFiniteAdele)) * t := by ring
      _ = t := by rw [reciprocalFrequency_mul_natCast m hm, one_mul]
  · rintro ⟨s, hs, rfl⟩
    rw [show reciprocalFrequency m * s * (m : RationalFiniteAdele) =
      (reciprocalFrequency m * (m : RationalFiniteAdele)) * s from by ring,
      reciprocalFrequency_mul_natCast m hm, one_mul]
    exact hs

/-! ## The family is a filtration, and exhaustive -/

/-- Clearing `m` implies clearing every multiple, so the strata are directed along divisibility. -/
theorem mul_natCast_mem_integral_of_dvd (t : RationalFiniteAdele) {m m' : ℕ} (hdvd : m ∣ m')
    (h : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    t * (m' : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [show ((m * k : ℕ) : RationalFiniteAdele) =
    (m : RationalFiniteAdele) * (k : RationalFiniteAdele) by push_cast; ring, ← mul_assoc]
  exact Subring.mul_mem _ h (natCast_mem _ k)

/-- And every frequency clears some conductor -- the repository's own natural denominator.  So the
finite adeles are the union of the strata. -/
theorem exists_conductor (t : RationalFiniteAdele) :
    ∃ m : ℕ, m ≠ 0 ∧ t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by
  obtain ⟨N, hN, hmem⟩ := exists_natScale_mem_integral t
  exact ⟨N, hN, by rwa [mul_comm]⟩

/-- Stated as the union: every finite adele is an `m`-th dilate of an integral element. -/
theorem exists_reciprocalFrequency_representation (t : RationalFiniteAdele) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ s ∈ integralFiniteAdeleSubring, t = reciprocalFrequency m * s := by
  obtain ⟨m, hm, hmem⟩ := exists_conductor t
  exact ⟨m, hm, (mul_natCast_mem_integral_iff t m hm).1 hmem⟩

/-! ## Exactness is exactly injectivity -/

/-- The converse of the recorded implication, so the two are equivalent: injectivity of the residue
character is exactness of the conductor.  A cleared `r` has residue character value one, hence
residue zero by injectivity, hence is an `m`-multiple. -/
theorem hasExactConductor_of_injective (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m hm htm)) :
    HasExactConductor t m := by
  intro r hr
  refine (residueOf_eq_zero_iff m hm r).1 (hinj ?_)
  rw [residueChar_residueOf, (complexFiniteChar_eq_one_iff _).2 hr, residueChar_zero]

/-- The equivalence. -/
theorem hasExactConductor_iff_injective (m : ℕ) (hm : m ≠ 0) {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    HasExactConductor t m ↔ Function.Injective (residueChar m hm htm) :=
  ⟨injective_residueChar m hm htm, hasExactConductor_of_injective m hm htm⟩

/-! ## The exact conductor is unique -/

/-- An exact conductor divides every cleared conductor. -/
theorem dvd_of_hasExactConductor {t : RationalFiniteAdele} {m m' : ℕ} (hm : m ≠ 0)
    (hex : HasExactConductor t m)
    (hc' : t * (m' : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    (m : ℤ) ∣ (m' : ℤ) := by
  have hcoe : ((integerToIntegralFiniteAdele (m' : ℤ) : IntegralFiniteAdele) :
      RationalFiniteAdele) = (m' : RationalFiniteAdele) := by
    rw [integerToIntegralFiniteAdele_coe]; simp
  have hmem := hex (integerToIntegralFiniteAdele (m' : ℤ)) (by rw [hcoe]; exact hc')
  exact (integerToIntegralFiniteAdele_mem_natDilation_range_iff hm _).1 hmem

/-- Hence the exact conductor is unique, so `the conductor of t` names a number and not a choice. -/
theorem hasExactConductor_unique {t : RationalFiniteAdele} {m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hex : HasExactConductor t m) (hex' : HasExactConductor t m')
    (hc : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hc' : t * (m' : RationalFiniteAdele) ∈ integralFiniteAdeleSubring) :
    m = m' := by
  have h1 : (m : ℤ) ∣ (m' : ℤ) := dvd_of_hasExactConductor hm hex hc'
  have h2 : (m' : ℤ) ∣ (m : ℤ) := dvd_of_hasExactConductor hm' hex' hc
  have : m ∣ m' := by exact_mod_cast h1
  have : m' ∣ m := by exact_mod_cast h2
  exact Nat.dvd_antisymm ‹m ∣ m'› ‹m' ∣ m›

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
