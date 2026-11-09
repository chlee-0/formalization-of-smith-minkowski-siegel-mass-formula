import SMSFormula.RationalDyadicNorm
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Rational Hilbert reciprocity

This module begins the global Hilbert product formula by isolating the finite
set of rational primes where a local Hilbert factor can be nontrivial.
-/

noncomputable section

namespace Rat

/-- The product of the reduced numerator and denominator parts of two rational
inputs. Every finite prime where either input has nonzero valuation divides
this number. -/
def hilbertSupportNat (d c : ℚ) : ℕ :=
  d.num.natAbs * d.den * c.num.natAbs * c.den

/-- An integral representative of the rational square class of `q`. -/
def hilbertSquareClassInteger (q : ℚ) : ℤ :=
  q.num * q.den

lemma hilbertSquareClassInteger_ne_zero {q : ℚ} (hq : q ≠ 0) :
    hilbertSquareClassInteger q ≠ 0 := by
  apply mul_ne_zero
  · exact Rat.num_ne_zero.mpr hq
  · exact_mod_cast q.den_nz

/-- Multiplying a rational by the square of its denominator gives its integral
square-class representative. -/
lemma mul_den_sq_eq_hilbertSquareClassInteger (q : ℚ) :
    q * (q.den : ℚ) ^ 2 = (hilbertSquareClassInteger q : ℚ) := by
  calc
    q * (q.den : ℚ) ^ 2 =
        ((q.num : ℚ) / (q.den : ℚ)) * (q.den : ℚ) ^ 2 := by
      congr 1
      exact q.num_div_den.symm
    _ = (q.num : ℚ) * q.den := by field_simp
    _ = (hilbertSquareClassInteger q : ℚ) := by
      norm_cast

/-- The product of the prime factors occurring to odd multiplicity in `n`. -/
def hilbertSquarefreeKernel (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter fun p => Odd (n.factorization p), p

/-- The product carrying half of every prime multiplicity in `n`. -/
def hilbertSquareRootPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

private lemma pow_eq_parityKernel_mul_sq (a e : ℕ) :
    a ^ e = (if Odd e then a else 1) * (a ^ (e / 2)) ^ 2 := by
  by_cases hodd : Odd e
  · simp only [hodd, if_true]
    have hmod : e % 2 = 1 := Nat.odd_iff.mp hodd
    nth_rewrite 1 [← Nat.mod_add_div e 2]
    rw [hmod, pow_add, pow_one, mul_comm 2, pow_mul]
  · simp only [hodd, if_false, one_mul]
    have hmod : e % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one e with h | h
      · exact h
      · exact False.elim (hodd (Nat.odd_iff.mpr h))
    nth_rewrite 1 [← Nat.mod_add_div e 2]
    rw [hmod, zero_add, mul_comm 2, pow_mul]

theorem hilbertSquarefreeKernel_squarefree (n : ℕ) :
    Squarefree (hilbertSquarefreeKernel n) := by
  unfold hilbertSquarefreeKernel
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    apply (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).2
    exact hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hp).1).prime.squarefree

/-- A nonzero natural number is its squarefree kernel times the square of the
remaining half-exponent product. -/
theorem eq_hilbertSquarefreeKernel_mul_squareRootPart_sq
    {n : ℕ} (hn : n ≠ 0) :
    n = hilbertSquarefreeKernel n * hilbertSquareRootPart n ^ 2 := by
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact (Nat.factorization_prod_pow_eq_self hn).symm
    _ = ∏ p ∈ n.primeFactors,
          ((if Odd (n.factorization p) then p else 1) *
            (p ^ (n.factorization p / 2)) ^ 2) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact pow_eq_parityKernel_mul_sq p (n.factorization p)
    _ = hilbertSquarefreeKernel n * hilbertSquareRootPart n ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [hilbertSquarefreeKernel, hilbertSquareRootPart]
      congr 1
      rw [Finset.prod_filter]

/-- The odd natural part of the canonical signed integral representative. -/
def hilbertSquareClassOddPart (q : ℚ) : ℕ :=
  pFreeNatPart 2 (hilbertSquareClassInteger q).natAbs

/-- The odd squarefree kernel of the canonical integral representative. -/
def hilbertSquareClassOddKernel (q : ℚ) : ℕ :=
  hilbertSquarefreeKernel (hilbertSquareClassOddPart q)

lemma hilbertSquareClassOddPart_ne_zero {q : ℚ} (hq : q ≠ 0) :
    hilbertSquareClassOddPart q ≠ 0 := by
  have hnat : (hilbertSquareClassInteger q).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (hilbertSquareClassInteger_ne_zero hq)
  exact (Nat.ordCompl_pos 2 hnat).ne'

lemma two_not_dvd_hilbertSquareClassOddPart {q : ℚ} (hq : q ≠ 0) :
    ¬2 ∣ hilbertSquareClassOddPart q := by
  exact prime_not_dvd_pFreeNatPart Nat.prime_two
    (Int.natAbs_ne_zero.mpr (hilbertSquareClassInteger_ne_zero hq))

theorem hilbertSquareClassOddKernel_squarefree (q : ℚ) :
    Squarefree (hilbertSquareClassOddKernel q) :=
  hilbertSquarefreeKernel_squarefree _

theorem hilbertSquareClassOddKernel_ne_zero (q : ℚ) :
    hilbertSquareClassOddKernel q ≠ 0 :=
  (hilbertSquareClassOddKernel_squarefree q).ne_zero

theorem hilbertSquareClassOddPart_eq_kernel_mul_sq
    {q : ℚ} (hq : q ≠ 0) :
    hilbertSquareClassOddPart q = hilbertSquareClassOddKernel q *
      hilbertSquareRootPart (hilbertSquareClassOddPart q) ^ 2 :=
  eq_hilbertSquarefreeKernel_mul_squareRootPart_sq
    (hilbertSquareClassOddPart_ne_zero hq)

lemma two_not_dvd_hilbertSquareClassOddKernel {q : ℚ} (hq : q ≠ 0) :
    ¬2 ∣ hilbertSquareClassOddKernel q := by
  intro htwo
  apply two_not_dvd_hilbertSquareClassOddPart hq
  have hkDvd : hilbertSquareClassOddKernel q ∣ hilbertSquareClassOddPart q := by
    refine ⟨hilbertSquareRootPart (hilbertSquareClassOddPart q) ^ 2, ?_⟩
    exact hilbertSquareClassOddPart_eq_kernel_mul_sq hq
  exact htwo.trans hkDvd

theorem hilbertSquareClassOddKernel_odd {q : ℚ} (hq : q ≠ 0) :
    Odd (hilbertSquareClassOddKernel q) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact two_not_dvd_hilbertSquareClassOddKernel hq

/-- The squarefree dyadic factor of the canonical integral representative. -/
def hilbertSquareClassDyadicKernel (q : ℚ) : ℕ :=
  if Odd ((hilbertSquareClassInteger q).natAbs.factorization 2) then 2 else 1

/-- The natural square root removed from the canonical integral
representative. -/
def hilbertSquareClassRootPart (q : ℚ) : ℕ :=
  2 ^ ((hilbertSquareClassInteger q).natAbs.factorization 2 / 2) *
    hilbertSquareRootPart (hilbertSquareClassOddPart q)

/-- The signed squarefree representative obtained from the canonical integral
representative by removing every square prime power. -/
def hilbertSignedSquarefreeInteger (q : ℚ) : ℤ :=
  (hilbertSquareClassInteger q).sign * hilbertSquareClassDyadicKernel q *
    hilbertSquareClassOddKernel q

lemma hilbertSquareClassNatAbs_eq_dyadicKernel_mul_oddKernel_mul_root_sq
    {q : ℚ} (hq : q ≠ 0) :
    (hilbertSquareClassInteger q).natAbs =
      hilbertSquareClassDyadicKernel q * hilbertSquareClassOddKernel q *
        hilbertSquareClassRootPart q ^ 2 := by
  let z := hilbertSquareClassInteger q
  let m := z.natAbs
  let e := m.factorization 2
  have hsplit : 2 ^ e * pFreeNatPart 2 m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m 2
  have htwo : 2 ^ e = (if Odd e then 2 else 1) * (2 ^ (e / 2)) ^ 2 :=
    pow_eq_parityKernel_mul_sq 2 e
  have hodd := hilbertSquareClassOddPart_eq_kernel_mul_sq hq
  change pFreeNatPart 2 m = hilbertSquareClassOddKernel q *
    hilbertSquareRootPart (hilbertSquareClassOddPart q) ^ 2 at hodd
  change m = (if Odd e then 2 else 1) * hilbertSquareClassOddKernel q *
    (2 ^ (e / 2) * hilbertSquareRootPart (hilbertSquareClassOddPart q)) ^ 2
  calc
    m = 2 ^ e * pFreeNatPart 2 m := hsplit.symm
    _ = (if Odd e then 2 else 1) * hilbertSquareClassOddKernel q *
        (2 ^ (e / 2) *
          hilbertSquareRootPart (hilbertSquareClassOddPart q)) ^ 2 := by
      rw [htwo, hodd]
      ring

lemma hilbertSquareClassRootPart_ne_zero {q : ℚ} (hq : q ≠ 0) :
    hilbertSquareClassRootPart q ≠ 0 := by
  intro hroot
  have hnat :=
    hilbertSquareClassNatAbs_eq_dyadicKernel_mul_oddKernel_mul_root_sq hq
  have hmzero : (hilbertSquareClassInteger q).natAbs = 0 := by
    simpa [hroot] using hnat
  exact Int.natAbs_ne_zero.mpr (hilbertSquareClassInteger_ne_zero hq) hmzero

theorem hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq
    {q : ℚ} (hq : q ≠ 0) :
    hilbertSquareClassInteger q = hilbertSignedSquarefreeInteger q *
      (hilbertSquareClassRootPart q : ℤ) ^ 2 := by
  have hnat :=
    hilbertSquareClassNatAbs_eq_dyadicKernel_mul_oddKernel_mul_root_sq hq
  calc
    hilbertSquareClassInteger q = (hilbertSquareClassInteger q).sign *
        ((hilbertSquareClassInteger q).natAbs : ℤ) :=
      (Int.sign_mul_natAbs _).symm
    _ = hilbertSignedSquarefreeInteger q *
        (hilbertSquareClassRootPart q : ℤ) ^ 2 := by
      rw [hnat]
      push_cast
      simp only [hilbertSignedSquarefreeInteger]
      ring

/-- A nonzero rational is its canonical signed squarefree integer times the
square of the removed integral root divided by its denominator. -/
theorem eq_signedSquarefreeInteger_mul_rootPart_div_den_sq
    {q : ℚ} (hq : q ≠ 0) :
    q = (hilbertSignedSquarefreeInteger q : ℚ) *
      ((hilbertSquareClassRootPart q : ℚ) / q.den) ^ 2 := by
  have hclass : (hilbertSquareClassInteger q : ℚ) =
      (hilbertSignedSquarefreeInteger q : ℚ) *
        (hilbertSquareClassRootPart q : ℚ) ^ 2 := by
    exact_mod_cast hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hq
  calc
    q = (hilbertSquareClassInteger q : ℚ) / (q.den : ℚ) ^ 2 := by
      rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
      field_simp
    _ = ((hilbertSignedSquarefreeInteger q : ℚ) *
          (hilbertSquareClassRootPart q : ℚ) ^ 2) /
        (q.den : ℚ) ^ 2 := by rw [hclass]
    _ = (hilbertSignedSquarefreeInteger q : ℚ) *
        ((hilbertSquareClassRootPart q : ℚ) / q.den) ^ 2 := by
      field_simp

lemma hilbertSquareClassRootPart_div_den_ne_zero
    {q : ℚ} (hq : q ≠ 0) :
    (hilbertSquareClassRootPart q : ℚ) / q.den ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast hilbertSquareClassRootPart_ne_zero hq
  · exact_mod_cast q.den_nz

theorem hilbertSignedSquarefreeInteger_ne_zero {q : ℚ} (hq : q ≠ 0) :
    hilbertSignedSquarefreeInteger q ≠ 0 := by
  intro hrep
  have h := hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hq
  rw [hrep, zero_mul] at h
  exact hilbertSquareClassInteger_ne_zero hq h

theorem exists_signedSquarefreeInteger_mul_sq {q : ℚ} (hq : q ≠ 0) :
    ∃ s : ℤ, s ≠ 0 ∧ hilbertSquareClassInteger q =
      hilbertSignedSquarefreeInteger q * s ^ 2 := by
  refine ⟨hilbertSquareClassRootPart q, ?_,
    hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hq⟩
  exact_mod_cast hilbertSquareClassRootPart_ne_zero hq

lemma realHilbertSymbol_squareClassInteger_left (q b : ℚ) :
    realHilbertSymbol (hilbertSquareClassInteger q : ℚ) b =
      realHilbertSymbol q b := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact realHilbertSymbol_mul_sq_left q b q.den hden

lemma realHilbertSymbol_squareClassInteger_right (a q : ℚ) :
    realHilbertSymbol a (hilbertSquareClassInteger q : ℚ) =
      realHilbertSymbol a q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact realHilbertSymbol_mul_sq_right a q q.den hden

lemma oddPrimeHilbertSymbol_squareClassInteger_left
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (q b : ℚ) (hq : q ≠ 0) :
    oddPrimeHilbertSymbol p hpodd (hilbertSquareClassInteger q : ℚ) b =
      oddPrimeHilbertSymbol p hpodd q b := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact oddPrimeHilbertSymbol_mul_sq_left p hpodd q b q.den hq hden

lemma oddPrimeHilbertSymbol_squareClassInteger_right
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (a q : ℚ) (hq : q ≠ 0) :
    oddPrimeHilbertSymbol p hpodd a (hilbertSquareClassInteger q : ℚ) =
      oddPrimeHilbertSymbol p hpodd a q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact oddPrimeHilbertSymbol_mul_sq_right p hpodd a q q.den hq hden

lemma dyadicHilbertSymbol_squareClassInteger_left
    (q b : ℚ) (hq : q ≠ 0) :
    dyadicHilbertSymbol (hilbertSquareClassInteger q : ℚ) b =
      dyadicHilbertSymbol q b := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact dyadicHilbertSymbol_mul_sq_left q b q.den hq hden

lemma dyadicHilbertSymbol_squareClassInteger_right
    (a q : ℚ) (hq : q ≠ 0) :
    dyadicHilbertSymbol a (hilbertSquareClassInteger q : ℚ) =
      dyadicHilbertSymbol a q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← mul_den_sq_eq_hilbertSquareClassInteger q]
  exact dyadicHilbertSymbol_mul_sq_right a q q.den hq hden

private def primeFactorsAsPrimes (n : ℕ) :
    Finset {p : ℕ // p.Prime} :=
  (n.primeFactors.attach).map
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
      by
        intro p q hpq
        exact Subtype.ext
          (congrArg (fun r : {p : ℕ // p.Prime} => r.1) hpq)⟩

/-- The finite set containing the dyadic prime and every prime dividing a
reduced numerator or denominator of either rational input. -/
def hilbertBadPrimeSet (d c : ℚ) : Finset {p : ℕ // p.Prime} :=
  insert ⟨2, Nat.prime_two⟩ (primeFactorsAsPrimes (hilbertSupportNat d c))

lemma hilbertSupportNat_ne_zero {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    hilbertSupportNat d c ≠ 0 := by
  have hdnum : d.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hd
  have hcnum : c.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hc
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hdnum d.den_nz) hcnum) c.den_nz

lemma mem_hilbertBadPrimeSet_iff {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : {p : ℕ // p.Prime}) :
    p ∈ hilbertBadPrimeSet d c ↔
      p.1 = 2 ∨ p.1 ∣ hilbertSupportNat d c := by
  have hsupp : hilbertSupportNat d c ≠ 0 := hilbertSupportNat_ne_zero hd hc
  simp only [hilbertBadPrimeSet, primeFactorsAsPrimes, Finset.mem_insert,
    Finset.mem_map, Finset.mem_attach]
  constructor
  · rintro (hp | ⟨q, _hq, hqp⟩)
    · exact Or.inl (congrArg Subtype.val hp)
    · refine Or.inr ?_
      have hqmem : q.1 ∈ (hilbertSupportNat d c).primeFactors := q.2
      have hqdvd : q.1 ∣ hilbertSupportNat d c :=
        (Nat.mem_primeFactors.mp hqmem).2.1
      have hqval : q.1 = p.1 := congrArg Subtype.val hqp
      simpa [hqval] using hqdvd
  · rintro (hp | hp)
    · exact Or.inl (Subtype.ext hp)
    · exact Or.inr
        ⟨⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hp, hsupp⟩⟩,
          trivial, Subtype.ext rfl⟩

private lemma padicValRat_eq_zero_of_not_dvd_num_den
    {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hnum : ¬p ∣ q.num.natAbs) (hden : ¬p ∣ q.den) :
    padicValRat p q = 0 := by
  rw [padicValRat_def, padicValInt,
    ← Nat.factorization_def _ (Fact.out : p.Prime),
    ← Nat.factorization_def _ (Fact.out : p.Prime),
    Nat.factorization_eq_zero_of_not_dvd hnum,
    Nat.factorization_eq_zero_of_not_dvd hden]
  norm_num

/-- Outside the bad-prime set, both rational inputs have valuation parity
zero. -/
lemma valuationParity_eq_zero_of_not_mem_hilbertBadPrimeSet
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : {p : ℕ // p.Prime}) (hp : p ∉ hilbertBadPrimeSet d c) :
    valuationParity p.1 d = 0 ∧ valuationParity p.1 c = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hpndvd : ¬p.1 ∣ hilbertSupportNat d c := by
    intro hpdvd
    exact hp ((mem_hilbertBadPrimeSet_iff hd hc p).2 (Or.inr hpdvd))
  have hpdnum : ¬p.1 ∣ d.num.natAbs := by
    intro h
    apply hpndvd
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h d.den) c.num.natAbs) c.den
  have hpdden : ¬p.1 ∣ d.den := by
    intro h
    apply hpndvd
    simpa [hilbertSupportNat, mul_assoc] using
      (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right h d.num.natAbs) (c.num.natAbs * c.den))
  have hpcnum : ¬p.1 ∣ c.num.natAbs := by
    intro h
    apply hpndvd
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right h (d.num.natAbs * d.den)) c.den
  have hpcden : ¬p.1 ∣ c.den := by
    intro h
    apply hpndvd
    exact dvd_mul_of_dvd_right h (d.num.natAbs * d.den * c.num.natAbs)
  have hdval : padicValRat p.1 d = 0 :=
    padicValRat_eq_zero_of_not_dvd_num_den hpdnum hpdden
  have hcval : padicValRat p.1 c = 0 :=
    padicValRat_eq_zero_of_not_dvd_num_den hpcnum hpcden
  simp [valuationParity, hdval, hcval]

/-- The rational finite-prime Hilbert factor, using the dyadic formula at two
and the odd-prime formula at every other rational prime. -/
def finiteHilbertFactor (d c : ℚ) (p : {p : ℕ // p.Prime}) : ℤ :=
  if hp : p.1 = 2 then
    dyadicHilbertSymbol d c
  else
    letI : Fact p.1.Prime := ⟨p.2⟩
    oddPrimeHilbertSymbol p.1 hp d c

lemma finiteHilbertFactor_squareClassInteger_left
    (q b : ℚ) (hq : q ≠ 0) (p : {p : ℕ // p.Prime}) :
    finiteHilbertFactor (hilbertSquareClassInteger q : ℚ) b p =
      finiteHilbertFactor q b p := by
  unfold finiteHilbertFactor
  split
  · exact dyadicHilbertSymbol_squareClassInteger_left q b hq
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimeHilbertSymbol_squareClassInteger_left p.1 _ q b hq

lemma finiteHilbertFactor_squareClassInteger_right
    (a q : ℚ) (hq : q ≠ 0) (p : {p : ℕ // p.Prime}) :
    finiteHilbertFactor a (hilbertSquareClassInteger q : ℚ) p =
      finiteHilbertFactor a q p := by
  unfold finiteHilbertFactor
  split
  · exact dyadicHilbertSymbol_squareClassInteger_right a q hq
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimeHilbertSymbol_squareClassInteger_right p.1 _ a q hq

lemma finiteHilbertFactor_mul_sq_left
    (a b x : ℚ) (ha : a ≠ 0) (hx : x ≠ 0)
    (p : {p : ℕ // p.Prime}) :
    finiteHilbertFactor (a * x ^ 2) b p = finiteHilbertFactor a b p := by
  unfold finiteHilbertFactor
  split
  · exact dyadicHilbertSymbol_mul_sq_left a b x ha hx
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimeHilbertSymbol_mul_sq_left p.1 _ a b x ha hx

lemma finiteHilbertFactor_mul_sq_right
    (a b y : ℚ) (hb : b ≠ 0) (hy : y ≠ 0)
    (p : {p : ℕ // p.Prime}) :
    finiteHilbertFactor a (b * y ^ 2) p = finiteHilbertFactor a b p := by
  unfold finiteHilbertFactor
  split
  · exact dyadicHilbertSymbol_mul_sq_right a b y hb hy
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimeHilbertSymbol_mul_sq_right p.1 _ a b y hb hy

/-- Every finite-prime Hilbert factor outside the explicit bad-prime set is
one. -/
theorem finiteHilbertFactor_eq_one_of_not_mem_hilbertBadPrimeSet
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : {p : ℕ // p.Prime}) (hp : p ∉ hilbertBadPrimeSet d c) :
    finiteHilbertFactor d c p = 1 := by
  have hpodd : p.1 ≠ 2 := by
    intro hp2
    exact hp ((mem_hilbertBadPrimeSet_iff hd hc p).2 (Or.inl hp2))
  letI : Fact p.1.Prime := ⟨p.2⟩
  obtain ⟨hdpar, hcpar⟩ :=
    valuationParity_eq_zero_of_not_mem_hilbertBadPrimeSet hd hc p hp
  rw [finiteHilbertFactor, dif_neg hpodd]
  exact oddPrimeHilbertSymbol_eq_one_of_valuationParity_eq_zero
    p.1 d c hpodd hdpar hcpar

/-- A finite product of rational finite-prime Hilbert factors. -/
def finiteHilbertProduct (d c : ℚ) (S : Finset {p : ℕ // p.Prime}) : ℤ :=
  ∏ p ∈ S, finiteHilbertFactor d c p

/-- Simultaneous integral square-class normalization leaves every supplied
finite prime product unchanged. -/
lemma finiteHilbertProduct_squareClassIntegers
    (d c : ℚ) (hd : d ≠ 0) (hc : c ≠ 0)
    (S : Finset {p : ℕ // p.Prime}) :
    finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) S =
      finiteHilbertProduct d c S := by
  unfold finiteHilbertProduct
  apply Finset.prod_congr rfl
  intro p _hp
  exact (finiteHilbertFactor_squareClassInteger_left d
      (hilbertSquareClassInteger c : ℚ) hd p).trans
    (finiteHilbertFactor_squareClassInteger_right d c hc p)

lemma finiteHilbertProduct_mul_sqs
    (a b x y : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (S : Finset {p : ℕ // p.Prime}) :
    finiteHilbertProduct (a * x ^ 2) (b * y ^ 2) S =
      finiteHilbertProduct a b S := by
  unfold finiteHilbertProduct
  apply Finset.prod_congr rfl
  intro p _hp
  exact (finiteHilbertFactor_mul_sq_left a (b * y ^ 2) x ha hx p).trans
    (finiteHilbertFactor_mul_sq_right a b y hb hy p)

/-- The exact finite rational Hilbert product formula remaining after the
finite-support reduction. -/
def HilbertProductFormula (d c : ℚ) : Prop :=
  realHilbertSymbol d c *
    finiteHilbertProduct d c (hilbertBadPrimeSet d c) = 1

/-- Enlarging the explicit bad-prime set does not change the finite Hilbert
product. -/
lemma finiteHilbertProduct_eq_badPrimeSet_of_subset
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    {S : Finset {p : ℕ // p.Prime}}
    (hsub : hilbertBadPrimeSet d c ⊆ S) :
    finiteHilbertProduct d c S =
      finiteHilbertProduct d c (hilbertBadPrimeSet d c) := by
  unfold finiteHilbertProduct
  exact (Finset.prod_subset hsub (by
    intro p _hpS hpbad
    exact finiteHilbertFactor_eq_one_of_not_mem_hilbertBadPrimeSet
      hd hc p hpbad)).symm

/-- The bad-prime product itself is unchanged by simultaneous integral
square-class normalization, even though the chosen support finsets may differ. -/
lemma finiteHilbertProduct_badPrimeSet_squareClassIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSquareClassInteger d : ℚ)
          (hilbertSquareClassInteger c : ℚ)) =
      finiteHilbertProduct d c (hilbertBadPrimeSet d c) := by
  have hdInt : (hilbertSquareClassInteger d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassInteger_ne_zero hd
  have hcInt : (hilbertSquareClassInteger c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassInteger_ne_zero hc
  let S := hilbertBadPrimeSet d c ∪
    hilbertBadPrimeSet (hilbertSquareClassInteger d : ℚ)
      (hilbertSquareClassInteger c : ℚ)
  have horig : finiteHilbertProduct d c S =
      finiteHilbertProduct d c (hilbertBadPrimeSet d c) :=
    finiteHilbertProduct_eq_badPrimeSet_of_subset hd hc Finset.subset_union_left
  have hInt : finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) S =
      finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSquareClassInteger d : ℚ)
          (hilbertSquareClassInteger c : ℚ)) :=
    finiteHilbertProduct_eq_badPrimeSet_of_subset hdInt hcInt
      Finset.subset_union_right
  calc
    finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSquareClassInteger d : ℚ)
          (hilbertSquareClassInteger c : ℚ)) =
      finiteHilbertProduct (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) S := hInt.symm
    _ = finiteHilbertProduct d c S :=
      finiteHilbertProduct_squareClassIntegers d c hd hc S
    _ = finiteHilbertProduct d c (hilbertBadPrimeSet d c) := horig

lemma finiteHilbertProduct_badPrimeSet_mul_sqs
    {a b x y : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteHilbertProduct (a * x ^ 2) (b * y ^ 2)
        (hilbertBadPrimeSet (a * x ^ 2) (b * y ^ 2)) =
      finiteHilbertProduct a b (hilbertBadPrimeSet a b) := by
  have hax : a * x ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hx)
  have hby : b * y ^ 2 ≠ 0 := mul_ne_zero hb (pow_ne_zero 2 hy)
  let S := hilbertBadPrimeSet a b ∪
    hilbertBadPrimeSet (a * x ^ 2) (b * y ^ 2)
  have horig : finiteHilbertProduct a b S =
      finiteHilbertProduct a b (hilbertBadPrimeSet a b) :=
    finiteHilbertProduct_eq_badPrimeSet_of_subset ha hb Finset.subset_union_left
  have hscaled : finiteHilbertProduct (a * x ^ 2) (b * y ^ 2) S =
      finiteHilbertProduct (a * x ^ 2) (b * y ^ 2)
        (hilbertBadPrimeSet (a * x ^ 2) (b * y ^ 2)) :=
    finiteHilbertProduct_eq_badPrimeSet_of_subset hax hby
      Finset.subset_union_right
  calc
    finiteHilbertProduct (a * x ^ 2) (b * y ^ 2)
        (hilbertBadPrimeSet (a * x ^ 2) (b * y ^ 2)) =
      finiteHilbertProduct (a * x ^ 2) (b * y ^ 2) S := hscaled.symm
    _ = finiteHilbertProduct a b S :=
      finiteHilbertProduct_mul_sqs a b x y ha hb hx hy S
    _ = finiteHilbertProduct a b (hilbertBadPrimeSet a b) := horig

theorem hilbertProductFormula_mul_sqs_iff
    {a b x y : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    HilbertProductFormula (a * x ^ 2) (b * y ^ 2) ↔
      HilbertProductFormula a b := by
  have hreal : realHilbertSymbol (a * x ^ 2) (b * y ^ 2) =
      realHilbertSymbol a b :=
    (realHilbertSymbol_mul_sq_left a (b * y ^ 2) x hx).trans
      (realHilbertSymbol_mul_sq_right a b y hy)
  have hfinite := finiteHilbertProduct_badPrimeSet_mul_sqs ha hb hx hy
  unfold HilbertProductFormula
  rw [hreal, hfinite]

/-- The rational Hilbert product formula is equivalent to its restriction to
the canonical integral representatives of both rational square classes. -/
theorem hilbertProductFormula_iff_squareClassIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    HilbertProductFormula d c ↔
      HilbertProductFormula (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) := by
  have hreal : realHilbertSymbol (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) = realHilbertSymbol d c :=
    (realHilbertSymbol_squareClassInteger_left d
      (hilbertSquareClassInteger c : ℚ)).trans
      (realHilbertSymbol_squareClassInteger_right d c)
  have hfinite := finiteHilbertProduct_badPrimeSet_squareClassIntegers hd hc
  unfold HilbertProductFormula
  rw [hreal, hfinite]

/-- The rational Hilbert product formula is equivalent to its restriction to
the canonical signed squarefree representatives of both inputs. -/
theorem hilbertProductFormula_iff_signedSquarefreeIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    HilbertProductFormula d c ↔
      HilbertProductFormula (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) := by
  have hdEq : (hilbertSquareClassInteger d : ℚ) =
      (hilbertSignedSquarefreeInteger d : ℚ) *
        (hilbertSquareClassRootPart d : ℚ) ^ 2 := by
    exact_mod_cast hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hd
  have hcEq : (hilbertSquareClassInteger c : ℚ) =
      (hilbertSignedSquarefreeInteger c : ℚ) *
        (hilbertSquareClassRootPart c : ℚ) ^ 2 := by
    exact_mod_cast hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hc
  have hdrep : (hilbertSignedSquarefreeInteger d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hd
  have hcrep : (hilbertSignedSquarefreeInteger c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hc
  have hdroot : (hilbertSquareClassRootPart d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassRootPart_ne_zero hd
  have hcroot : (hilbertSquareClassRootPart c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassRootPart_ne_zero hc
  apply (hilbertProductFormula_iff_squareClassIntegers hd hc).trans
  rw [hdEq, hcEq]
  exact hilbertProductFormula_mul_sqs_iff hdrep hcrep hdroot hcroot

/-- The common odd factor of the two canonical squarefree kernels. -/
def hilbertCommonOddKernel (d c : ℚ) : ℕ :=
  Nat.gcd (hilbertSquareClassOddKernel d) (hilbertSquareClassOddKernel c)

/-- The part of the left odd kernel remaining after removing the common
factor. -/
def hilbertLeftOddKernelRemainder (d c : ℚ) : ℕ :=
  hilbertSquareClassOddKernel d / hilbertCommonOddKernel d c

/-- The part of the right odd kernel remaining after removing the common
factor. -/
def hilbertRightOddKernelRemainder (d c : ℚ) : ℕ :=
  hilbertSquareClassOddKernel c / hilbertCommonOddKernel d c

theorem oddKernel_eq_common_mul_leftRemainder (d c : ℚ) :
    hilbertSquareClassOddKernel d = hilbertCommonOddKernel d c *
      hilbertLeftOddKernelRemainder d c :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_left
    (hilbertSquareClassOddKernel d) (hilbertSquareClassOddKernel c))).symm

theorem oddKernel_eq_common_mul_rightRemainder (d c : ℚ) :
    hilbertSquareClassOddKernel c = hilbertCommonOddKernel d c *
      hilbertRightOddKernelRemainder d c :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_right
    (hilbertSquareClassOddKernel d) (hilbertSquareClassOddKernel c))).symm

lemma hilbertLeftOddKernelRemainder_dvd (d c : ℚ) :
    hilbertLeftOddKernelRemainder d c ∣ hilbertSquareClassOddKernel d := by
  refine ⟨hilbertCommonOddKernel d c, ?_⟩
  rw [mul_comm]
  exact oddKernel_eq_common_mul_leftRemainder d c

lemma hilbertRightOddKernelRemainder_dvd (d c : ℚ) :
    hilbertRightOddKernelRemainder d c ∣ hilbertSquareClassOddKernel c := by
  refine ⟨hilbertCommonOddKernel d c, ?_⟩
  rw [mul_comm]
  exact oddKernel_eq_common_mul_rightRemainder d c

theorem hilbertCommonOddKernel_ne_zero (d c : ℚ) :
    hilbertCommonOddKernel d c ≠ 0 := by
  exact (Nat.gcd_pos_of_pos_left _
    (Nat.pos_of_ne_zero (hilbertSquareClassOddKernel_ne_zero d))).ne'

theorem hilbertLeftOddKernelRemainder_ne_zero (d c : ℚ) :
    hilbertLeftOddKernelRemainder d c ≠ 0 := by
  have hk := hilbertSquareClassOddKernel_ne_zero d
  have hgpos : 0 < hilbertCommonOddKernel d c :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hk)
  apply (Nat.div_pos ?_ hgpos).ne'
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_left _ _)

theorem hilbertRightOddKernelRemainder_ne_zero (d c : ℚ) :
    hilbertRightOddKernelRemainder d c ≠ 0 := by
  have hk := hilbertSquareClassOddKernel_ne_zero c
  have hgpos : 0 < hilbertCommonOddKernel d c :=
    Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk)
  apply (Nat.div_pos ?_ hgpos).ne'
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_right _ _)

theorem hilbertOddKernelFactors_ne_zero (d c : ℚ) :
    hilbertCommonOddKernel d c ≠ 0 ∧
      hilbertLeftOddKernelRemainder d c ≠ 0 ∧
      hilbertRightOddKernelRemainder d c ≠ 0 :=
  ⟨hilbertCommonOddKernel_ne_zero d c,
    hilbertLeftOddKernelRemainder_ne_zero d c,
    hilbertRightOddKernelRemainder_ne_zero d c⟩

theorem hilbertCommonOddKernel_squarefree (d c : ℚ) :
    Squarefree (hilbertCommonOddKernel d c) :=
  Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
    (hilbertSquareClassOddKernel_squarefree d)

theorem hilbertLeftOddKernelRemainder_squarefree (d c : ℚ) :
    Squarefree (hilbertLeftOddKernelRemainder d c) :=
  Squarefree.squarefree_of_dvd (hilbertLeftOddKernelRemainder_dvd d c)
    (hilbertSquareClassOddKernel_squarefree d)

theorem hilbertRightOddKernelRemainder_squarefree (d c : ℚ) :
    Squarefree (hilbertRightOddKernelRemainder d c) :=
  Squarefree.squarefree_of_dvd (hilbertRightOddKernelRemainder_dvd d c)
    (hilbertSquareClassOddKernel_squarefree c)

theorem hilbertOddKernelFactors_squarefree (d c : ℚ) :
    Squarefree (hilbertCommonOddKernel d c) ∧
      Squarefree (hilbertLeftOddKernelRemainder d c) ∧
      Squarefree (hilbertRightOddKernelRemainder d c) :=
  ⟨hilbertCommonOddKernel_squarefree d c,
    hilbertLeftOddKernelRemainder_squarefree d c,
    hilbertRightOddKernelRemainder_squarefree d c⟩

theorem hilbertCommonOddKernel_odd {d c : ℚ} (hd : d ≠ 0) :
    Odd (hilbertCommonOddKernel d c) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro htwo
  exact two_not_dvd_hilbertSquareClassOddKernel hd
    (htwo.trans (Nat.gcd_dvd_left _ _))

theorem hilbertLeftOddKernelRemainder_odd
    {d c : ℚ} (hd : d ≠ 0) :
    Odd (hilbertLeftOddKernelRemainder d c) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro htwo
  exact two_not_dvd_hilbertSquareClassOddKernel hd
    (htwo.trans (hilbertLeftOddKernelRemainder_dvd d c))

theorem hilbertRightOddKernelRemainder_odd
    {d c : ℚ} (hc : c ≠ 0) :
    Odd (hilbertRightOddKernelRemainder d c) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro htwo
  exact two_not_dvd_hilbertSquareClassOddKernel hc
    (htwo.trans (hilbertRightOddKernelRemainder_dvd d c))

theorem hilbertOddKernelFactors_odd
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    Odd (hilbertCommonOddKernel d c) ∧
      Odd (hilbertLeftOddKernelRemainder d c) ∧
      Odd (hilbertRightOddKernelRemainder d c) :=
  ⟨hilbertCommonOddKernel_odd hd,
    hilbertLeftOddKernelRemainder_odd hd,
    hilbertRightOddKernelRemainder_odd hc⟩

theorem hilbertOddKernelFactors_pairwise_coprime (d c : ℚ) :
    Nat.Coprime (hilbertCommonOddKernel d c)
        (hilbertLeftOddKernelRemainder d c) ∧
      Nat.Coprime (hilbertCommonOddKernel d c)
        (hilbertRightOddKernelRemainder d c) ∧
      Nat.Coprime (hilbertLeftOddKernelRemainder d c)
        (hilbertRightOddKernelRemainder d c) := by
  have hga : Nat.Coprime (hilbertCommonOddKernel d c)
      (hilbertLeftOddKernelRemainder d c) :=
    Nat.coprime_of_squarefree_mul
      (oddKernel_eq_common_mul_leftRemainder d c ▸
        hilbertSquareClassOddKernel_squarefree d)
  have hgb : Nat.Coprime (hilbertCommonOddKernel d c)
      (hilbertRightOddKernelRemainder d c) :=
    Nat.coprime_of_squarefree_mul
      (oddKernel_eq_common_mul_rightRemainder d c ▸
        hilbertSquareClassOddKernel_squarefree c)
  have hakc : Nat.Coprime (hilbertLeftOddKernelRemainder d c)
      (hilbertSquareClassOddKernel c) := by
    exact Nat.coprime_div_gcd_of_squarefree
      (hilbertSquareClassOddKernel_squarefree d)
      (hilbertSquareClassOddKernel_ne_zero c)
  exact ⟨hga, hgb,
    hakc.of_dvd_right (hilbertRightOddKernelRemainder_dvd d c)⟩

/-- The product of the Legendre symbols over the distinct prime factors of a
natural number. -/
def legendrePrimeFactorProduct (n : ℕ) (z : ℤ) : ℤ :=
  ∏ p ∈ primeFactorsAsPrimes n,
    letI : Fact p.1.Prime := ⟨p.2⟩
    legendreSym p.1 z

private lemma prod_primeFactorsAsPrimes (n : ℕ) :
    ∏ p ∈ primeFactorsAsPrimes n, p.1 = ∏ p ∈ n.primeFactors, p := by
  simp only [primeFactorsAsPrimes, Finset.prod_map,
    Function.Embedding.coeFn_mk]
  simpa using (Finset.prod_attach n.primeFactors (fun p => p))

private lemma jacobiSym_prod_prime_right (z : ℤ)
    (S : Finset {p : ℕ // p.Prime}) :
    jacobiSym z (∏ p ∈ S, p.1) = ∏ p ∈ S, jacobiSym z p.1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      rw [Finset.prod_insert hp]
      rw [jacobiSym.mul_right' z p.2.ne_zero
        (Finset.prod_ne_zero_iff.mpr fun q hq => q.2.ne_zero)]
      rw [ih, Finset.prod_insert hp]

/-- On a squarefree natural number, the product of Legendre symbols over its
prime factors is its Jacobi symbol. -/
theorem legendrePrimeFactorProduct_eq_jacobiSym
    {n : ℕ} (hn : Squarefree n) (z : ℤ) :
    legendrePrimeFactorProduct n z = jacobiSym z n := by
  calc
    legendrePrimeFactorProduct n z =
        ∏ p ∈ primeFactorsAsPrimes n, jacobiSym z p.1 := by
      unfold legendrePrimeFactorProduct
      apply Finset.prod_congr rfl
      intro p _hp
      letI : Fact p.1.Prime := ⟨p.2⟩
      exact jacobiSym.legendreSym.to_jacobiSym p.1 z
    _ = jacobiSym z (∏ p ∈ primeFactorsAsPrimes n, p.1) :=
      (jacobiSym_prod_prime_right z _).symm
    _ = jacobiSym z (∏ p ∈ n.primeFactors, p) := by
      rw [prod_primeFactorsAsPrimes]
    _ = jacobiSym z n := by
      rw [Nat.prod_primeFactors_of_squarefree hn]

theorem legendrePrimeFactorProduct_commonOddKernel_eq_jacobiSym
    (d c : ℚ) (z : ℤ) :
    legendrePrimeFactorProduct (hilbertCommonOddKernel d c) z =
      jacobiSym z (hilbertCommonOddKernel d c) :=
  legendrePrimeFactorProduct_eq_jacobiSym
    (hilbertCommonOddKernel_squarefree d c) z

theorem legendrePrimeFactorProduct_leftOddKernelRemainder_eq_jacobiSym
    (d c : ℚ) (z : ℤ) :
    legendrePrimeFactorProduct (hilbertLeftOddKernelRemainder d c) z =
      jacobiSym z (hilbertLeftOddKernelRemainder d c) :=
  legendrePrimeFactorProduct_eq_jacobiSym
    (hilbertLeftOddKernelRemainder_squarefree d c) z

theorem legendrePrimeFactorProduct_rightOddKernelRemainder_eq_jacobiSym
    (d c : ℚ) (z : ℤ) :
    legendrePrimeFactorProduct (hilbertRightOddKernelRemainder d c) z =
      jacobiSym z (hilbertRightOddKernelRemainder d c) :=
  legendrePrimeFactorProduct_eq_jacobiSym
    (hilbertRightOddKernelRemainder_squarefree d c) z

/-- At a prime not dividing a nonzero integer, the rational unit character is
the ordinary Legendre symbol of that integer. -/
lemma oddPrimeUnitCharacter_intCast_of_not_dvd
    (p : ℕ) [Fact p.Prime] (z : ℤ) (hpz : ¬p ∣ z.natAbs) :
    oddPrimeUnitCharacter p (z : ℚ) = legendreSym p z := by
  have hfac : z.natAbs.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpz
  let n := z.natAbs
  have hbase : oddPrimeUnitCharacter p (z : ℚ) =
      (if z < 0 then legendreSym p (-1) else 1) *
        legendreSym p n := by
    simp [oddPrimeUnitCharacter, pFreeNatPart, hfac, n]
  rw [hbase]
  by_cases hneg : z < 0
  · have hzEq : z = -(n : ℤ) := by dsimp [n]; omega
    rw [if_pos hneg]
    calc
      legendreSym p (-1) * legendreSym p n =
          legendreSym p ((-1) * (n : ℤ)) :=
        (legendreSym.mul p (-1) n).symm
      _ = legendreSym p z := by rw [hzEq]; congr 1; ring
  · have hzEq : z = (n : ℤ) := by
      simp [n, Int.natAbs_of_nonneg (not_lt.mp hneg)]
    rw [if_neg hneg, one_mul, hzEq]

lemma valuationParity_intCast_eq_zero_of_not_dvd
    (p : ℕ) [Fact p.Prime] (z : ℤ) (hpz : ¬p ∣ z.natAbs) :
    valuationParity p (z : ℚ) = 0 := by
  have hval : padicValInt p z = 0 :=
    padicValNat.eq_zero_of_not_dvd hpz
  simp [valuationParity, padicValRat.of_int, hval]

lemma hilbertSignedSquarefreeInteger_natAbs {q : ℚ} (hq : q ≠ 0) :
    (hilbertSignedSquarefreeInteger q).natAbs =
      hilbertSquareClassDyadicKernel q * hilbertSquareClassOddKernel q := by
  simp only [hilbertSignedSquarefreeInteger, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [Int.natAbs_sign_of_ne_zero (hilbertSquareClassInteger_ne_zero hq)]
  simp

theorem hilbertSignedSquarefreeInteger_natAbs_squarefree
    {q : ℚ} (hq : q ≠ 0) :
    Squarefree (hilbertSignedSquarefreeInteger q).natAbs := by
  rw [hilbertSignedSquarefreeInteger_natAbs hq]
  rw [Nat.squarefree_mul]
  · exact ⟨by
        simp only [hilbertSquareClassDyadicKernel]
        split_ifs
        · exact Nat.prime_two.squarefree
        · exact squarefree_one,
      hilbertSquareClassOddKernel_squarefree q⟩
  · simp only [hilbertSquareClassDyadicKernel]
    split_ifs
    · exact (hilbertSquareClassOddKernel_odd hq).coprime_two_left
    · simp

lemma valuationParity_intCast_eq_one_of_squarefree_dvd
    (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : z ≠ 0)
    (hsq : Squarefree z.natAbs) (hpz : p ∣ z.natAbs) :
    valuationParity p (z : ℚ) = 1 := by
  have hnat : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hfac : z.natAbs.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq Fact.out hpz
  have hval : padicValInt p z = 1 := by
    rw [padicValInt, padicValNat_def' (Fact.out : p.Prime).ne_one hnat,
      Nat.multiplicity_eq_factorization Fact.out hnat, hfac]
  simp [valuationParity, padicValRat.of_int, hval]

theorem hilbertLeftOddKernelRemainder_coprime_rightOddKernel (d c : ℚ) :
    Nat.Coprime (hilbertLeftOddKernelRemainder d c)
      (hilbertSquareClassOddKernel c) :=
  Nat.coprime_div_gcd_of_squarefree
    (hilbertSquareClassOddKernel_squarefree d)
    (hilbertSquareClassOddKernel_ne_zero c)

lemma prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder
    {d c : ℚ} (hd : d ≠ 0) {p : ℕ}
    (hp : p ∣ hilbertLeftOddKernelRemainder d c) : p ≠ 2 := by
  intro hp2
  have hnot2 : ¬2 ∣ hilbertLeftOddKernelRemainder d c := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hilbertLeftOddKernelRemainder_odd hd
  exact hnot2 (hp2 ▸ hp)

/-- On the left-only odd support, the Hilbert factor is the Legendre symbol
of the right signed squarefree representative. -/
theorem oddPrimeHilbertSymbol_signedSquarefree_leftRemainder
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime]
    (hp : p ∣ hilbertLeftOddKernelRemainder d c) :
    oddPrimeHilbertSymbol p
        (prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder hd hp)
        (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      legendreSym p (hilbertSignedSquarefreeInteger c) := by
  let hpodd := prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder hd hp
  have hpD : p ∣ (hilbertSignedSquarefreeInteger d).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hd]
    apply dvd_mul_of_dvd_right
    exact hp.trans (hilbertLeftOddKernelRemainder_dvd d c)
  have hpDyadic : Nat.Coprime p (hilbertSquareClassDyadicKernel c) := by
    simp only [hilbertSquareClassDyadicKernel]
    split_ifs
    · exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hpodd
    · simp
  have hpKernel : Nat.Coprime p (hilbertSquareClassOddKernel c) :=
    (hilbertLeftOddKernelRemainder_coprime_rightOddKernel d c).of_dvd_left hp
  have hpNatAbs : ¬p ∣ (hilbertSignedSquarefreeInteger c).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hc]
    intro hpC
    have hcop : Nat.Coprime p
        (hilbertSquareClassDyadicKernel c *
          hilbertSquareClassOddKernel c) :=
      hpDyadic.mul_right hpKernel
    have hpOne : p ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd (dvd_refl p) hpC
    exact (Fact.out : p.Prime).not_dvd_one hpOne
  have hdpar : valuationParity p
      (hilbertSignedSquarefreeInteger d : ℚ) = 1 :=
    valuationParity_intCast_eq_one_of_squarefree_dvd p
      (hilbertSignedSquarefreeInteger d)
      (hilbertSignedSquarefreeInteger_ne_zero hd)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hd) hpD
  have hcpar : valuationParity p
      (hilbertSignedSquarefreeInteger c : ℚ) = 0 :=
    valuationParity_intCast_eq_zero_of_not_dvd p
      (hilbertSignedSquarefreeInteger c) hpNatAbs
  change oddPrimeHilbertSymbol p hpodd
      (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) = _
  simp [oddPrimeHilbertSymbol, hdpar, hcpar,
    oddPrimeUnitCharacter_intCast_of_not_dvd p
      (hilbertSignedSquarefreeInteger c) hpNatAbs]

private lemma dvd_of_mem_primeFactorsAsPrimes
    {n : ℕ} {p : {p : ℕ // p.Prime}}
    (hp : p ∈ primeFactorsAsPrimes n) : p.1 ∣ n := by
  simp only [primeFactorsAsPrimes, Finset.mem_map,
    Finset.mem_attach] at hp
  rcases hp with ⟨q, _hq, hqp⟩
  have hqmem : q.1 ∈ n.primeFactors := q.2
  have hqdvd : q.1 ∣ n := (Nat.mem_primeFactors.mp hqmem).2.1
  have hval : q.1 = p.1 := congrArg Subtype.val hqp
  rw [← hval]
  exact hqdvd

/-- The part of the signed-squarefree finite Hilbert product supported only on
the left odd-kernel remainder. -/
def signedSquarefreeLeftRemainderHilbertProduct (d c : ℚ) : ℤ :=
  ∏ p ∈ primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c),
    finiteHilbertFactor (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) p

/-- The left-only odd-prime Hilbert product is one Jacobi symbol. -/
theorem signedSquarefreeLeftRemainderHilbertProduct_eq_jacobiSym
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeLeftRemainderHilbertProduct d c =
      jacobiSym (hilbertSignedSquarefreeInteger c)
        (hilbertLeftOddKernelRemainder d c) := by
  calc
    signedSquarefreeLeftRemainderHilbertProduct d c =
        legendrePrimeFactorProduct (hilbertLeftOddKernelRemainder d c)
          (hilbertSignedSquarefreeInteger c) := by
      unfold signedSquarefreeLeftRemainderHilbertProduct
      unfold legendrePrimeFactorProduct
      apply Finset.prod_congr rfl
      intro p hpMem
      letI : Fact p.1.Prime := ⟨p.2⟩
      have hp : p.1 ∣ hilbertLeftOddKernelRemainder d c :=
        dvd_of_mem_primeFactorsAsPrimes hpMem
      have hpodd : p.1 ≠ 2 :=
        prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder hd hp
      rw [finiteHilbertFactor, dif_neg hpodd]
      exact oddPrimeHilbertSymbol_signedSquarefree_leftRemainder hd hc p.1 hp
    _ = jacobiSym (hilbertSignedSquarefreeInteger c)
        (hilbertLeftOddKernelRemainder d c) :=
      legendrePrimeFactorProduct_leftOddKernelRemainder_eq_jacobiSym d c _

lemma hilbertRightOddKernelRemainder_eq_left_swap (d c : ℚ) :
    hilbertRightOddKernelRemainder d c =
      hilbertLeftOddKernelRemainder c d := by
  simp [hilbertRightOddKernelRemainder,
    hilbertLeftOddKernelRemainder, hilbertCommonOddKernel, Nat.gcd_comm]

theorem hilbertRightOddKernelRemainder_coprime_leftOddKernel (d c : ℚ) :
    Nat.Coprime (hilbertRightOddKernelRemainder d c)
      (hilbertSquareClassOddKernel d) := by
  rw [hilbertRightOddKernelRemainder_eq_left_swap]
  exact hilbertLeftOddKernelRemainder_coprime_rightOddKernel c d

lemma prime_ne_two_of_dvd_hilbertRightOddKernelRemainder
    {d c : ℚ} (hc : c ≠ 0) {p : ℕ}
    (hp : p ∣ hilbertRightOddKernelRemainder d c) : p ≠ 2 := by
  rw [hilbertRightOddKernelRemainder_eq_left_swap] at hp
  exact prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder hc hp

/-- On the right-only odd support, the Hilbert factor is the Legendre symbol
of the left signed squarefree representative. -/
theorem oddPrimeHilbertSymbol_signedSquarefree_rightRemainder
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime]
    (hp : p ∣ hilbertRightOddKernelRemainder d c) :
    oddPrimeHilbertSymbol p
        (prime_ne_two_of_dvd_hilbertRightOddKernelRemainder hc hp)
        (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      legendreSym p (hilbertSignedSquarefreeInteger d) := by
  have hp' : p ∣ hilbertLeftOddKernelRemainder c d := by
    rwa [hilbertRightOddKernelRemainder_eq_left_swap] at hp
  let hpodd := prime_ne_two_of_dvd_hilbertRightOddKernelRemainder hc hp
  calc
    oddPrimeHilbertSymbol p hpodd
        (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      oddPrimeHilbertSymbol p hpodd
        (hilbertSignedSquarefreeInteger c : ℚ)
        (hilbertSignedSquarefreeInteger d : ℚ) :=
      oddPrimeHilbertSymbol_symm p hpodd _ _
    _ = legendreSym p (hilbertSignedSquarefreeInteger d) := by
      change oddPrimeHilbertSymbol p
          (prime_ne_two_of_dvd_hilbertLeftOddKernelRemainder hc hp')
          (hilbertSignedSquarefreeInteger c : ℚ)
          (hilbertSignedSquarefreeInteger d : ℚ) = _
      exact oddPrimeHilbertSymbol_signedSquarefree_leftRemainder
        hc hd p hp'

/-- The part of the signed-squarefree finite Hilbert product supported only on
the right odd-kernel remainder. -/
def signedSquarefreeRightRemainderHilbertProduct (d c : ℚ) : ℤ :=
  ∏ p ∈ primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c),
    finiteHilbertFactor (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) p

/-- The right-only odd-prime Hilbert product is one Jacobi symbol. -/
theorem signedSquarefreeRightRemainderHilbertProduct_eq_jacobiSym
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeRightRemainderHilbertProduct d c =
      jacobiSym (hilbertSignedSquarefreeInteger d)
        (hilbertRightOddKernelRemainder d c) := by
  calc
    signedSquarefreeRightRemainderHilbertProduct d c =
        legendrePrimeFactorProduct (hilbertRightOddKernelRemainder d c)
          (hilbertSignedSquarefreeInteger d) := by
      unfold signedSquarefreeRightRemainderHilbertProduct
      unfold legendrePrimeFactorProduct
      apply Finset.prod_congr rfl
      intro p hpMem
      letI : Fact p.1.Prime := ⟨p.2⟩
      have hp : p.1 ∣ hilbertRightOddKernelRemainder d c :=
        dvd_of_mem_primeFactorsAsPrimes hpMem
      have hpodd : p.1 ≠ 2 :=
        prime_ne_two_of_dvd_hilbertRightOddKernelRemainder hc hp
      rw [finiteHilbertFactor, dif_neg hpodd]
      exact oddPrimeHilbertSymbol_signedSquarefree_rightRemainder hd hc p.1 hp
    _ = jacobiSym (hilbertSignedSquarefreeInteger d)
        (hilbertRightOddKernelRemainder d c) :=
      legendrePrimeFactorProduct_rightOddKernelRemainder_eq_jacobiSym d c _

/-- The signed quotient obtained by removing one natural prime factor from an
integer's absolute value. -/
def signedPrimeQuotient (p : ℕ) (z : ℤ) : ℤ :=
  z.sign * (z.natAbs / p : ℕ)

lemma mul_signedPrimeQuotient {p : ℕ} {z : ℤ}
    (hp : p ∣ z.natAbs) :
    (p : ℤ) * signedPrimeQuotient p z = z := by
  rw [signedPrimeQuotient]
  calc
    (p : ℤ) * (z.sign * ((z.natAbs / p : ℕ) : ℤ)) =
        z.sign * ((p * (z.natAbs / p) : ℕ) : ℤ) := by
      push_cast
      ring
    _ = z.sign * (z.natAbs : ℤ) := by rw [Nat.mul_div_cancel' hp]
    _ = z := Int.sign_mul_natAbs z

lemma signedPrimeQuotient_natAbs {p : ℕ} {z : ℤ} (hz : z ≠ 0) :
    (signedPrimeQuotient p z).natAbs = z.natAbs / p := by
  simp only [signedPrimeQuotient, Int.natAbs_mul, Int.natAbs_natCast]
  rw [Int.natAbs_sign_of_ne_zero hz]
  simp

lemma signedPrimeQuotient_eq_of_mul_eq
    (p : ℕ) [Fact p.Prime] {z q : ℤ} (hp : p ∣ z.natAbs)
    (hq : (p : ℤ) * q = z) :
    signedPrimeQuotient p z = q := by
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [mul_signedPrimeQuotient hp, hq]

lemma prime_not_dvd_signedPrimeQuotient_natAbs
    (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : z ≠ 0)
    (hsq : Squarefree z.natAbs) (hpz : p ∣ z.natAbs) :
    ¬p ∣ (signedPrimeQuotient p z).natAbs := by
  rw [signedPrimeQuotient_natAbs hz]
  intro hpq
  apply (Nat.squarefree_iff_prime_squarefree.mp hsq p Fact.out)
  rcases hpq with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    z.natAbs = p * (z.natAbs / p) := (Nat.mul_div_cancel' hpz).symm
    _ = p * (p * k) := by rw [hk]
    _ = p * p * k := by ring

/-- At the unique occurrence of a prime in a squarefree integer, the rational
unit character is the Legendre symbol after removing that prime factor. -/
lemma oddPrimeUnitCharacter_intCast_of_squarefree_dvd
    (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : z ≠ 0)
    (hsq : Squarefree z.natAbs) (hpz : p ∣ z.natAbs) :
    oddPrimeUnitCharacter p (z : ℚ) =
      legendreSym p (signedPrimeQuotient p z) := by
  have hfac : z.natAbs.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq Fact.out hpz
  let n := z.natAbs / p
  have hbase : oddPrimeUnitCharacter p (z : ℚ) =
      (if z < 0 then legendreSym p (-1) else 1) *
        legendreSym p n := by
    simp [oddPrimeUnitCharacter, pFreeNatPart, hfac, n]
  rw [hbase]
  by_cases hneg : z < 0
  · have hsign : z.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
    rw [if_pos hneg, signedPrimeQuotient, hsign]
    exact (legendreSym.mul p (-1) (z.natAbs / p)).symm
  · have hzpos : 0 < z := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hz)
    have hsign : z.sign = 1 := Int.sign_eq_one_of_pos hzpos
    rw [if_neg hneg, one_mul, signedPrimeQuotient, hsign]
    rw [one_mul]

lemma prime_ne_two_of_dvd_hilbertCommonOddKernel
    {d c : ℚ} (hd : d ≠ 0) {p : ℕ}
    (hp : p ∣ hilbertCommonOddKernel d c) : p ≠ 2 := by
  intro hp2
  have hnot2 : ¬2 ∣ hilbertCommonOddKernel d c := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hilbertCommonOddKernel_odd hd
  exact hnot2 (hp2 ▸ hp)

theorem signedPrimeQuotient_signedSquarefree_left
    {d c : ℚ} (hd : d ≠ 0) (p : ℕ) [Fact p.Prime]
    (hp : p ∣ hilbertCommonOddKernel d c) :
    signedPrimeQuotient p (hilbertSignedSquarefreeInteger d) =
      (hilbertSquareClassInteger d).sign *
        (hilbertSquareClassDyadicKernel d : ℤ) *
        (↑(hilbertCommonOddKernel d c / p) : ℤ) *
        (hilbertLeftOddKernelRemainder d c : ℤ) := by
  have hpD : p ∣ (hilbertSignedSquarefreeInteger d).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hd]
    apply dvd_mul_of_dvd_right
    exact hp.trans (Nat.gcd_dvd_left _ _)
  apply signedPrimeQuotient_eq_of_mul_eq p hpD
  simp only [hilbertSignedSquarefreeInteger]
  rw [oddKernel_eq_common_mul_leftRemainder]
  simp only [Nat.cast_mul]
  have hcancel : p * (hilbertCommonOddKernel d c / p) =
      hilbertCommonOddKernel d c := Nat.mul_div_cancel' hp
  have hcancelZ : (p : ℤ) * (↑(hilbertCommonOddKernel d c / p) : ℤ) =
      hilbertCommonOddKernel d c := by exact_mod_cast hcancel
  conv_rhs => rw [← hcancelZ]
  ring

theorem signedPrimeQuotient_signedSquarefree_right
    {d c : ℚ} (hc : c ≠ 0) (p : ℕ) [Fact p.Prime]
    (hp : p ∣ hilbertCommonOddKernel d c) :
    signedPrimeQuotient p (hilbertSignedSquarefreeInteger c) =
      (hilbertSquareClassInteger c).sign *
        (hilbertSquareClassDyadicKernel c : ℤ) *
        (↑(hilbertCommonOddKernel d c / p) : ℤ) *
        (hilbertRightOddKernelRemainder d c : ℤ) := by
  have hpC : p ∣ (hilbertSignedSquarefreeInteger c).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hc]
    apply dvd_mul_of_dvd_right
    exact hp.trans (Nat.gcd_dvd_right _ _)
  apply signedPrimeQuotient_eq_of_mul_eq p hpC
  simp only [hilbertSignedSquarefreeInteger]
  rw [oddKernel_eq_common_mul_rightRemainder]
  simp only [Nat.cast_mul]
  have hcancel : p * (hilbertCommonOddKernel d c / p) =
      hilbertCommonOddKernel d c := Nat.mul_div_cancel' hp
  have hcancelZ : (p : ℤ) * (↑(hilbertCommonOddKernel d c / p) : ℤ) =
      hilbertCommonOddKernel d c := by exact_mod_cast hcancel
  conv_rhs => rw [← hcancelZ]
  ring

/-- At a common odd-kernel prime, both valuation parities are one and the
Hilbert factor is expressed using the two signed prime quotients. -/
theorem oddPrimeHilbertSymbol_signedSquarefree_commonKernel
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp : p ∣ hilbertCommonOddKernel d c) :
    oddPrimeHilbertSymbol p
        (prime_ne_two_of_dvd_hilbertCommonOddKernel hd hp)
        (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      (-1 : ℤ) ^ ((p - 1) / 2) *
        legendreSym p
          (signedPrimeQuotient p (hilbertSignedSquarefreeInteger d)) *
        legendreSym p
          (signedPrimeQuotient p (hilbertSignedSquarefreeInteger c)) := by
  let hpodd := prime_ne_two_of_dvd_hilbertCommonOddKernel hd hp
  have hpD : p ∣ (hilbertSignedSquarefreeInteger d).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hd]
    apply dvd_mul_of_dvd_right
    exact hp.trans (Nat.gcd_dvd_left _ _)
  have hpC : p ∣ (hilbertSignedSquarefreeInteger c).natAbs := by
    rw [hilbertSignedSquarefreeInteger_natAbs hc]
    apply dvd_mul_of_dvd_right
    exact hp.trans (Nat.gcd_dvd_right _ _)
  have hdpar : valuationParity p
      (hilbertSignedSquarefreeInteger d : ℚ) = 1 :=
    valuationParity_intCast_eq_one_of_squarefree_dvd p
      (hilbertSignedSquarefreeInteger d)
      (hilbertSignedSquarefreeInteger_ne_zero hd)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hd) hpD
  have hcpar : valuationParity p
      (hilbertSignedSquarefreeInteger c : ℚ) = 1 :=
    valuationParity_intCast_eq_one_of_squarefree_dvd p
      (hilbertSignedSquarefreeInteger c)
      (hilbertSignedSquarefreeInteger_ne_zero hc)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hc) hpC
  change oddPrimeHilbertSymbol p hpodd
      (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) = _
  simp [oddPrimeHilbertSymbol, hdpar, hcpar,
    oddPrimeUnitCharacter_intCast_of_squarefree_dvd p
      (hilbertSignedSquarefreeInteger d)
      (hilbertSignedSquarefreeInteger_ne_zero hd)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hd) hpD,
    oddPrimeUnitCharacter_intCast_of_squarefree_dvd p
      (hilbertSignedSquarefreeInteger c)
      (hilbertSignedSquarefreeInteger_ne_zero hc)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hc) hpC]

/-- At a common odd-kernel prime, the duplicated quotient of the common
factor cancels from the two unit characters. -/
theorem oddPrimeHilbertSymbol_signedSquarefree_commonKernel_simplified
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp : p ∣ hilbertCommonOddKernel d c) :
    oddPrimeHilbertSymbol p
        (prime_ne_two_of_dvd_hilbertCommonOddKernel hd hp)
        (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      (-1 : ℤ) ^ ((p - 1) / 2) *
        legendreSym p
          ((hilbertSquareClassInteger d).sign *
            (hilbertSquareClassDyadicKernel d : ℤ) *
            (hilbertLeftOddKernelRemainder d c : ℤ)) *
        legendreSym p
          ((hilbertSquareClassInteger c).sign *
            (hilbertSquareClassDyadicKernel c : ℤ) *
            (hilbertRightOddKernelRemainder d c : ℤ)) := by
  rw [oddPrimeHilbertSymbol_signedSquarefree_commonKernel hd hc p hp,
    signedPrimeQuotient_signedSquarefree_left hd p hp,
    signedPrimeQuotient_signedSquarefree_right hc p hp]
  have hpQuot : ¬p ∣ hilbertCommonOddKernel d c / p := by
    intro hpq
    apply (Nat.squarefree_iff_prime_squarefree.mp
      (hilbertCommonOddKernel_squarefree d c) p Fact.out)
    rcases hpq with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      hilbertCommonOddKernel d c =
          p * (hilbertCommonOddKernel d c / p) :=
        (Nat.mul_div_cancel' hp).symm
      _ = p * (p * k) := by rw [hk]
      _ = p * p * k := by ring
  have hquotRes :
      ((hilbertCommonOddKernel d c / p : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hpQuot
  have hquotSq :
      legendreSym p (↑(hilbertCommonOddKernel d c / p) : ℤ) ^ 2 = 1 := by
    apply legendreSym.sq_one
    exact_mod_cast hquotRes
  simp only [legendreSym.mul]
  calc
    _ = legendreSym p (↑(hilbertCommonOddKernel d c / p) : ℤ) ^ 2 *
          ((-1 : ℤ) ^ ((p - 1) / 2) *
            (legendreSym p (hilbertSquareClassInteger d).sign *
              legendreSym p (hilbertSquareClassDyadicKernel d) *
              legendreSym p (hilbertLeftOddKernelRemainder d c)) *
            (legendreSym p (hilbertSquareClassInteger c).sign *
              legendreSym p (hilbertSquareClassDyadicKernel c) *
              legendreSym p (hilbertRightOddKernelRemainder d c))) := by ring
    _ = _ := by rw [hquotSq, one_mul]

lemma neg_one_pow_half_eq_legendreSym
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    (-1 : ℤ) ^ ((p - 1) / 2) = legendreSym p (-1) := by
  have hpOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hpodd
  rw [legendreSym.at_neg_one hpodd,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hpOdd)]
  have hpdiv : p / 2 = (p - 1) / 2 := by
    rcases hpOdd with ⟨k, hk⟩
    omega
  rw [hpdiv]

/-- The part of the signed-squarefree finite Hilbert product supported on the
common odd kernel. -/
def signedSquarefreeCommonKernelHilbertProduct (d c : ℚ) : ℤ :=
  ∏ p ∈ primeFactorsAsPrimes (hilbertCommonOddKernel d c),
    finiteHilbertFactor (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) p

/-- The common odd-kernel Hilbert product is the product of the supplementary
Jacobi symbol and the two Jacobi symbols left after removing the common
prime. -/
theorem signedSquarefreeCommonKernelHilbertProduct_eq_jacobiSyms
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeCommonKernelHilbertProduct d c =
      jacobiSym (-1) (hilbertCommonOddKernel d c) *
        jacobiSym
          ((hilbertSquareClassInteger d).sign *
            (hilbertSquareClassDyadicKernel d : ℤ) *
            (hilbertLeftOddKernelRemainder d c : ℤ))
          (hilbertCommonOddKernel d c) *
        jacobiSym
          ((hilbertSquareClassInteger c).sign *
            (hilbertSquareClassDyadicKernel c : ℤ) *
            (hilbertRightOddKernelRemainder d c : ℤ))
          (hilbertCommonOddKernel d c) := by
  calc
    signedSquarefreeCommonKernelHilbertProduct d c =
        legendrePrimeFactorProduct (hilbertCommonOddKernel d c) (-1) *
          legendrePrimeFactorProduct (hilbertCommonOddKernel d c)
            ((hilbertSquareClassInteger d).sign *
              (hilbertSquareClassDyadicKernel d : ℤ) *
              (hilbertLeftOddKernelRemainder d c : ℤ)) *
          legendrePrimeFactorProduct (hilbertCommonOddKernel d c)
            ((hilbertSquareClassInteger c).sign *
              (hilbertSquareClassDyadicKernel c : ℤ) *
              (hilbertRightOddKernelRemainder d c : ℤ)) := by
      unfold signedSquarefreeCommonKernelHilbertProduct
        legendrePrimeFactorProduct
      calc
        (∏ p ∈ primeFactorsAsPrimes (hilbertCommonOddKernel d c),
            finiteHilbertFactor (hilbertSignedSquarefreeInteger d : ℚ)
              (hilbertSignedSquarefreeInteger c : ℚ) p) =
            ∏ p ∈ primeFactorsAsPrimes (hilbertCommonOddKernel d c),
              letI : Fact p.1.Prime := ⟨p.2⟩
              legendreSym p.1 (-1) *
                legendreSym p.1
                  ((hilbertSquareClassInteger d).sign *
                    (hilbertSquareClassDyadicKernel d : ℤ) *
                    (hilbertLeftOddKernelRemainder d c : ℤ)) *
                legendreSym p.1
                  ((hilbertSquareClassInteger c).sign *
                    (hilbertSquareClassDyadicKernel c : ℤ) *
                    (hilbertRightOddKernelRemainder d c : ℤ)) := by
          apply Finset.prod_congr rfl
          intro p hpMem
          letI : Fact p.1.Prime := ⟨p.2⟩
          have hp : p.1 ∣ hilbertCommonOddKernel d c :=
            dvd_of_mem_primeFactorsAsPrimes hpMem
          have hpodd : p.1 ≠ 2 :=
            prime_ne_two_of_dvd_hilbertCommonOddKernel hd hp
          rw [finiteHilbertFactor, dif_neg hpodd,
            oddPrimeHilbertSymbol_signedSquarefree_commonKernel_simplified
              hd hc p.1 hp,
            neg_one_pow_half_eq_legendreSym p.1 hpodd]
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = _ := by
      rw [legendrePrimeFactorProduct_commonOddKernel_eq_jacobiSym,
        legendrePrimeFactorProduct_commonOddKernel_eq_jacobiSym,
        legendrePrimeFactorProduct_commonOddKernel_eq_jacobiSym]

private lemma mem_primeFactorsAsPrimes_iff
    {n : ℕ} (hn : n ≠ 0) (p : {p : ℕ // p.Prime}) :
    p ∈ primeFactorsAsPrimes n ↔ p.1 ∣ n := by
  constructor
  · exact dvd_of_mem_primeFactorsAsPrimes
  · intro hp
    simp only [primeFactorsAsPrimes, Finset.mem_map, Finset.mem_attach]
    exact ⟨⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hp, hn⟩⟩,
      trivial, Subtype.ext rfl⟩

private lemma prime_not_dvd_hilbertSquareClassDyadicKernel
    {q : ℚ} {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ¬p ∣ hilbertSquareClassDyadicKernel q := by
  simp only [hilbertSquareClassDyadicKernel]
  split_ifs
  · intro hpdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd with hpone | hptwo
    · exact hp.ne_one hpone
    · exact hpodd hptwo
  · exact hp.not_dvd_one

/-- The dyadic prime and the three disjoint odd supports of the two signed
squarefree representatives. -/
def signedSquarefreePrimeSupport (d c : ℚ) :
    Finset {p : ℕ // p.Prime} :=
  insert ⟨2, Nat.prime_two⟩
    (primeFactorsAsPrimes (hilbertCommonOddKernel d c) ∪
      (primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c) ∪
        primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c)))

/-- For the signed squarefree integer representatives, the rational bad-prime
set is exactly the dyadic prime together with the common, left-only, and
right-only odd supports. -/
theorem hilbertBadPrimeSet_signedSquarefreeIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    hilbertBadPrimeSet (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      signedSquarefreePrimeSupport d c := by
  have hdrep : (hilbertSignedSquarefreeInteger d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hd
  have hcrep : (hilbertSignedSquarefreeInteger c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hc
  ext p
  rw [mem_hilbertBadPrimeSet_iff hdrep hcrep]
  simp only [signedSquarefreePrimeSupport, Finset.mem_insert,
    Finset.mem_union]
  rw [mem_primeFactorsAsPrimes_iff (hilbertCommonOddKernel_ne_zero d c),
    mem_primeFactorsAsPrimes_iff (hilbertLeftOddKernelRemainder_ne_zero d c),
    mem_primeFactorsAsPrimes_iff (hilbertRightOddKernelRemainder_ne_zero d c)]
  by_cases hp2 : p.1 = 2
  · have hpEq : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    simp [hpEq]
  simp only [hp2, false_or]
  have hpNe : p ≠ ⟨2, Nat.prime_two⟩ := by
    intro hpEq
    exact hp2 (congrArg Subtype.val hpEq)
  have hpDyadicD : ¬p.1 ∣ hilbertSquareClassDyadicKernel d :=
    prime_not_dvd_hilbertSquareClassDyadicKernel p.2 hp2
  have hpDyadicC : ¬p.1 ∣ hilbertSquareClassDyadicKernel c :=
    prime_not_dvd_hilbertSquareClassDyadicKernel p.2 hp2
  rw [show hilbertSupportNat
      (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) =
        (hilbertSignedSquarefreeInteger d).natAbs *
          (hilbertSignedSquarefreeInteger c).natAbs by
        simp [hilbertSupportNat],
    hilbertSignedSquarefreeInteger_natAbs hd,
    hilbertSignedSquarefreeInteger_natAbs hc,
    oddKernel_eq_common_mul_leftRemainder,
    oddKernel_eq_common_mul_rightRemainder]
  simp only [p.2.dvd_mul, hpDyadicD, hpDyadicC, false_or]
  simp only [hpNe, false_or]
  tauto

private lemma primeFactorsAsPrimes_disjoint_of_coprime
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    Disjoint (primeFactorsAsPrimes m) (primeFactorsAsPrimes n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hpM : p.1 ∣ m := dvd_of_mem_primeFactorsAsPrimes hpm
  have hpN : p.1 ∣ n := dvd_of_mem_primeFactorsAsPrimes hpn
  apply p.2.not_dvd_one
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd hpM hpN

private lemma dyadicPrime_not_mem_signedSquarefreeOddSupport
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∉
      primeFactorsAsPrimes (hilbertCommonOddKernel d c) ∪
        (primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c) ∪
          primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c)) := by
  simp only [Finset.mem_union, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    have hdvd : 2 ∣ hilbertCommonOddKernel d c :=
      dvd_of_mem_primeFactorsAsPrimes hmem
    have hnot : ¬2 ∣ hilbertCommonOddKernel d c := by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact hilbertCommonOddKernel_odd (d := d) (c := c) hd
    exact hnot hdvd
  · intro hmem
    have hdvd : 2 ∣ hilbertLeftOddKernelRemainder d c :=
      dvd_of_mem_primeFactorsAsPrimes hmem
    have hnot : ¬2 ∣ hilbertLeftOddKernelRemainder d c := by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact hilbertLeftOddKernelRemainder_odd (d := d) (c := c) hd
    exact hnot hdvd
  · intro hmem
    have hdvd : 2 ∣ hilbertRightOddKernelRemainder d c :=
      dvd_of_mem_primeFactorsAsPrimes hmem
    have hnot : ¬2 ∣ hilbertRightOddKernelRemainder d c := by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact hilbertRightOddKernelRemainder_odd (d := d) (c := c) hc
    exact hnot hdvd

/-- The bad-prime finite product of the signed squarefree representatives is
the dyadic factor times the common, left-only, and right-only odd products. -/
theorem finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    finiteHilbertProduct (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ)) =
      dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ) *
        (signedSquarefreeCommonKernelHilbertProduct d c *
          (signedSquarefreeLeftRemainderHilbertProduct d c *
            signedSquarefreeRightRemainderHilbertProduct d c)) := by
  have hcop := hilbertOddKernelFactors_pairwise_coprime d c
  have hcommonLeft : Disjoint
      (primeFactorsAsPrimes (hilbertCommonOddKernel d c))
      (primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c)) :=
    primeFactorsAsPrimes_disjoint_of_coprime hcop.1
  have hcommonRight : Disjoint
      (primeFactorsAsPrimes (hilbertCommonOddKernel d c))
      (primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c)) :=
    primeFactorsAsPrimes_disjoint_of_coprime hcop.2.1
  have hleftRight : Disjoint
      (primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c))
      (primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c)) :=
    primeFactorsAsPrimes_disjoint_of_coprime hcop.2.2
  have hcommonOthers : Disjoint
      (primeFactorsAsPrimes (hilbertCommonOddKernel d c))
      (primeFactorsAsPrimes (hilbertLeftOddKernelRemainder d c) ∪
        primeFactorsAsPrimes (hilbertRightOddKernelRemainder d c)) :=
    hcommonLeft.sup_right hcommonRight
  rw [hilbertBadPrimeSet_signedSquarefreeIntegers hd hc]
  unfold finiteHilbertProduct signedSquarefreePrimeSupport
  rw [Finset.prod_insert
      (dyadicPrime_not_mem_signedSquarefreeOddSupport hd hc),
    Finset.prod_union hcommonOthers,
    Finset.prod_union hleftRight]
  rw [show finiteHilbertFactor (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) ⟨2, Nat.prime_two⟩ =
        dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ) by
      simp [finiteHilbertFactor]]
  rfl

/-- After partitioning its support, the complete finite Hilbert product of the
signed squarefree representatives is the dyadic factor times the four Jacobi
factors supplied by the common and one-sided odd supports. -/
theorem finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_eq_jacobiSyms
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    finiteHilbertProduct (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ)) =
      dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ) *
        ((jacobiSym (-1) (hilbertCommonOddKernel d c) *
            jacobiSym
              ((hilbertSquareClassInteger d).sign *
                (hilbertSquareClassDyadicKernel d : ℤ) *
                (hilbertLeftOddKernelRemainder d c : ℤ))
              (hilbertCommonOddKernel d c) *
            jacobiSym
              ((hilbertSquareClassInteger c).sign *
                (hilbertSquareClassDyadicKernel c : ℤ) *
                (hilbertRightOddKernelRemainder d c : ℤ))
              (hilbertCommonOddKernel d c)) *
          (jacobiSym (hilbertSignedSquarefreeInteger c)
              (hilbertLeftOddKernelRemainder d c) *
            jacobiSym (hilbertSignedSquarefreeInteger d)
              (hilbertRightOddKernelRemainder d c))) := by
  rw [finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers hd hc,
    signedSquarefreeCommonKernelHilbertProduct_eq_jacobiSyms hd hc,
    signedSquarefreeLeftRemainderHilbertProduct_eq_jacobiSym hd hc,
    signedSquarefreeRightRemainderHilbertProduct_eq_jacobiSym hd hc]

lemma hilbertSignedSquarefreeInteger_eq_common_mul_left
    (d c : ℚ) :
    hilbertSignedSquarefreeInteger d =
      (hilbertSquareClassInteger d).sign *
        (hilbertSquareClassDyadicKernel d : ℤ) *
        (hilbertCommonOddKernel d c : ℤ) *
        (hilbertLeftOddKernelRemainder d c : ℤ) := by
  simp only [hilbertSignedSquarefreeInteger]
  rw [oddKernel_eq_common_mul_leftRemainder]
  push_cast
  ring

lemma hilbertSignedSquarefreeInteger_eq_common_mul_right
    (d c : ℚ) :
    hilbertSignedSquarefreeInteger c =
      (hilbertSquareClassInteger c).sign *
        (hilbertSquareClassDyadicKernel c : ℤ) *
        (hilbertCommonOddKernel d c : ℤ) *
        (hilbertRightOddKernelRemainder d c : ℤ) := by
  simp only [hilbertSignedSquarefreeInteger]
  rw [oddKernel_eq_common_mul_rightRemainder]
  push_cast
  ring

/-- The sign and dyadic-kernel Jacobi factors remaining after separating the
three reciprocal odd-factor pairs. -/
def signedSquarefreeJacobiSupplementaryProduct (d c : ℚ) : ℤ :=
  jacobiSym (-1) (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertSquareClassInteger d).sign
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertSquareClassDyadicKernel d)
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertSquareClassInteger c).sign
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertSquareClassDyadicKernel c)
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertSquareClassInteger c).sign
      (hilbertLeftOddKernelRemainder d c) *
    jacobiSym (hilbertSquareClassDyadicKernel c)
      (hilbertLeftOddKernelRemainder d c) *
    jacobiSym (hilbertSquareClassInteger d).sign
      (hilbertRightOddKernelRemainder d c) *
    jacobiSym (hilbertSquareClassDyadicKernel d)
      (hilbertRightOddKernelRemainder d c)

/-- The Jacobi character contributed by the sign of the integral square-class
representative. -/
def hilbertSquareClassSignJacobiCharacter (q : ℚ) (n : ℕ) : ℤ :=
  if hilbertSquareClassInteger q < 0 then ZMod.χ₄ n else 1

/-- The Jacobi character contributed by the parity of the dyadic exponent of
the integral square-class representative. -/
def hilbertSquareClassDyadicJacobiCharacter (q : ℚ) (n : ℕ) : ℤ :=
  if Odd ((hilbertSquareClassInteger q).natAbs.factorization 2) then
    ZMod.χ₈ n
  else 1

/-- On an odd modulus, the sign Jacobi symbol is the corresponding choice
between the trivial character and `χ₄`. -/
lemma jacobiSym_hilbertSquareClassInteger_sign
    {q : ℚ} (hq : q ≠ 0) {n : ℕ} (hn : Odd n) :
    jacobiSym (hilbertSquareClassInteger q).sign n =
      hilbertSquareClassSignJacobiCharacter q n := by
  have hz : hilbertSquareClassInteger q ≠ 0 :=
    hilbertSquareClassInteger_ne_zero hq
  by_cases hneg : hilbertSquareClassInteger q < 0
  · rw [Int.sign_eq_neg_one_of_neg hneg, jacobiSym.at_neg_one hn]
    simp [hilbertSquareClassSignJacobiCharacter, hneg]
  · have hpos : 0 < hilbertSquareClassInteger q :=
      lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hz)
    rw [Int.sign_eq_one_of_pos hpos]
    simp [hilbertSquareClassSignJacobiCharacter, hneg]

/-- On an odd modulus, the dyadic-kernel Jacobi symbol is the corresponding
choice between the trivial character and `χ₈`. -/
lemma jacobiSym_hilbertSquareClassDyadicKernel
    (q : ℚ) {n : ℕ} (hn : Odd n) :
    jacobiSym (hilbertSquareClassDyadicKernel q) n =
      hilbertSquareClassDyadicJacobiCharacter q n := by
  simp only [hilbertSquareClassDyadicKernel,
    hilbertSquareClassDyadicJacobiCharacter]
  split_ifs
  · exact jacobiSym.at_two hn
  · simp

/-- The supplementary Jacobi product is the explicit product of the `χ₄` and
`χ₈` choices determined by the two signs and dyadic exponent parities. -/
theorem signedSquarefreeJacobiSupplementaryProduct_eq_characters
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeJacobiSupplementaryProduct d c =
      ZMod.χ₄ (hilbertCommonOddKernel d c) *
        hilbertSquareClassSignJacobiCharacter d
          (hilbertCommonOddKernel d c) *
        hilbertSquareClassDyadicJacobiCharacter d
          (hilbertCommonOddKernel d c) *
        hilbertSquareClassSignJacobiCharacter c
          (hilbertCommonOddKernel d c) *
        hilbertSquareClassDyadicJacobiCharacter c
          (hilbertCommonOddKernel d c) *
        hilbertSquareClassSignJacobiCharacter c
          (hilbertLeftOddKernelRemainder d c) *
        hilbertSquareClassDyadicJacobiCharacter c
          (hilbertLeftOddKernelRemainder d c) *
        hilbertSquareClassSignJacobiCharacter d
          (hilbertRightOddKernelRemainder d c) *
        hilbertSquareClassDyadicJacobiCharacter d
          (hilbertRightOddKernelRemainder d c) := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  unfold signedSquarefreeJacobiSupplementaryProduct
  rw [jacobiSym.at_neg_one hgOdd,
    jacobiSym_hilbertSquareClassInteger_sign hd hgOdd,
    jacobiSym_hilbertSquareClassDyadicKernel d hgOdd,
    jacobiSym_hilbertSquareClassInteger_sign hc hgOdd,
    jacobiSym_hilbertSquareClassDyadicKernel c hgOdd,
    jacobiSym_hilbertSquareClassInteger_sign hc haOdd,
    jacobiSym_hilbertSquareClassDyadicKernel c haOdd,
    jacobiSym_hilbertSquareClassInteger_sign hd hbOdd,
    jacobiSym_hilbertSquareClassDyadicKernel d hbOdd]

private lemma neg_one_pow_dyadic_exponent_period_eight
    (n : ℕ) (hn : Odd n) :
    (-1 : ℤ) ^ (((n + 8) ^ 2 - 1) / 8) =
      (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  have hnpos : 0 < n := hn.pos
  have hexpand : (n + 8) ^ 2 = n ^ 2 + 16 * n + 64 := by ring
  have hsq :
      (n + 8) ^ 2 - 1 = (n ^ 2 - 1) + 8 * (2 * n + 8) := by
    rw [hexpand]
    have hsqpos : 0 < n ^ 2 := pow_pos hnpos 2
    omega
  rw [hsq, Nat.add_mul_div_left _ _ (by omega : 0 < 8), pow_add]
  have heven : (-1 : ℤ) ^ (2 * n + 8) = 1 := by
    rw [show 2 * n + 8 = 2 * (n + 4) by omega, pow_mul]
    norm_num
  rw [heven, mul_one]

/-- On odd natural inputs, `χ₈` is the standard supplementary power of
`-1`. -/
lemma chi8_eq_neg_one_pow_of_odd {n : ℕ} (hn : Odd n) :
    ZMod.χ₈ n = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hlt : n < 8
      · have hcases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 := by
          rw [Nat.odd_iff] at hn
          omega
        rcases hcases with h | h | h | h <;> subst n <;> decide
      · have h8 : 8 ≤ n := Nat.le_of_not_gt hlt
        let m := n - 8
        have hnm : n = m + 8 := by dsimp [m]; omega
        have hmLt : m < n := by dsimp [m]; omega
        have hmOdd : Odd m := by
          rw [Nat.odd_iff] at hn ⊢
          dsimp [m]
          omega
        have hchi : ZMod.χ₈ n = ZMod.χ₈ m := by
          have hmod : n % 8 = m % 8 := by
            dsimp [m]
            omega
          calc
            ZMod.χ₈ n = ZMod.χ₈ (n % 8 : ℕ) :=
              ZMod.χ₈_nat_mod_eight n
            _ = ZMod.χ₈ (m % 8 : ℕ) :=
              congrArg (fun k : ℕ => ZMod.χ₈ k) hmod
            _ = ZMod.χ₈ m := (ZMod.χ₈_nat_mod_eight m).symm
        rw [hchi, ih m hmLt hmOdd, hnm,
          neg_one_pow_dyadic_exponent_period_eight m hmOdd]

/-- The parity indicator of the sign of the canonical integral square-class
representative. -/
def hilbertSquareClassSignParity (q : ℚ) : ℕ :=
  if hilbertSquareClassInteger q < 0 then 1 else 0

/-- The parity indicator of the dyadic exponent of the canonical integral
square-class representative. -/
def hilbertSquareClassDyadicParity (q : ℚ) : ℕ :=
  if Odd ((hilbertSquareClassInteger q).natAbs.factorization 2) then 1 else 0

/-- The sign character is the standard `χ₄` power selected by the sign parity. -/
lemma hilbertSquareClassSignJacobiCharacter_eq_neg_one_pow
    (q : ℚ) {n : ℕ} (hn : Odd n) :
    hilbertSquareClassSignJacobiCharacter q n =
      (-1 : ℤ) ^ (hilbertSquareClassSignParity q * (n / 2)) := by
  rw [show hilbertSquareClassSignJacobiCharacter q n =
      if hilbertSquareClassInteger q < 0 then ZMod.χ₄ n else 1 by rfl]
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn)]
  by_cases hneg : hilbertSquareClassInteger q < 0 <;>
    simp [hilbertSquareClassSignParity, hneg]

/-- The dyadic character is the standard `χ₈` power selected by the dyadic
exponent parity. -/
lemma hilbertSquareClassDyadicJacobiCharacter_eq_neg_one_pow
    (q : ℚ) {n : ℕ} (hn : Odd n) :
    hilbertSquareClassDyadicJacobiCharacter q n =
      (-1 : ℤ) ^
        (hilbertSquareClassDyadicParity q * ((n ^ 2 - 1) / 8)) := by
  rw [show hilbertSquareClassDyadicJacobiCharacter q n =
      if Odd ((hilbertSquareClassInteger q).natAbs.factorization 2) then
        ZMod.χ₈ n else 1 by rfl]
  rw [chi8_eq_neg_one_pow_of_odd hn]
  by_cases hodd : Odd ((hilbertSquareClassInteger q).natAbs.factorization 2) <;>
    simp [hilbertSquareClassDyadicParity, hodd]

/-- The explicit exponent of the supplementary Jacobi product after applying
the laws at `-1` and `2`. -/
def signedSquarefreeJacobiSupplementaryExponent (d c : ℚ) : ℕ :=
  let g := hilbertCommonOddKernel d c
  let a := hilbertLeftOddKernelRemainder d c
  let b := hilbertRightOddKernelRemainder d c
  g / 2 +
    hilbertSquareClassSignParity d * (g / 2) +
    hilbertSquareClassDyadicParity d * ((g ^ 2 - 1) / 8) +
    hilbertSquareClassSignParity c * (g / 2) +
    hilbertSquareClassDyadicParity c * ((g ^ 2 - 1) / 8) +
    hilbertSquareClassSignParity c * (a / 2) +
    hilbertSquareClassDyadicParity c * ((a ^ 2 - 1) / 8) +
    hilbertSquareClassSignParity d * (b / 2) +
    hilbertSquareClassDyadicParity d * ((b ^ 2 - 1) / 8)

/-- The complete supplementary Jacobi product is one explicit power of
`-1`. -/
theorem signedSquarefreeJacobiSupplementaryProduct_eq_neg_one_pow
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeJacobiSupplementaryProduct d c =
      (-1 : ℤ) ^ signedSquarefreeJacobiSupplementaryExponent d c := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  rw [signedSquarefreeJacobiSupplementaryProduct_eq_characters hd hc,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hgOdd),
    hilbertSquareClassSignJacobiCharacter_eq_neg_one_pow d hgOdd,
    hilbertSquareClassDyadicJacobiCharacter_eq_neg_one_pow d hgOdd,
    hilbertSquareClassSignJacobiCharacter_eq_neg_one_pow c hgOdd,
    hilbertSquareClassDyadicJacobiCharacter_eq_neg_one_pow c hgOdd,
    hilbertSquareClassSignJacobiCharacter_eq_neg_one_pow c haOdd,
    hilbertSquareClassDyadicJacobiCharacter_eq_neg_one_pow c haOdd,
    hilbertSquareClassSignJacobiCharacter_eq_neg_one_pow d hbOdd,
    hilbertSquareClassDyadicJacobiCharacter_eq_neg_one_pow d hbOdd]
  simp only [← pow_add]
  rfl

/-- The real Hilbert symbol of the signed squarefree representatives is the
product of their sign parities. -/
lemma realHilbertSymbol_signedSquarefreeIntegers_eq_neg_one_pow
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    realHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      (-1 : ℤ) ^
        (hilbertSquareClassSignParity d * hilbertSquareClassSignParity c) := by
  have hdroot : (hilbertSquareClassRootPart d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassRootPart_ne_zero hd
  have hcroot : (hilbertSquareClassRootPart c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassRootPart_ne_zero hc
  have hdEq : (hilbertSquareClassInteger d : ℚ) =
      (hilbertSignedSquarefreeInteger d : ℚ) *
        (hilbertSquareClassRootPart d : ℚ) ^ 2 := by
    exact_mod_cast hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hd
  have hcEq : (hilbertSquareClassInteger c : ℚ) =
      (hilbertSignedSquarefreeInteger c : ℚ) *
        (hilbertSquareClassRootPart c : ℚ) ^ 2 := by
    exact_mod_cast hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hc
  calc
    realHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      realHilbertSymbol
        ((hilbertSignedSquarefreeInteger d : ℚ) *
          (hilbertSquareClassRootPart d : ℚ) ^ 2)
        (hilbertSignedSquarefreeInteger c : ℚ) :=
      (realHilbertSymbol_mul_sq_left _ _ _ hdroot).symm
    _ = realHilbertSymbol (hilbertSquareClassInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) := by rw [← hdEq]
    _ = realHilbertSymbol (hilbertSquareClassInteger d : ℚ)
        ((hilbertSignedSquarefreeInteger c : ℚ) *
          (hilbertSquareClassRootPart c : ℚ) ^ 2) :=
      (realHilbertSymbol_mul_sq_right _ _ _ hcroot).symm
    _ = realHilbertSymbol (hilbertSquareClassInteger d : ℚ)
        (hilbertSquareClassInteger c : ℚ) := by rw [← hcEq]
    _ = (-1 : ℤ) ^
        (hilbertSquareClassSignParity d *
          hilbertSquareClassSignParity c) := by
      unfold realHilbertSymbol hilbertSquareClassSignParity
      norm_cast
      by_cases hdneg : hilbertSquareClassInteger d < 0 <;>
        by_cases hcneg : hilbertSquareClassInteger c < 0 <;>
          simp [hdneg, hcneg]

/-- The dyadic exponent parity is the valuation parity of the signed
squarefree representative. -/
lemma valuationParity_signedSquarefreeInteger
    (q : ℚ) (hq : q ≠ 0) :
    valuationParity 2 (hilbertSignedSquarefreeInteger q : ℚ) =
      hilbertSquareClassDyadicParity q := by
  by_cases hodd : Odd ((hilbertSquareClassInteger q).natAbs.factorization 2)
  · have hdvd : 2 ∣ (hilbertSignedSquarefreeInteger q).natAbs := by
      rw [hilbertSignedSquarefreeInteger_natAbs hq]
      simp [hilbertSquareClassDyadicKernel, hodd]
    rw [valuationParity_intCast_eq_one_of_squarefree_dvd 2
      (hilbertSignedSquarefreeInteger q)
      (hilbertSignedSquarefreeInteger_ne_zero hq)
      (hilbertSignedSquarefreeInteger_natAbs_squarefree hq) hdvd]
    simp [hilbertSquareClassDyadicParity, hodd]
  · have hnot : ¬2 ∣ (hilbertSignedSquarefreeInteger q).natAbs := by
      rw [hilbertSignedSquarefreeInteger_natAbs hq]
      simp [hilbertSquareClassDyadicKernel, hodd,
        two_not_dvd_hilbertSquareClassOddKernel hq]
    rw [valuationParity_intCast_eq_zero_of_not_dvd 2
      (hilbertSignedSquarefreeInteger q) hnot]
    simp [hilbertSquareClassDyadicParity, hodd]

private lemma dyadicUnitRepresentative_intCast
    (z : ℤ) (hz : z ≠ 0) :
    dyadicUnitRepresentative (z : ℚ) =
      z.sign * (pFreeNatPart 2 z.natAbs : ℤ) := by
  unfold dyadicUnitRepresentative
  rw [Rat.num_intCast, Rat.den_intCast]
  simp only [pFreeNatPart]
  norm_num
  by_cases hneg : z < 0
  · rw [if_pos (by exact_mod_cast hneg), Int.sign_eq_neg_one_of_neg hneg]
    ring
  · have hpos : 0 < z := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hz)
    rw [if_neg (by exact_mod_cast hneg), Int.sign_eq_one_of_pos hpos]
    simp

lemma hilbertSignedSquarefreeInteger_sign
    (q : ℚ) (hq : q ≠ 0) :
    (hilbertSignedSquarefreeInteger q).sign =
      (hilbertSquareClassInteger q).sign := by
  have hroot : (hilbertSquareClassRootPart q : ℤ) ≠ 0 := by
    exact_mod_cast hilbertSquareClassRootPart_ne_zero hq
  have hsquare : ((hilbertSquareClassRootPart q : ℤ) ^ 2).sign = 1 :=
    Int.sign_eq_one_iff_pos.mpr (sq_pos_of_ne_zero hroot)
  have hsign := congrArg Int.sign
    (hilbertSquareClassInteger_eq_signedSquarefreeInteger_mul_sq hq)
  rw [Int.sign_mul, hsquare, mul_one] at hsign
  exact hsign.symm

/-- The dyadic unit residue of the signed squarefree representative is its
original integral sign times its odd squarefree kernel. -/
lemma dyadicUnitRepresentative_signedSquarefreeInteger
    (q : ℚ) (hq : q ≠ 0) :
    (dyadicUnitRepresentative
        (hilbertSignedSquarefreeInteger q : ℚ) : ZMod 8) =
      ((hilbertSquareClassInteger q).sign *
        (hilbertSquareClassOddKernel q : ℤ) : ℤ) := by
  rw [dyadicUnitRepresentative_intCast _
      (hilbertSignedSquarefreeInteger_ne_zero hq),
    hilbertSignedSquarefreeInteger_natAbs hq, pFreeNatPart_mul]
  have hdyadicFree :
      pFreeNatPart 2 (hilbertSquareClassDyadicKernel q) = 1 := by
    simp only [hilbertSquareClassDyadicKernel]
    split_ifs <;> norm_num [pFreeNatPart]
  have hoddFree : pFreeNatPart 2 (hilbertSquareClassOddKernel q) =
      hilbertSquareClassOddKernel q := by
    simpa [pFreeNatPart] using
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd
        (hilbertSquareClassOddKernel q) Nat.prime_two).2
          (Or.inr (two_not_dvd_hilbertSquareClassOddKernel hq))
  rw [hdyadicFree, hoddFree, one_mul,
    hilbertSignedSquarefreeInteger_sign q hq]

/-- The three pairs of Jacobi symbols to which quadratic reciprocity applies. -/
def signedSquarefreeJacobiReciprocityProduct (d c : ℚ) : ℤ :=
  (jacobiSym (hilbertLeftOddKernelRemainder d c)
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertCommonOddKernel d c)
      (hilbertLeftOddKernelRemainder d c)) *
  (jacobiSym (hilbertRightOddKernelRemainder d c)
      (hilbertCommonOddKernel d c) *
    jacobiSym (hilbertCommonOddKernel d c)
      (hilbertRightOddKernelRemainder d c)) *
  (jacobiSym (hilbertRightOddKernelRemainder d c)
      (hilbertLeftOddKernelRemainder d c) *
    jacobiSym (hilbertLeftOddKernelRemainder d c)
      (hilbertRightOddKernelRemainder d c))

/-- Expanding every Jacobi numerator in the signed-squarefree finite product
separates the sign/dyadic supplementary terms from the three quadratic-
reciprocity pairs. -/
theorem finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_expanded
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    finiteHilbertProduct (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ)) =
      dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ) *
        (signedSquarefreeJacobiSupplementaryProduct d c *
          signedSquarefreeJacobiReciprocityProduct d c) := by
  rw [finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_eq_jacobiSyms
      hd hc,
    hilbertSignedSquarefreeInteger_eq_common_mul_left d c,
    hilbertSignedSquarefreeInteger_eq_common_mul_right d c]
  simp only [jacobiSym.mul_left]
  unfold signedSquarefreeJacobiSupplementaryProduct
    signedSquarefreeJacobiReciprocityProduct
  ring

/-- For coprime odd natural numbers, the two oppositely oriented Jacobi symbols
multiply to the quadratic-reciprocity sign. -/
lemma jacobiSym_mul_swap_of_odd_coprime
    {a b : ℕ} (ha : Odd a) (hb : Odd b) (hcop : Nat.Coprime a b) :
    jacobiSym (a : ℤ) b * jacobiSym (b : ℤ) a =
      (-1 : ℤ) ^ (a / 2 * (b / 2)) := by
  have hgcd : (b : ℤ).gcd (a : ℤ) = 1 := by
    simpa [Int.gcd, Nat.gcd_comm] using hcop.gcd_eq_one
  have hsq : jacobiSym (b : ℤ) a ^ 2 = 1 :=
    jacobiSym.sq_one hgcd
  rw [jacobiSym.quadratic_reciprocity ha hb]
  calc
    ((-1 : ℤ) ^ (a / 2 * (b / 2)) * jacobiSym (b : ℤ) a) *
        jacobiSym (b : ℤ) a =
      (-1 : ℤ) ^ (a / 2 * (b / 2)) *
        jacobiSym (b : ℤ) a ^ 2 := by ring
    _ = _ := by rw [hsq, mul_one]

/-- The three reciprocal Jacobi pairs contribute exactly the sum of their
quadratic-reciprocity exponents. -/
theorem signedSquarefreeJacobiReciprocityProduct_eq_neg_one_pow
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeJacobiReciprocityProduct d c =
      (-1 : ℤ) ^
        (hilbertLeftOddKernelRemainder d c / 2 *
            (hilbertCommonOddKernel d c / 2) +
          hilbertRightOddKernelRemainder d c / 2 *
            (hilbertCommonOddKernel d c / 2) +
          hilbertRightOddKernelRemainder d c / 2 *
            (hilbertLeftOddKernelRemainder d c / 2)) := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  obtain ⟨hga, hgb, hab⟩ := hilbertOddKernelFactors_pairwise_coprime d c
  unfold signedSquarefreeJacobiReciprocityProduct
  rw [jacobiSym_mul_swap_of_odd_coprime haOdd hgOdd hga.symm,
    jacobiSym_mul_swap_of_odd_coprime hbOdd hgOdd hgb.symm,
    jacobiSym_mul_swap_of_odd_coprime hbOdd haOdd hab.symm]
  rw [← pow_add, ← pow_add]

/-- After quadratic reciprocity, the finite product retains only the dyadic
factor, the sign/dyadic supplementary product, and one explicit parity sign. -/
theorem finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_after_reciprocity
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    finiteHilbertProduct (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ)
        (hilbertBadPrimeSet (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ)) =
      dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
          (hilbertSignedSquarefreeInteger c : ℚ) *
        (signedSquarefreeJacobiSupplementaryProduct d c *
          (-1 : ℤ) ^
            (hilbertLeftOddKernelRemainder d c / 2 *
                (hilbertCommonOddKernel d c / 2) +
              hilbertRightOddKernelRemainder d c / 2 *
                (hilbertCommonOddKernel d c / 2) +
              hilbertRightOddKernelRemainder d c / 2 *
                (hilbertLeftOddKernelRemainder d c / 2))) := by
  rw [finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_expanded hd hc,
    signedSquarefreeJacobiReciprocityProduct_eq_neg_one_pow hd hc]

private def hilbertResidueEpsilon (u : ZMod 8) : ℕ :=
  if u = 1 ∨ u = 5 then 0 else 1

private def hilbertResidueOmega (u : ZMod 8) : ℕ :=
  if u = 1 ∨ u = 7 then 0 else 1

private lemma hilbertResidueEpsilon_zero_or_one (u : ZMod 8) :
    hilbertResidueEpsilon u = 0 ∨ hilbertResidueEpsilon u = 1 := by
  unfold hilbertResidueEpsilon
  split <;> simp_all

private lemma hilbertResidueOmega_zero_or_one (u : ZMod 8) :
    hilbertResidueOmega u = 0 ∨ hilbertResidueOmega u = 1 := by
  unfold hilbertResidueOmega
  split <;> simp_all

private lemma odd_nat_mod_eight_cases {n : ℕ} (hn : Odd n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hmod2 : n % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 8)]
    exact Nat.odd_iff.mp hn
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  omega

private lemma neg_one_pow_half_eq_residueEpsilon {n : ℕ} (hn : Odd n) :
    (-1 : ℤ) ^ (n / 2) =
      (-1 : ℤ) ^ hilbertResidueEpsilon (n : ZMod 8) := by
  rw [← ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn)]
  rcases odd_nat_mod_eight_cases hn with h | h | h | h
  all_goals
    have h4 : n % 4 = (n % 8) % 4 := by
      rw [Nat.mod_mod_of_dvd n (by norm_num : 4 ∣ 8)]
    have hz : (n : ZMod 8) = (n % 8 : ℕ) := by
      rw [← ZMod.natCast_mod n 8]
  · rw [hz, h, ZMod.χ₄_nat_mod_four, h4, h]
    decide
  · rw [hz, h, ZMod.χ₄_nat_mod_four, h4, h]
    decide
  · rw [hz, h, ZMod.χ₄_nat_mod_four, h4, h]
    decide
  · rw [hz, h, ZMod.χ₄_nat_mod_four, h4, h]
    decide

private lemma neg_one_pow_omega_eq_residueOmega {n : ℕ} (hn : Odd n) :
    (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) =
      (-1 : ℤ) ^ hilbertResidueOmega (n : ZMod 8) := by
  rw [← chi8_eq_neg_one_pow_of_odd hn]
  rcases odd_nat_mod_eight_cases hn with h | h | h | h
  all_goals
    have hz : (n : ZMod 8) = (n % 8 : ℕ) := by
      rw [← ZMod.natCast_mod n 8]
  · rw [hz, h]
    decide
  · rw [hz, h]
    decide
  · rw [hz, h]
    decide
  · rw [hz, h]
    decide

private lemma dyadicUnitEpsilon_eq_reciprocityResidue
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitEpsilon q =
      hilbertResidueEpsilon (dyadicUnitRepresentative q : ZMod 8) := by
  rcases dyadicUnitRepresentative_cast_eq_one_or_three_or_five_or_seven hq with
    hrep | hrep | hrep | hrep
  · rw [dyadicUnitEpsilon_eq_zero_of_cast_eq_one hrep, hrep]
    decide
  · rw [dyadicUnitEpsilon_eq_one_of_cast_eq_three hrep, hrep]
    decide
  · rw [dyadicUnitEpsilon_eq_zero_of_cast_eq_five hrep, hrep]
    decide
  · rw [dyadicUnitEpsilon_eq_one_of_cast_eq_seven hrep, hrep]
    decide

private lemma dyadicUnitOmega_eq_reciprocityResidue
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitOmega q =
      hilbertResidueOmega (dyadicUnitRepresentative q : ZMod 8) := by
  rcases dyadicUnitRepresentative_cast_eq_one_or_three_or_five_or_seven hq with
    hrep | hrep | hrep | hrep
  · rw [dyadicUnitOmega_eq_zero_of_cast_eq_one hrep, hrep]
    decide
  · rw [dyadicUnitOmega_eq_one_of_cast_eq_three hrep, hrep]
    decide
  · rw [dyadicUnitOmega_eq_one_of_cast_eq_five hrep, hrep]
    decide
  · rw [dyadicUnitOmega_eq_zero_of_cast_eq_seven hrep, hrep]
    decide

private def hilbertSignResidue (s : ℕ) : ZMod 8 :=
  if s = 1 then -1 else 1

private lemma squareClassInteger_sign_cast_eq_hilbertSignResidue
    (q : ℚ) (hq : q ≠ 0) :
    ((hilbertSquareClassInteger q).sign : ZMod 8) =
      hilbertSignResidue (hilbertSquareClassSignParity q) := by
  by_cases hneg : hilbertSquareClassInteger q < 0
  · rw [Int.sign_eq_neg_one_of_neg hneg]
    simp [hilbertSignResidue, hilbertSquareClassSignParity, hneg]
  · have hpos : 0 < hilbertSquareClassInteger q :=
      lt_of_le_of_ne (not_lt.mp hneg)
        (Ne.symm (hilbertSquareClassInteger_ne_zero hq))
    rw [Int.sign_eq_one_of_pos hpos]
    simp [hilbertSignResidue, hilbertSquareClassSignParity, hneg]

private lemma signedSquarefreeLeftUnitResidue
    {d c : ℚ} (hd : d ≠ 0) :
    (dyadicUnitRepresentative
        (hilbertSignedSquarefreeInteger d : ℚ) : ZMod 8) =
      hilbertSignResidue (hilbertSquareClassSignParity d) *
        (hilbertCommonOddKernel d c : ℕ) *
        (hilbertLeftOddKernelRemainder d c : ℕ) := by
  rw [dyadicUnitRepresentative_signedSquarefreeInteger d hd,
    oddKernel_eq_common_mul_leftRemainder (d := d) (c := c)]
  push_cast
  rw [squareClassInteger_sign_cast_eq_hilbertSignResidue d hd]
  ring

private lemma signedSquarefreeRightUnitResidue
    {d c : ℚ} (hc : c ≠ 0) :
    (dyadicUnitRepresentative
        (hilbertSignedSquarefreeInteger c : ℚ) : ZMod 8) =
      hilbertSignResidue (hilbertSquareClassSignParity c) *
        (hilbertCommonOddKernel d c : ℕ) *
        (hilbertRightOddKernelRemainder d c : ℕ) := by
  rw [dyadicUnitRepresentative_signedSquarefreeInteger c hc,
    oddKernel_eq_common_mul_rightRemainder (d := d) (c := c)]
  push_cast
  rw [squareClassInteger_sign_cast_eq_hilbertSignResidue c hc]
  ring

private def signedSquarefreeDyadicResidueExponent
    (sd sc ad ac : ℕ) (g a b : ZMod 8) : ℕ :=
  let u := hilbertSignResidue sd * g * a
  let v := hilbertSignResidue sc * g * b
  hilbertResidueEpsilon u * hilbertResidueEpsilon v +
    ad * hilbertResidueOmega v + ac * hilbertResidueOmega u

private def signedSquarefreeSupplementaryResidueExponent
    (sd sc ad ac : ℕ) (g a b : ZMod 8) : ℕ :=
  hilbertResidueEpsilon g +
    sd * hilbertResidueEpsilon g + ad * hilbertResidueOmega g +
    sc * hilbertResidueEpsilon g + ac * hilbertResidueOmega g +
    sc * hilbertResidueEpsilon a + ac * hilbertResidueOmega a +
    sd * hilbertResidueEpsilon b + ad * hilbertResidueOmega b

private def signedSquarefreeReciprocityResidueExponent
    (g a b : ZMod 8) : ℕ :=
  hilbertResidueEpsilon a * hilbertResidueEpsilon g +
    hilbertResidueEpsilon b * hilbertResidueEpsilon g +
    hilbertResidueEpsilon b * hilbertResidueEpsilon a

private lemma finite_signedSquarefree_parity_identity
    (sd sc ad ac : ℕ)
    (hsd : sd = 0 ∨ sd = 1) (hsc : sc = 0 ∨ sc = 1)
    (had : ad = 0 ∨ ad = 1) (hac : ac = 0 ∨ ac = 1)
    (g a b : ZMod 8)
    (hg : g = 1 ∨ g = 3 ∨ g = 5 ∨ g = 7)
    (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7)
    (hb : b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7) :
    (-1 : ℤ) ^ (sd * sc) *
        ((-1 : ℤ) ^
            signedSquarefreeDyadicResidueExponent sd sc ad ac g a b *
          ((-1 : ℤ) ^
              signedSquarefreeSupplementaryResidueExponent sd sc ad ac g a b *
            (-1 : ℤ) ^
              signedSquarefreeReciprocityResidueExponent g a b)) = 1 := by
  rcases hsd with (rfl | rfl) <;>
    rcases hsc with (rfl | rfl) <;>
    rcases had with (rfl | rfl) <;>
    rcases hac with (rfl | rfl) <;>
    rcases hg with (rfl | rfl | rfl | rfl) <;>
    rcases ha with (rfl | rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl | rfl) <;>
    decide

private lemma hilbertSquareClassSignParity_zero_or_one (q : ℚ) :
    hilbertSquareClassSignParity q = 0 ∨
      hilbertSquareClassSignParity q = 1 := by
  unfold hilbertSquareClassSignParity
  split <;> simp

private lemma hilbertSquareClassDyadicParity_zero_or_one (q : ℚ) :
    hilbertSquareClassDyadicParity q = 0 ∨
      hilbertSquareClassDyadicParity q = 1 := by
  unfold hilbertSquareClassDyadicParity
  split <;> simp

private lemma odd_nat_cast_zmod_eight_cases {n : ℕ} (hn : Odd n) :
    (n : ZMod 8) = 1 ∨ (n : ZMod 8) = 3 ∨
      (n : ZMod 8) = 5 ∨ (n : ZMod 8) = 7 := by
  rcases odd_nat_mod_eight_cases hn with h | h | h | h
  · left
    rw [← ZMod.natCast_mod n 8, h]
    norm_num
  · right; left
    rw [← ZMod.natCast_mod n 8, h]
    norm_num
  · right; right; left
    rw [← ZMod.natCast_mod n 8, h]
    norm_num
  · right; right; right
    rw [← ZMod.natCast_mod n 8, h]
    norm_num

private lemma neg_one_pow_flag_mul_half_eq_residueEpsilon
    (s n : ℕ) (hs : s = 0 ∨ s = 1) (hn : Odd n) :
    (-1 : ℤ) ^ (s * (n / 2)) =
      (-1 : ℤ) ^ (s * hilbertResidueEpsilon (n : ZMod 8)) := by
  rcases hs with rfl | rfl
  · simp
  · simpa using neg_one_pow_half_eq_residueEpsilon hn

private lemma neg_one_pow_flag_mul_omega_eq_residueOmega
    (s n : ℕ) (hs : s = 0 ∨ s = 1) (hn : Odd n) :
    (-1 : ℤ) ^ (s * ((n ^ 2 - 1) / 8)) =
      (-1 : ℤ) ^ (s * hilbertResidueOmega (n : ZMod 8)) := by
  rcases hs with rfl | rfl
  · simp
  · simpa using neg_one_pow_omega_eq_residueOmega hn

private lemma neg_one_pow_half_mul_half_eq_residueEpsilon
    (n m : ℕ) (hn : Odd n) (hm : Odd m) :
    (-1 : ℤ) ^ (n / 2 * (m / 2)) =
      (-1 : ℤ) ^
        (hilbertResidueEpsilon (n : ZMod 8) *
          hilbertResidueEpsilon (m : ZMod 8)) := by
  have hnPow := neg_one_pow_half_eq_residueEpsilon hn
  have hmPow := neg_one_pow_half_eq_residueEpsilon hm
  rcases hilbertResidueEpsilon_zero_or_one (n : ZMod 8) with he | he
  · have hnOne : (-1 : ℤ) ^ (n / 2) = 1 := by simpa [he] using hnPow
    rw [pow_mul, hnOne, one_pow, he]
    simp
  · have hnNeg : (-1 : ℤ) ^ (n / 2) = -1 := by simpa [he] using hnPow
    rw [pow_mul, hnNeg, he, one_mul]
    exact hmPow

private lemma signedSupplementaryProduct_eq_residueExponent
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    signedSquarefreeJacobiSupplementaryProduct d c =
      (-1 : ℤ) ^ signedSquarefreeSupplementaryResidueExponent
        (hilbertSquareClassSignParity d)
        (hilbertSquareClassSignParity c)
        (hilbertSquareClassDyadicParity d)
        (hilbertSquareClassDyadicParity c)
        (hilbertCommonOddKernel d c : ZMod 8)
        (hilbertLeftOddKernelRemainder d c : ZMod 8)
        (hilbertRightOddKernelRemainder d c : ZMod 8) := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  have hsd := hilbertSquareClassSignParity_zero_or_one d
  have hsc := hilbertSquareClassSignParity_zero_or_one c
  have had := hilbertSquareClassDyadicParity_zero_or_one d
  have hac := hilbertSquareClassDyadicParity_zero_or_one c
  rw [signedSquarefreeJacobiSupplementaryProduct_eq_neg_one_pow hd hc]
  unfold signedSquarefreeJacobiSupplementaryExponent
    signedSquarefreeSupplementaryResidueExponent
  simp only [pow_add]
  rw [neg_one_pow_half_eq_residueEpsilon hgOdd,
    neg_one_pow_flag_mul_half_eq_residueEpsilon _ _ hsd hgOdd,
    neg_one_pow_flag_mul_omega_eq_residueOmega _ _ had hgOdd,
    neg_one_pow_flag_mul_half_eq_residueEpsilon _ _ hsc hgOdd,
    neg_one_pow_flag_mul_omega_eq_residueOmega _ _ hac hgOdd,
    neg_one_pow_flag_mul_half_eq_residueEpsilon _ _ hsc haOdd,
    neg_one_pow_flag_mul_omega_eq_residueOmega _ _ hac haOdd,
    neg_one_pow_flag_mul_half_eq_residueEpsilon _ _ hsd hbOdd,
    neg_one_pow_flag_mul_omega_eq_residueOmega _ _ had hbOdd]

private lemma signedReciprocityPower_eq_residueExponent
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    (-1 : ℤ) ^
        (hilbertLeftOddKernelRemainder d c / 2 *
            (hilbertCommonOddKernel d c / 2) +
          hilbertRightOddKernelRemainder d c / 2 *
            (hilbertCommonOddKernel d c / 2) +
          hilbertRightOddKernelRemainder d c / 2 *
            (hilbertLeftOddKernelRemainder d c / 2)) =
      (-1 : ℤ) ^ signedSquarefreeReciprocityResidueExponent
        (hilbertCommonOddKernel d c : ZMod 8)
        (hilbertLeftOddKernelRemainder d c : ZMod 8)
        (hilbertRightOddKernelRemainder d c : ZMod 8) := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  unfold signedSquarefreeReciprocityResidueExponent
  simp only [pow_add]
  rw [neg_one_pow_half_mul_half_eq_residueEpsilon _ _ haOdd hgOdd,
    neg_one_pow_half_mul_half_eq_residueEpsilon _ _ hbOdd hgOdd,
    neg_one_pow_half_mul_half_eq_residueEpsilon _ _ hbOdd haOdd]

private lemma dyadicHilbertSymbol_signed_eq_residueExponent
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    dyadicHilbertSymbol (hilbertSignedSquarefreeInteger d : ℚ)
        (hilbertSignedSquarefreeInteger c : ℚ) =
      (-1 : ℤ) ^ signedSquarefreeDyadicResidueExponent
        (hilbertSquareClassSignParity d)
        (hilbertSquareClassSignParity c)
        (hilbertSquareClassDyadicParity d)
        (hilbertSquareClassDyadicParity c)
        (hilbertCommonOddKernel d c : ZMod 8)
        (hilbertLeftOddKernelRemainder d c : ZMod 8)
        (hilbertRightOddKernelRemainder d c : ZMod 8) := by
  have hdrep : (hilbertSignedSquarefreeInteger d : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hd
  have hcrep : (hilbertSignedSquarefreeInteger c : ℚ) ≠ 0 := by
    exact_mod_cast hilbertSignedSquarefreeInteger_ne_zero hc
  unfold dyadicHilbertSymbol signedSquarefreeDyadicResidueExponent
  rw [valuationParity_signedSquarefreeInteger d hd,
    valuationParity_signedSquarefreeInteger c hc,
    dyadicUnitEpsilon_eq_reciprocityResidue hdrep,
    dyadicUnitEpsilon_eq_reciprocityResidue hcrep,
    dyadicUnitOmega_eq_reciprocityResidue hdrep,
    dyadicUnitOmega_eq_reciprocityResidue hcrep,
    signedSquarefreeLeftUnitResidue (d := d) (c := c) hd,
    signedSquarefreeRightUnitResidue (d := d) (c := c) hc]

/-- Hilbert reciprocity for the canonical signed squarefree representatives of
two nonzero rational square classes. -/
theorem hilbertProductFormula_signedSquarefreeIntegers
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    HilbertProductFormula (hilbertSignedSquarefreeInteger d : ℚ)
      (hilbertSignedSquarefreeInteger c : ℚ) := by
  obtain ⟨hgOdd, haOdd, hbOdd⟩ := hilbertOddKernelFactors_odd hd hc
  unfold HilbertProductFormula
  rw [realHilbertSymbol_signedSquarefreeIntegers_eq_neg_one_pow hd hc,
    finiteHilbertProduct_badPrimeSet_signedSquarefreeIntegers_after_reciprocity
      hd hc,
    dyadicHilbertSymbol_signed_eq_residueExponent hd hc,
    signedSupplementaryProduct_eq_residueExponent hd hc,
    signedReciprocityPower_eq_residueExponent hd hc]
  exact finite_signedSquarefree_parity_identity _ _ _ _
    (hilbertSquareClassSignParity_zero_or_one d)
    (hilbertSquareClassSignParity_zero_or_one c)
    (hilbertSquareClassDyadicParity_zero_or_one d)
    (hilbertSquareClassDyadicParity_zero_or_one c)
    _ _ _ (odd_nat_cast_zmod_eight_cases hgOdd)
    (odd_nat_cast_zmod_eight_cases haOdd)
    (odd_nat_cast_zmod_eight_cases hbOdd)

/-- The rational Hilbert product formula, obtained from the explicit local
formulas by square-class normalization and finite quadratic reciprocity. -/
theorem hilbertProductFormula
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    HilbertProductFormula d c := by
  exact (hilbertProductFormula_iff_signedSquarefreeIntegers hd hc).2
    (hilbertProductFormula_signedSquarefreeIntegers hd hc)

end Rat
