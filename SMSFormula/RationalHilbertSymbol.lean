import SMSFormula.RationalIsotropy

/-!
# Rational Hilbert-symbol formulas

This module begins the reciprocity results needed for rational ternary
Hasse--Minkowski.  It defines the standard odd-prime Hilbert-symbol formula
from the parity of `padicValRat` and the Legendre character of the remaining
`p`-adic unit.  It also defines the real sign formula and the dyadic formula
through an explicit odd rational unit representative.

The definition is purely rational arithmetic.  This module does not
identify the formula with representation by a local quadratic norm, and it
does not prove Hilbert reciprocity or the quadratic Hasse norm theorem.
-/

noncomputable section

namespace Rat

/-- The part of a natural number remaining after removing its full `p`-power
factor. -/
def pFreeNatPart (p n : ℕ) : ℕ :=
  n / p ^ n.factorization p

/-- Removing the full `p`-power commutes with multiplication. -/
lemma pFreeNatPart_mul (p a b : ℕ) :
    pFreeNatPart p (a * b) = pFreeNatPart p a * pFreeNatPart p b := by
  simpa [pFreeNatPart] using Nat.ordCompl_mul a b p

/-- A prime does not divide the `p`-free part of a nonzero natural number. -/
lemma prime_not_dvd_pFreeNatPart {p n : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ pFreeNatPart p n := by
  exact Nat.not_dvd_ordCompl hp hn

private def pFreeCharacter (p : ℕ) [Fact p.Prime] (n : ℕ) : ℤ :=
  legendreSym p (pFreeNatPart p n)

private lemma pFreeCharacter_mul (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    pFreeCharacter p (a * b) = pFreeCharacter p a * pFreeCharacter p b := by
  simp [pFreeCharacter, pFreeNatPart_mul, legendreSym.mul]

private lemma pFreeCharacter_sq {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    pFreeCharacter p n ^ 2 = 1 := by
  apply legendreSym.sq_one
  have h : ((pFreeNatPart p n : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact prime_not_dvd_pFreeNatPart Fact.out hn
  exact_mod_cast h

private lemma exists_mul_sq_num_den_normalization
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    ∃ g : ℕ, g ≠ 0 ∧
      q.num.natAbs * (x.num.natAbs * x.num.natAbs) =
        (q * x ^ 2).num.natAbs * g ∧
      q.den * (x.den * x.den) = (q * x ^ 2).den * g := by
  let y := x ^ 2
  let r := q * y
  let g := (q.num * y.num).natAbs.gcd (q.den * y.den)
  have hg : g ≠ 0 := by
    apply Nat.gcd_ne_zero_left
    simp [y]
    exact ⟨hq, hx⟩
  have hyNum : y.num = x.num * x.num := by
    simpa [y, pow_two] using Rat.mul_self_num x
  have hyDen : y.den = x.den * x.den := by
    simpa [y, pow_two] using Rat.mul_self_den x
  have hnumInt := Rat.num_mul_num_eq_num_mul_gcd q y
  have hdenNatRaw := Rat.den_mul_den_eq_den_mul_gcd q y
  have hnumNat :
      q.num.natAbs * (x.num.natAbs * x.num.natAbs) =
        r.num.natAbs * g := by
    have h := congrArg Int.natAbs hnumInt
    simp only [Int.natAbs_mul] at h
    have h' : q.num.natAbs * y.num.natAbs = r.num.natAbs * g := by
      simpa [r, g, Int.natAbs_natCast, Int.natAbs_mul] using h
    simpa only [hyNum, Int.natAbs_mul] using h'
  have hdenNat :
      q.den * (x.den * x.den) = r.den * g := by
    have h : q.den * y.den = r.den * g := hdenNatRaw
    simpa only [hyDen] using h
  exact ⟨g, hg, hnumNat, hdenNat⟩

/-- The Legendre character of the `p`-adic unit part of a rational number.

The denominator character occurs multiplicatively rather than inversely
because every nonzero Legendre value has square one. -/
def oddPrimeUnitCharacter (p : ℕ) [Fact p.Prime] (q : ℚ) : ℤ :=
  (if q < 0 then legendreSym p (-1) else 1) *
    legendreSym p (pFreeNatPart p q.num.natAbs) *
      legendreSym p (pFreeNatPart p q.den)

/-- The unit-part character of a nonzero rational number is a sign. -/
lemma oddPrimeUnitCharacter_sq {p : ℕ} [Fact p.Prime]
    {q : ℚ} (hq : q ≠ 0) :
    oddPrimeUnitCharacter p q ^ 2 = 1 := by
  have hnum0 : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hq
  have hden0 : q.den ≠ 0 := q.den_nz
  have hnum : ((pFreeNatPart p q.num.natAbs : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact prime_not_dvd_pFreeNatPart Fact.out hnum0
  have hden : ((pFreeNatPart p q.den : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact prime_not_dvd_pFreeNatPart Fact.out hden0
  have hnumSq : legendreSym p (pFreeNatPart p q.num.natAbs) ^ 2 = 1 := by
    apply legendreSym.sq_one
    exact_mod_cast hnum
  have hdenSq : legendreSym p (pFreeNatPart p q.den) ^ 2 = 1 := by
    apply legendreSym.sq_one
    exact_mod_cast hden
  have hnegOneSq : legendreSym p (-1) ^ 2 = 1 := by
    apply legendreSym.sq_one
    simp
  by_cases hneg : q < 0
  · simp only [oddPrimeUnitCharacter, if_pos hneg, mul_pow]
    rw [hnegOneSq, hnumSq, hdenSq]
    norm_num
  · simp only [oddPrimeUnitCharacter, if_neg hneg, one_mul, mul_pow]
    rw [hnumSq, hdenSq]
    norm_num

/-- The odd-prime unit character is multiplicative on nonzero rational
numbers. -/
lemma oddPrimeUnitCharacter_mul {p : ℕ} [Fact p.Prime]
    (q r : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) :
    oddPrimeUnitCharacter p (q * r) =
      oddPrimeUnitCharacter p q * oddPrimeUnitCharacter p r := by
  let s := q * r
  let g := (q.num * r.num).natAbs.gcd (q.den * r.den)
  have hg : g ≠ 0 := by
    apply Nat.gcd_ne_zero_left
    simp
    exact ⟨hq, hr⟩
  have hnumInt := Rat.num_mul_num_eq_num_mul_gcd q r
  have hdenNat := Rat.den_mul_den_eq_den_mul_gcd q r
  have hnumNat :
      q.num.natAbs * r.num.natAbs = s.num.natAbs * g := by
    have h := congrArg Int.natAbs hnumInt
    simpa [s, g, Int.natAbs_mul, Int.natAbs_natCast] using h
  have hdenNat' : q.den * r.den = s.den * g := by
    simpa [s, g] using hdenNat
  have hnumChar := congrArg (pFreeCharacter p) hnumNat
  have hdenChar := congrArg (pFreeCharacter p) hdenNat'
  simp only [pFreeCharacter_mul] at hnumChar hdenChar
  have hgChar := pFreeCharacter_sq (p := p) hg
  have hchar :
      pFreeCharacter p s.num.natAbs * pFreeCharacter p s.den =
        (pFreeCharacter p q.num.natAbs * pFreeCharacter p q.den) *
          (pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den) := by
    calc
      pFreeCharacter p s.num.natAbs * pFreeCharacter p s.den =
          (pFreeCharacter p s.num.natAbs * pFreeCharacter p s.den) *
            pFreeCharacter p g ^ 2 := by rw [hgChar, mul_one]
      _ = (pFreeCharacter p s.num.natAbs * pFreeCharacter p g) *
          (pFreeCharacter p s.den * pFreeCharacter p g) := by ring
      _ = _ := by rw [← hnumChar, ← hdenChar]; ring
  have hnegOneSq : legendreSym p (-1) ^ 2 = 1 := by
    apply legendreSym.sq_one
    simp
  change
    (if s < 0 then legendreSym p (-1) else 1) *
        pFreeCharacter p s.num.natAbs * pFreeCharacter p s.den =
      ((if q < 0 then legendreSym p (-1) else 1) *
          pFreeCharacter p q.num.natAbs * pFreeCharacter p q.den) *
        ((if r < 0 then legendreSym p (-1) else 1) *
          pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den)
  rw [mul_assoc, hchar]
  by_cases hqneg : q < 0 <;> by_cases hrneg : r < 0
  · have hspos : ¬s < 0 := by
      exact not_lt_of_ge (mul_pos_of_neg_of_neg hqneg hrneg).le
    simp only [if_neg hspos, if_pos hqneg, if_pos hrneg]
    ring_nf
    rw [hnegOneSq]
    ring
  · have hsneg : s < 0 := by
      have hrpos : 0 < r :=
        lt_of_le_of_ne (not_lt.mp hrneg) (Ne.symm hr)
      exact mul_neg_of_neg_of_pos hqneg hrpos
    simp only [if_pos hsneg, if_pos hqneg, if_neg hrneg]
    ring
  · have hsneg : s < 0 := by
      have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hqneg) (Ne.symm hq)
      exact mul_neg_of_pos_of_neg hqpos hrneg
    simp only [if_pos hsneg, if_neg hqneg, if_pos hrneg]
    ring
  · have hspos : ¬s < 0 := by
      have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hqneg) (Ne.symm hq)
      have hrpos : 0 < r :=
        lt_of_le_of_ne (not_lt.mp hrneg) (Ne.symm hr)
      exact not_lt_of_ge (mul_pos hqpos hrpos).le
    simp only [if_neg hspos, if_neg hqneg, if_neg hrneg]
    ring

/-- Inversion does not change the odd-prime unit character of a nonzero
rational number. -/
lemma oddPrimeUnitCharacter_inv {p : ℕ} [Fact p.Prime]
    (q : ℚ) (hq : q ≠ 0) :
    oddPrimeUnitCharacter p q⁻¹ = oddPrimeUnitCharacter p q := by
  have hmul := oddPrimeUnitCharacter_mul (p := p) q q⁻¹ hq (inv_ne_zero hq)
  have hsq := oddPrimeUnitCharacter_sq (p := p) hq
  rw [mul_inv_cancel₀ hq] at hmul
  have hone : oddPrimeUnitCharacter p (1 : ℚ) = 1 := by
    simp [oddPrimeUnitCharacter, pFreeNatPart]
  rw [hone] at hmul
  calc
    oddPrimeUnitCharacter p q⁻¹ =
        oddPrimeUnitCharacter p q⁻¹ * oddPrimeUnitCharacter p q ^ 2 := by
          rw [hsq, mul_one]
    _ = (oddPrimeUnitCharacter p q * oddPrimeUnitCharacter p q⁻¹) *
        oddPrimeUnitCharacter p q := by ring
    _ = oddPrimeUnitCharacter p q := by rw [← hmul, one_mul]

/-- The unit character of a negative quotient is the product of the
supplementary character of `-1` and the two unit characters. -/
lemma oddPrimeUnitCharacter_neg_div {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (c d : ℚ) (hc : c ≠ 0) (hd : d ≠ 0) :
    oddPrimeUnitCharacter p (-c / d) =
      (-1 : ℤ) ^ ((p - 1) / 2) * oddPrimeUnitCharacter p c *
        oddPrimeUnitCharacter p d := by
  have hnegOne : oddPrimeUnitCharacter p (-1 : ℚ) = legendreSym p (-1) := by
    simp [oddPrimeUnitCharacter, pFreeNatPart]
  rw [div_eq_mul_inv, show -c = (-1 : ℚ) * c by ring,
    oddPrimeUnitCharacter_mul (-1 * c) d⁻¹ (mul_ne_zero (by norm_num) hc)
      (inv_ne_zero hd),
    oddPrimeUnitCharacter_mul (-1) c (by norm_num) hc,
    oddPrimeUnitCharacter_inv d hd, hnegOne]
  have hpOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hpodd
  rw [legendreSym.at_neg_one hpodd,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hpOdd)]
  have hpdiv : p / 2 = (p - 1) / 2 := by
    rcases hpOdd with ⟨k, hk⟩
    omega
  rw [hpdiv]

/-- Multiplication by a nonzero rational square does not change the Legendre
character of the `p`-adic unit part. -/
lemma oddPrimeUnitCharacter_mul_sq {p : ℕ} [Fact p.Prime]
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    oddPrimeUnitCharacter p (q * x ^ 2) = oddPrimeUnitCharacter p q := by
  let r := q * x ^ 2
  obtain ⟨g, hg, hnumNat, hdenNat⟩ :=
    exists_mul_sq_num_den_normalization q x hq hx
  have hxnum : x.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hx
  have hxden : x.den ≠ 0 := x.den_nz
  change q.num.natAbs * (x.num.natAbs * x.num.natAbs) =
    r.num.natAbs * g at hnumNat
  change q.den * (x.den * x.den) = r.den * g at hdenNat
  have hnumChar := congrArg (pFreeCharacter p) hnumNat
  have hdenChar := congrArg (pFreeCharacter p) hdenNat
  simp only [pFreeCharacter_mul] at hnumChar hdenChar
  have hxnumChar := pFreeCharacter_sq (p := p) hxnum
  have hxdenChar := pFreeCharacter_sq (p := p) hxden
  have hgChar := pFreeCharacter_sq (p := p) hg
  have hnumChar' :
      pFreeCharacter p q.num.natAbs =
        pFreeCharacter p r.num.natAbs * pFreeCharacter p g := by
    calc
      pFreeCharacter p q.num.natAbs =
          pFreeCharacter p q.num.natAbs *
            (pFreeCharacter p x.num.natAbs * pFreeCharacter p x.num.natAbs) := by
              rw [show pFreeCharacter p x.num.natAbs *
                pFreeCharacter p x.num.natAbs = 1 by simpa [pow_two] using hxnumChar]
              simp
      _ = _ := hnumChar
  have hdenChar' :
      pFreeCharacter p q.den =
        pFreeCharacter p r.den * pFreeCharacter p g := by
    calc
      pFreeCharacter p q.den =
          pFreeCharacter p q.den *
            (pFreeCharacter p x.den * pFreeCharacter p x.den) := by
              rw [show pFreeCharacter p x.den * pFreeCharacter p x.den = 1 by
                simpa [pow_two] using hxdenChar]
              simp
      _ = _ := hdenChar
  have hchar :
      pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den =
        pFreeCharacter p q.num.natAbs * pFreeCharacter p q.den := by
    calc
      pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den =
          (pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den) *
            pFreeCharacter p g ^ 2 := by rw [hgChar, mul_one]
      _ = (pFreeCharacter p r.num.natAbs * pFreeCharacter p g) *
          (pFreeCharacter p r.den * pFreeCharacter p g) := by ring
      _ = _ := by rw [← hnumChar', ← hdenChar']
  have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hsign : r < 0 ↔ q < 0 := by
    simp [r, mul_neg_iff, hxpos, not_lt_of_ge hxpos.le]
  change
    (if r < 0 then legendreSym p (-1) else 1) *
        pFreeCharacter p r.num.natAbs * pFreeCharacter p r.den =
      (if q < 0 then legendreSym p (-1) else 1) *
        pFreeCharacter p q.num.natAbs * pFreeCharacter p q.den
  rw [if_congr hsign rfl, mul_assoc, hchar, ← mul_assoc]
  rfl

/-- The parity of the rational `p`-adic valuation, represented by `0` or
`1`. -/
def valuationParity (p : ℕ) (q : ℚ) : ℕ :=
  (padicValRat p q % 2).natAbs

/-- Rational valuation parity is represented canonically by zero or one. -/
lemma valuationParity_eq_zero_or_one (p : ℕ) (q : ℚ) :
    valuationParity p q = 0 ∨ valuationParity p q = 1 := by
  unfold valuationParity
  rcases Int.emod_two_eq_zero_or_one (padicValRat p q) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- Multiplication by a nonzero rational square does not change valuation
parity. -/
lemma valuationParity_mul_sq {p : ℕ} [Fact p.Prime]
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    valuationParity p (q * x ^ 2) = valuationParity p q := by
  unfold valuationParity
  rw [padicValRat.mul hq (pow_ne_zero 2 hx), padicValRat.pow hx]
  congr 1
  omega

/-- A negative quotient of two rationals with odd `p`-adic valuation parity
has even valuation parity. -/
lemma valuationParity_neg_div_eq_zero {p : ℕ} [Fact p.Prime]
    {c d : ℚ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hcpar : valuationParity p c = 1)
    (hdpar : valuationParity p d = 1) :
    valuationParity p (-c / d) = 0 := by
  unfold valuationParity at hcpar hdpar ⊢
  rw [padicValRat.div (neg_ne_zero.mpr hc) hd, padicValRat.neg]
  have hcmod : padicValRat p c % 2 = 1 := by
    have hnonneg : 0 ≤ padicValRat p c % 2 := Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hcpar with h | h
    · exact h
    · omega
  have hdmod : padicValRat p d % 2 = 1 := by
    have hnonneg : 0 ≤ padicValRat p d % 2 := Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hdpar with h | h
    · exact h
    · omega
  rw [Int.sub_emod, hcmod, hdmod]
  norm_num

/-- A negative product of two rationals with odd `p`-adic valuation parity
has even valuation parity. -/
lemma valuationParity_neg_mul_eq_zero {p : ℕ} [Fact p.Prime]
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : valuationParity p d = 1)
    (hcpar : valuationParity p c = 1) :
    valuationParity p (-d * c) = 0 := by
  unfold valuationParity at hdpar hcpar ⊢
  rw [padicValRat.mul (neg_ne_zero.mpr hd) hc, padicValRat.neg]
  have hdmod : padicValRat p d % 2 = 1 := by
    have hnonneg : 0 ≤ padicValRat p d % 2 :=
      Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hdpar with h | h
    · exact h
    · omega
  have hcmod : padicValRat p c % 2 = 1 := by
    have hnonneg : 0 ≤ padicValRat p c % 2 :=
      Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hcpar with h | h
    · exact h
    · omega
  rw [Int.add_emod, hdmod, hcmod]
  norm_num

/-- The standard odd-prime Hilbert-symbol formula

`(-1)^(αβ(p-1)/2) * (u/p)^β * (v/p)^α`,

where `a = p^α u` and `b = p^β v` modulo squares.  The explicit `p ≠ 2`
hypothesis keeps this definition separate from the dyadic formula. -/
def oddPrimeHilbertSymbol (p : ℕ) [Fact p.Prime] (_hpodd : p ≠ 2)
    (a b : ℚ) : ℤ :=
  (-1 : ℤ) ^ (valuationParity p a * valuationParity p b * ((p - 1) / 2)) *
    oddPrimeUnitCharacter p a ^ valuationParity p b *
      oddPrimeUnitCharacter p b ^ valuationParity p a

/-- The explicit odd-prime Hilbert-symbol formula is symmetric. -/
lemma oddPrimeHilbertSymbol_symm (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (a b : ℚ) :
    oddPrimeHilbertSymbol p hpodd a b =
      oddPrimeHilbertSymbol p hpodd b a := by
  simp [oddPrimeHilbertSymbol, Nat.mul_comm]
  ring

/-- If both valuations are even, the odd-prime formula is one. -/
lemma oddPrimeHilbertSymbol_eq_one_of_valuationParity_eq_zero
    (p : ℕ) [Fact p.Prime] (a b : ℚ) (hpodd : p ≠ 2)
    (ha : valuationParity p a = 0) (hb : valuationParity p b = 0) :
    oddPrimeHilbertSymbol p hpodd a b = 1 := by
  simp [oddPrimeHilbertSymbol, ha, hb]

/-- For nonzero arguments, the odd-prime formula takes values in
`{1, -1}`. -/
lemma oddPrimeHilbertSymbol_sq (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oddPrimeHilbertSymbol p hpodd a b ^ 2 = 1 := by
  have hca := oddPrimeUnitCharacter_sq (p := p) ha
  have hcb := oddPrimeUnitCharacter_sq (p := p) hb
  have hsign :
      (((-1 : ℤ) ^
        (valuationParity p a * valuationParity p b * ((p - 1) / 2))) ^ 2) = 1 := by
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  have hcaPow :
      (oddPrimeUnitCharacter p a ^ valuationParity p b) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul, hca, one_pow]
  have hcbPow :
      (oddPrimeUnitCharacter p b ^ valuationParity p a) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul, hcb, one_pow]
  simp only [oddPrimeHilbertSymbol, mul_pow]
  rw [hsign, hcaPow, hcbPow]
  norm_num

/-- The odd-prime formula is invariant under multiplying its first argument
by a nonzero rational square. -/
lemma oddPrimeHilbertSymbol_mul_sq_left
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (a b x : ℚ) (ha : a ≠ 0) (hx : x ≠ 0) :
    oddPrimeHilbertSymbol p hpodd (a * x ^ 2) b =
      oddPrimeHilbertSymbol p hpodd a b := by
  simp [oddPrimeHilbertSymbol, valuationParity_mul_sq (p := p) a x ha hx,
    oddPrimeUnitCharacter_mul_sq a x ha hx]

/-- The odd-prime formula is invariant under multiplying its second argument
by a nonzero rational square. -/
lemma oddPrimeHilbertSymbol_mul_sq_right
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (a b x : ℚ) (hb : b ≠ 0) (hx : x ≠ 0) :
    oddPrimeHilbertSymbol p hpodd a (b * x ^ 2) =
      oddPrimeHilbertSymbol p hpodd a b := by
  simp [oddPrimeHilbertSymbol, valuationParity_mul_sq (p := p) b x hb hx,
    oddPrimeUnitCharacter_mul_sq b x hb hx]

/-- The real-place Hilbert symbol on rational inputs: it is negative exactly
when both inputs are negative. -/
def realHilbertSymbol (a b : ℚ) : ℤ :=
  if a < 0 ∧ b < 0 then -1 else 1

/-- The real-place formula is symmetric. -/
lemma realHilbertSymbol_symm (a b : ℚ) :
    realHilbertSymbol a b = realHilbertSymbol b a := by
  simp [realHilbertSymbol, and_comm]

/-- The real-place formula is sign-valued. -/
lemma realHilbertSymbol_sq (a b : ℚ) :
    realHilbertSymbol a b ^ 2 = 1 := by
  simp [realHilbertSymbol]

/-- The real-place formula is invariant under multiplying its first argument
by a nonzero rational square. -/
lemma realHilbertSymbol_mul_sq_left (a b x : ℚ) (hx : x ≠ 0) :
    realHilbertSymbol (a * x ^ 2) b = realHilbertSymbol a b := by
  have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  simp [realHilbertSymbol, mul_neg_iff, hxpos, not_lt_of_ge hxpos.le]

/-- The real-place formula is invariant under multiplying its second argument
by a nonzero rational square. -/
lemma realHilbertSymbol_mul_sq_right (a b x : ℚ) (hx : x ≠ 0) :
    realHilbertSymbol a (b * x ^ 2) = realHilbertSymbol a b := by
  rw [realHilbertSymbol_symm, realHilbertSymbol_mul_sq_left b a x hx,
    realHilbertSymbol_symm]

/-- An explicit odd integer representing the `2`-adic unit part of a
nonzero rational number modulo eight.

The denominator is multiplied rather than inverted because every odd residue
modulo eight is its own inverse. -/
def dyadicUnitRepresentative (q : ℚ) : ℤ :=
  (if q < 0 then -1 else 1) *
    (pFreeNatPart 2 q.num.natAbs : ℤ) * (pFreeNatPart 2 q.den : ℤ)

private lemma pFreeNatPart_two_odd {n : ℕ} (hn : n ≠ 0) :
    Odd (pFreeNatPart 2 n) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact prime_not_dvd_pFreeNatPart (by norm_num) hn

/-- The explicit dyadic unit representative of a nonzero rational number is
odd. -/
lemma dyadicUnitRepresentative_odd {q : ℚ} (hq : q ≠ 0) :
    Odd (dyadicUnitRepresentative q) := by
  have hnum0 : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hq
  have hnumOdd : Odd (pFreeNatPart 2 q.num.natAbs : ℤ) :=
    (Int.odd_coe_nat _).mpr (pFreeNatPart_two_odd hnum0)
  have hdenOdd : Odd (pFreeNatPart 2 q.den : ℤ) :=
    (Int.odd_coe_nat _).mpr (pFreeNatPart_two_odd q.den_nz)
  have hsign : Odd (if q < 0 then (-1 : ℤ) else 1) := by
    split <;> norm_num
  exact (hsign.mul hnumOdd).mul hdenOdd

private lemma odd_int_sq_cast_zmod_eight {z : ℤ} (hz : Odd z) :
    (z : ZMod 8) ^ 2 = 1 := by
  rw [← Int.cast_pow, ← Int.cast_one,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hz with ⟨k, hk⟩
  rcases Int.even_mul_succ_self k with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  rw [hk]
  calc
    1 - (2 * k + 1) ^ 2 = -4 * (k * (k + 1)) := by ring
    _ = 8 * -m := by rw [hm]; ring

private lemma pFreeNatPart_sq_cast_zmod_eight {n : ℕ} (hn : n ≠ 0) :
    ((pFreeNatPart 2 n : ℕ) : ZMod 8) ^ 2 = 1 := by
  simpa only [Int.cast_natCast] using
    odd_int_sq_cast_zmod_eight
      ((Int.odd_coe_nat _).mpr (pFreeNatPart_two_odd hn))

/-- The explicit dyadic unit representative is multiplicative modulo eight on
nonzero rational inputs. -/
lemma dyadicUnitRepresentative_mul_cast
    (q r : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) :
    (dyadicUnitRepresentative (q * r) : ZMod 8) =
      dyadicUnitRepresentative q * dyadicUnitRepresentative r := by
  let s := q * r
  let g := (q.num * r.num).natAbs.gcd (q.den * r.den)
  have hg : g ≠ 0 := by
    apply Nat.gcd_ne_zero_left
    simp
    exact ⟨hq, hr⟩
  have hnumInt := Rat.num_mul_num_eq_num_mul_gcd q r
  have hdenNat := Rat.den_mul_den_eq_den_mul_gcd q r
  have hnumNat :
      q.num.natAbs * r.num.natAbs = s.num.natAbs * g := by
    have h := congrArg Int.natAbs hnumInt
    simpa [s, g, Int.natAbs_mul, Int.natAbs_natCast] using h
  have hdenNat' : q.den * r.den = s.den * g := by
    simpa [s, g] using hdenNat
  have hnum := congrArg (pFreeNatPart 2) hnumNat
  have hden := congrArg (pFreeNatPart 2) hdenNat'
  simp only [pFreeNatPart_mul] at hnum hden
  have hgSq := pFreeNatPart_sq_cast_zmod_eight hg
  have hprod :
      (pFreeNatPart 2 s.num.natAbs : ZMod 8) * pFreeNatPart 2 s.den =
        (pFreeNatPart 2 q.num.natAbs * pFreeNatPart 2 q.den) *
          (pFreeNatPart 2 r.num.natAbs * pFreeNatPart 2 r.den) := by
    have hnumZ := congrArg (fun n : ℕ => (n : ZMod 8)) hnum
    have hdenZ := congrArg (fun n : ℕ => (n : ZMod 8)) hden
    push_cast at hnumZ hdenZ
    calc
      (pFreeNatPart 2 s.num.natAbs : ZMod 8) * pFreeNatPart 2 s.den =
          ((pFreeNatPart 2 s.num.natAbs : ZMod 8) * pFreeNatPart 2 s.den) *
            (pFreeNatPart 2 g : ZMod 8) ^ 2 := by rw [hgSq, mul_one]
      _ = (pFreeNatPart 2 s.num.natAbs * pFreeNatPart 2 g) *
          (pFreeNatPart 2 s.den * pFreeNatPart 2 g) := by ring
      _ = _ := by rw [← hnumZ, ← hdenZ]; ring
  have hcast (t : ℚ) :
      (dyadicUnitRepresentative t : ZMod 8) =
        ((if t < 0 then (-1 : ℤ) else 1) : ZMod 8) *
          pFreeNatPart 2 t.num.natAbs * pFreeNatPart 2 t.den := by
    simp [dyadicUnitRepresentative]
  change (dyadicUnitRepresentative s : ZMod 8) = _
  rw [hcast, hcast, hcast, mul_assoc, hprod]
  by_cases hqneg : q < 0 <;> by_cases hrneg : r < 0
  · have hspos : ¬s < 0 :=
      not_lt_of_ge (mul_pos_of_neg_of_neg hqneg hrneg).le
    simp only [if_neg hspos, if_pos hqneg, if_pos hrneg]
    ring
  · have hsneg : s < 0 := by
      have hrpos : 0 < r :=
        lt_of_le_of_ne (not_lt.mp hrneg) (Ne.symm hr)
      exact mul_neg_of_neg_of_pos hqneg hrpos
    simp only [if_pos hsneg, if_pos hqneg, if_neg hrneg]
    ring
  · have hsneg : s < 0 := by
      have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hqneg) (Ne.symm hq)
      exact mul_neg_of_pos_of_neg hqpos hrneg
    simp only [if_pos hsneg, if_neg hqneg, if_pos hrneg]
    ring
  · have hspos : ¬s < 0 := by
      have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hqneg) (Ne.symm hq)
      have hrpos : 0 < r :=
        lt_of_le_of_ne (not_lt.mp hrneg) (Ne.symm hr)
      exact not_lt_of_ge (mul_pos hqpos hrpos).le
    simp only [if_neg hspos, if_neg hqneg, if_neg hrneg]
    ring

/-- Removing one rational factor of two does not change the explicit dyadic
unit representative modulo eight. -/
lemma dyadicUnitRepresentative_div_two_cast (q : ℚ) (hq : q ≠ 0) :
    (dyadicUnitRepresentative (q / 2) : ZMod 8) =
      dyadicUnitRepresentative q := by
  have hmul := dyadicUnitRepresentative_mul_cast (q / 2) 2
    (div_ne_zero hq (by norm_num)) (by norm_num)
  norm_num [dyadicUnitRepresentative, pFreeNatPart] at hmul ⊢
  exact hmul.symm

/-- The dyadic unit representative of `-q*r` is the negative product of the
two unit representatives modulo eight. -/
lemma dyadicUnitRepresentative_neg_mul_cast
    (q r : ℚ) (hq : q ≠ 0) (hr : r ≠ 0) :
    (dyadicUnitRepresentative (-q * r) : ZMod 8) =
      -dyadicUnitRepresentative q * dyadicUnitRepresentative r := by
  have hnegOne : (dyadicUnitRepresentative (-1 : ℚ) : ZMod 8) = -1 := by
    norm_num [dyadicUnitRepresentative, pFreeNatPart]
  rw [show -q = (-1 : ℚ) * q by ring,
    dyadicUnitRepresentative_mul_cast ((-1 : ℚ) * q) r
      (mul_ne_zero (by norm_num) hq) hr,
    dyadicUnitRepresentative_mul_cast (-1 : ℚ) q (by norm_num) hq,
    hnegOne]
  ring

/-- Multiplication by a nonzero rational square leaves the explicit dyadic
unit representative unchanged modulo eight. -/
lemma dyadicUnitRepresentative_mul_sq_cast
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    (dyadicUnitRepresentative (q * x ^ 2) : ZMod 8) =
      dyadicUnitRepresentative q := by
  obtain ⟨g, hg, hnumRaw, hdenRaw⟩ :=
    exists_mul_sq_num_den_normalization q x hq hx
  have hnum := congrArg (pFreeNatPart 2) hnumRaw
  have hden := congrArg (pFreeNatPart 2) hdenRaw
  simp only [pFreeNatPart_mul] at hnum hden
  have hxnum : x.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hx
  have hxden : x.den ≠ 0 := x.den_nz
  have hxnumSq := pFreeNatPart_sq_cast_zmod_eight hxnum
  have hxdenSq := pFreeNatPart_sq_cast_zmod_eight hxden
  have hgSq := pFreeNatPart_sq_cast_zmod_eight hg
  have hnumZ :
      (pFreeNatPart 2 q.num.natAbs : ZMod 8) =
        pFreeNatPart 2 (q * x ^ 2).num.natAbs * pFreeNatPart 2 g := by
    have h := congrArg (fun n : ℕ => (n : ZMod 8)) hnum
    push_cast at h
    simpa [← pow_two, hxnumSq] using h
  have hdenZ :
      (pFreeNatPart 2 q.den : ZMod 8) =
        pFreeNatPart 2 (q * x ^ 2).den * pFreeNatPart 2 g := by
    have h := congrArg (fun n : ℕ => (n : ZMod 8)) hden
    push_cast at h
    simpa [← pow_two, hxdenSq] using h
  have hprod :
      (pFreeNatPart 2 (q * x ^ 2).num.natAbs : ZMod 8) *
          pFreeNatPart 2 (q * x ^ 2).den =
        pFreeNatPart 2 q.num.natAbs * pFreeNatPart 2 q.den := by
    calc
      (pFreeNatPart 2 (q * x ^ 2).num.natAbs : ZMod 8) *
          pFreeNatPart 2 (q * x ^ 2).den =
          ((pFreeNatPart 2 (q * x ^ 2).num.natAbs : ZMod 8) *
            pFreeNatPart 2 (q * x ^ 2).den) *
              (pFreeNatPart 2 g : ZMod 8) ^ 2 := by rw [hgSq, mul_one]
      _ = ((pFreeNatPart 2 (q * x ^ 2).num.natAbs : ZMod 8) *
            pFreeNatPart 2 g) *
          (pFreeNatPart 2 (q * x ^ 2).den * pFreeNatPart 2 g) := by ring
      _ = _ := by rw [← hnumZ, ← hdenZ]
  have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hsign : q * x ^ 2 < 0 ↔ q < 0 := by
    simp [mul_neg_iff, hxpos, not_lt_of_ge hxpos.le]
  have hcast (t : ℚ) :
      (dyadicUnitRepresentative t : ZMod 8) =
        ((if t < 0 then (-1 : ℤ) else 1) : ZMod 8) *
          pFreeNatPart 2 t.num.natAbs * pFreeNatPart 2 t.den := by
    simp [dyadicUnitRepresentative]
  rw [hcast, hcast, if_congr hsign rfl]
  rw [mul_assoc, hprod, ← mul_assoc]
  rfl

/-- The first standard dyadic unit exponent is integral for nonzero rational
inputs. -/
lemma two_dvd_dyadicUnitRepresentative_sub_one {q : ℚ} (hq : q ≠ 0) :
    (2 : ℤ) ∣ dyadicUnitRepresentative q - 1 := by
  rcases dyadicUnitRepresentative_odd hq with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

/-- The second standard dyadic unit exponent is integral for nonzero rational
inputs. -/
lemma eight_dvd_dyadicUnitRepresentative_sq_sub_one {q : ℚ} (hq : q ≠ 0) :
    (8 : ℤ) ∣ dyadicUnitRepresentative q ^ 2 - 1 := by
  rcases dyadicUnitRepresentative_odd hq with ⟨k, hk⟩
  rcases Int.even_mul_succ_self k with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  rw [hk]
  nlinarith

/-- The parity of `(u - 1) / 2` for the odd dyadic unit representative. -/
def dyadicUnitEpsilon (q : ℚ) : ℕ :=
  (((dyadicUnitRepresentative q - 1) / 2) % 2).natAbs

/-- The parity of `(u^2 - 1) / 8` for the odd dyadic unit representative. -/
def dyadicUnitOmega (q : ℚ) : ℕ :=
  (((dyadicUnitRepresentative q ^ 2 - 1) / 8) % 2).natAbs

/-- Multiplication by a nonzero rational square does not change the first
dyadic unit exponent. -/
lemma dyadicUnitEpsilon_mul_sq
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    dyadicUnitEpsilon (q * x ^ 2) = dyadicUnitEpsilon q := by
  have hcast := dyadicUnitRepresentative_mul_sq_cast q x hq hx
  have hdiv : (8 : ℤ) ∣
      dyadicUnitRepresentative q - dyadicUnitRepresentative (q * x ^ 2) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hcast
  rcases hdiv with ⟨k, hk⟩
  unfold dyadicUnitEpsilon
  congr 1
  omega

/-- Multiplication by a nonzero rational square does not change the second
dyadic unit exponent. -/
lemma dyadicUnitOmega_mul_sq
    (q x : ℚ) (hq : q ≠ 0) (hx : x ≠ 0) :
    dyadicUnitOmega (q * x ^ 2) = dyadicUnitOmega q := by
  have hcast := dyadicUnitRepresentative_mul_sq_cast q x hq hx
  have hdiv : (8 : ℤ) ∣
      dyadicUnitRepresentative q - dyadicUnitRepresentative (q * x ^ 2) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hcast
  rcases hdiv with ⟨k, hk⟩
  let t := -dyadicUnitRepresentative q * k + 4 * k ^ 2
  have hsq :
      dyadicUnitRepresentative (q * x ^ 2) ^ 2 - 1 =
        (dyadicUnitRepresentative q ^ 2 - 1) + 16 * t := by
    dsimp [t]
    have hu : dyadicUnitRepresentative (q * x ^ 2) =
        dyadicUnitRepresentative q - 8 * k := by omega
    rw [hu]
    ring
  unfold dyadicUnitOmega
  congr 1
  omega

/-- The standard dyadic Hilbert-symbol formula on rational inputs. -/
def dyadicHilbertSymbol (a b : ℚ) : ℤ :=
  (-1 : ℤ) ^
    (dyadicUnitEpsilon a * dyadicUnitEpsilon b +
      valuationParity 2 a * dyadicUnitOmega b +
      valuationParity 2 b * dyadicUnitOmega a)

/-- The explicit dyadic Hilbert-symbol formula is symmetric. -/
lemma dyadicHilbertSymbol_symm (a b : ℚ) :
    dyadicHilbertSymbol a b = dyadicHilbertSymbol b a := by
  simp [dyadicHilbertSymbol, Nat.mul_comm, Nat.add_comm]
  ring

/-- The explicit dyadic formula is sign-valued. -/
lemma dyadicHilbertSymbol_sq (a b : ℚ) :
    dyadicHilbertSymbol a b ^ 2 = 1 := by
  simp only [dyadicHilbertSymbol]
  rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
  norm_num

/-- The dyadic formula is invariant under multiplying its first argument by
a nonzero rational square. -/
lemma dyadicHilbertSymbol_mul_sq_left
    (a b x : ℚ) (ha : a ≠ 0) (hx : x ≠ 0) :
    dyadicHilbertSymbol (a * x ^ 2) b = dyadicHilbertSymbol a b := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  simp [dyadicHilbertSymbol, dyadicUnitEpsilon_mul_sq a x ha hx,
    dyadicUnitOmega_mul_sq a x ha hx,
    valuationParity_mul_sq (p := 2) a x ha hx]

/-- The dyadic formula is invariant under multiplying its second argument by
a nonzero rational square. -/
lemma dyadicHilbertSymbol_mul_sq_right
    (a b x : ℚ) (hb : b ≠ 0) (hx : x ≠ 0) :
    dyadicHilbertSymbol a (b * x ^ 2) = dyadicHilbertSymbol a b := by
  rw [dyadicHilbertSymbol_symm,
    dyadicHilbertSymbol_mul_sq_left b a x hb hx,
    dyadicHilbertSymbol_symm]

end Rat

namespace PositiveDefiniteIntegralLattice

/-- At the real place, representation by the quadratic norm is equivalent to
the explicit real Hilbert symbol being one. -/
theorem quadraticNormRepresents_real_iff_realHilbertSymbol_eq_one
    (d c : ℚ) (hd : d ≠ 0) (hc : c ≠ 0) :
    quadraticNormRepresents (d : ℝ) (c : ℝ) ↔
      Rat.realHilbertSymbol d c = 1 := by
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · constructor
    · intro hnorm
      rw [quadraticNormRepresents_iff_exists] at hnorm
      obtain ⟨x, y, hxy⟩ := hnorm
      have hdreal : (d : ℝ) < 0 := by exact_mod_cast hdneg
      have hcreal_nonneg : 0 ≤ (c : ℝ) := by
        rw [← hxy]
        nlinarith [sq_nonneg x, sq_nonneg y]
      have hc_nonneg : 0 ≤ c := by exact_mod_cast hcreal_nonneg
      have hcpos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
      simp [Rat.realHilbertSymbol, hdneg, not_lt_of_ge hcpos.le]
    · intro hsymbol
      have hcnotneg : ¬c < 0 := by
        intro hcneg
        have hneg : Rat.realHilbertSymbol d c = -1 := by
          simp [Rat.realHilbertSymbol, hdneg, hcneg]
        rw [hneg] at hsymbol
        norm_num at hsymbol
      have hcpos : 0 < c :=
        lt_of_le_of_ne (le_of_not_gt hcnotneg) (Ne.symm hc)
      rw [quadraticNormRepresents_iff_exists]
      refine ⟨Real.sqrt (c : ℝ), 0, ?_⟩
      simpa [pow_two] using
        Real.sq_sqrt (show (0 : ℝ) ≤ (c : ℝ) by exact_mod_cast hcpos.le)
  · have hdrealpos : 0 < (d : ℝ) := by exact_mod_cast hdpos
    have hdreal0 : (d : ℝ) ≠ 0 := ne_of_gt hdrealpos
    have hdsq : IsSquare (d : ℝ) := by
      refine ⟨Real.sqrt (d : ℝ), ?_⟩
      simpa [pow_two] using (Real.sq_sqrt hdrealpos.le).symm
    have hnorm : quadraticNormRepresents (d : ℝ) (c : ℝ) :=
      quadraticNormRepresents_of_isSquare (d : ℝ) (c : ℝ)
        (by norm_num) hdreal0 hdsq
    constructor
    · intro _
      simp [Rat.realHilbertSymbol, not_lt_of_ge hdpos.le]
    · intro _
      exact hnorm

end PositiveDefiniteIntegralLattice
