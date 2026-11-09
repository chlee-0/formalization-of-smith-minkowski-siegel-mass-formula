import SMSFormula.RationalHilbertSymbol
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Odd-prime square classes of rational p-adic elements

This module identifies squarehood of a nonzero rational element in `ℚ_[p]`
for odd `p` with even valuation and square residue.  The residue condition is
expressed by `Rat.oddPrimeUnitCharacter`, matching the odd-prime Hilbert
formula in `RationalHilbertSymbol.lean`.
-/

noncomputable section

namespace PadicInt

/-- For odd residue characteristic, a p-adic unit is a square exactly when
its residue is a square. -/
theorem isSquare_iff_isSquare_toZMod_of_isUnit
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare u ↔ IsSquare (toZMod u) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨toZMod x, by simp⟩
  · rintro ⟨r, hr⟩
    let a : ℤ_[p] := (r.val : ℕ)
    let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u
    have hru : r ≠ 0 := by
      intro hr0
      have hzero : toZMod u = 0 := by simpa [hr0] using hr
      have hres : IsLocalRing.residue ℤ_[p] u = 0 := by
        apply residueField.injective
        simpa [toZMod_eq_residueField_comp_residue] using hzero
      exact (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu hres
    have htoa : toZMod a = r := by
      apply ZMod.val_injective
      simp [a]
    have hFa : toZMod (F.eval a) = 0 := by
      simp [F, htoa, pow_two, hr]
    have hFa_mem : F.eval a ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← ker_toZMod, RingHom.mem_ker]
      exact hFa
    have hFa_norm : ‖F.eval a‖ < 1 := by
      rw [← not_isUnit_iff]
      simpa [IsLocalRing.mem_maximalIdeal] using hFa_mem
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have hpdiv : p ∣ 2 :=
        (ZMod.natCast_eq_zero_iff 2 p).mp h
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
      · exact (Fact.out : p.Prime).ne_one hp1
      · exact hpodd hp2
    have hderiv_map :
        toZMod (F.derivative.eval a) = (2 : ZMod p) * r := by
      calc
        toZMod (F.derivative.eval a) =
            toZMod ((2 : ℤ_[p]) * a) := by
              apply congrArg toZMod
              rw [show F.derivative.eval a = (1 + 1) * a by simp [F]]
              rw [one_add_one_eq_two]
        _ = toZMod (2 : ℤ_[p]) * toZMod a := map_mul _ _ _
        _ = (2 : ZMod p) * r := by rw [map_ofNat, htoa]
    have hderiv_res : toZMod (F.derivative.eval a) ≠ 0 := by
      rw [hderiv_map]
      exact mul_ne_zero htwo hru
    have hderiv_unit : IsUnit (F.derivative.eval a) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro hzero
      apply hderiv_res
      rw [toZMod_eq_residueField_comp_residue]
      simp [hzero]
    have hderiv_norm : ‖F.derivative.eval a‖ = 1 :=
      isUnit_iff.mp hderiv_unit
    have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
      simpa [hderiv_norm] using hFa_norm
    obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
    refine ⟨z, ?_⟩
    exact (sub_eq_zero.mp (by simpa [F, pow_two] using hz)).symm

end PadicInt

namespace Rat

private lemma padicValRat_prime_zpow
    (p : ℕ) [Fact p.Prime] (k : ℤ) :
    padicValRat p ((p : ℚ) ^ k) = k := by
  cases k with
  | ofNat n =>
      change padicValRat p ((p : ℚ) ^ n) = (n : ℤ)
      rw [padicValRat.pow]
      · rw [padicValRat.of_nat,
          padicValNat.self (Fact.out : p.Prime).one_lt]
        simp
      · exact_mod_cast (Fact.out : p.Prime).ne_zero
  | negSucc n =>
      change padicValRat p ((p : ℚ) ^ (Int.negSucc n)) = -(n + 1 : ℕ)
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow]
      · rw [padicValRat.of_nat,
          padicValNat.self (Fact.out : p.Prime).one_lt]
        simp
      · exact_mod_cast (Fact.out : p.Prime).ne_zero

private lemma prime_not_dvd_num_den_of_padicValRat_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    (¬p ∣ q.num.natAbs) ∧ (¬p ∣ q.den) := by
  have hnum0 : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hq
  constructor
  · intro hpnum
    have hpden : ¬p ∣ q.den :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (q.reduced.of_dvd_left hpnum)
    have hnumpos :=
      (Fact.out : p.Prime).factorization_pos_of_dvd hnum0 hpnum
    rw [padicValRat_def, padicValInt,
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      Nat.factorization_eq_zero_of_not_dvd hpden] at hv
    omega
  · intro hpden
    have hpnum : ¬p ∣ q.num.natAbs :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (q.reduced.of_dvd_right hpden).symm
    have hdenpos :=
      (Fact.out : p.Prime).factorization_pos_of_dvd q.den_nz hpden
    rw [padicValRat_def, padicValInt,
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      ← Nat.factorization_def _ (Fact.out : p.Prime),
      Nat.factorization_eq_zero_of_not_dvd hpnum] at hv
    omega

private lemma oddPrimeUnitCharacter_eq_legendre_num_mul_den_of_valuation_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    oddPrimeUnitCharacter p q =
      legendreSym p q.num * legendreSym p q.den := by
  obtain ⟨hpnum, hpden⟩ :=
    prime_not_dvd_num_den_of_padicValRat_eq_zero hq hv
  have hnumfac : q.num.natAbs.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpnum
  have hdenfac : q.den.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpden
  have hnumchar :
      (if q < 0 then legendreSym p (-1) else 1) *
          legendreSym p q.num.natAbs = legendreSym p q.num := by
    by_cases hneg : q < 0
    · have hnumneg : q.num < 0 := Rat.num_neg.mpr hneg
      have hnum_eq : q.num = -(q.num.natAbs : ℤ) := by
        rcases Int.natAbs_eq q.num with h | h
        · omega
        · exact h
      rw [if_pos hneg, hnum_eq]
      simpa using (legendreSym.mul p (-1) q.num.natAbs).symm
    · have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hq)
      have hnumpos : 0 < q.num := Rat.num_pos.mpr hqpos
      rw [if_neg hneg, one_mul]
      exact congrArg (legendreSym p) (Int.natAbs_of_nonneg hnumpos.le)
  change
    (if q < 0 then legendreSym p (-1) else 1) *
        legendreSym p (q.num.natAbs / p ^ q.num.natAbs.factorization p) *
          legendreSym p (q.den / p ^ q.den.factorization p) = _
  simp only [hnumfac, hdenfac, pow_zero]
  norm_num only [Int.ediv_one]
  rw [hnumchar]

private lemma oddPrimeUnitCharacter_eq_legendre_residue_of_valuation_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    let u : ℤ_[p] :=
      ⟨(q : ℚ_[p]), by
        rw [Padic.norm_eq_zpow_neg_valuation]
        · simp [Padic.valuation_ratCast, hv]
        · exact_mod_cast hq⟩
    oddPrimeUnitCharacter p q = legendreSym p u.zmodRepr := by
  let u : ℤ_[p] :=
    ⟨(q : ℚ_[p]), by
      rw [Padic.norm_eq_zpow_neg_valuation]
      · simp [Padic.valuation_ratCast, hv]
      · exact_mod_cast hq⟩
  dsimp only
  have hnorm : ‖(q : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation]
    · simp [Padic.valuation_ratCast, hv]
    · exact_mod_cast hq
  have hdenunit : IsUnit (q.den : ℤ_[p]) :=
    PadicInt.isUnit_den q hnorm.le
  have hdenres : PadicInt.toZMod (q.den : ℤ_[p]) ≠ 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    intro hzero
    have hreszero : IsLocalRing.residue ℤ_[p] (q.den : ℤ_[p]) = 0 := by
      apply PadicInt.residueField.injective
      simpa using hzero
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hdenunit hreszero
  have hmul : u * (q.den : ℤ_[p]) = (q.num : ℤ_[p]) := by
    apply Subtype.ext
    change (q : ℚ_[p]) * q.den = q.num
    exact_mod_cast Rat.mul_den_eq_num q
  have hresmul := congrArg PadicInt.toZMod hmul
  rw [map_mul, map_natCast, map_intCast] at hresmul
  have hzrepr :
      ((u.zmodRepr : ℕ) : ZMod p) = PadicInt.toZMod u := by
    apply ZMod.val_injective
    simp [ZMod.val_natCast_of_lt (PadicInt.zmodRepr_lt_p u),
      PadicInt.val_toZMod_eq_zmodRepr]
  have hcharCongr :
      legendreSym p u.zmodRepr * legendreSym p q.den =
        legendreSym p q.num := by
    have hzreprInt :
        ((u.zmodRepr : ℤ) : ZMod p) = PadicInt.toZMod u := by
      exact_mod_cast hzrepr
    unfold legendreSym
    rw [← map_mul]
    apply congrArg (quadraticChar (ZMod p))
    rw [hzreprInt]
    norm_cast
  have hdencharSq : legendreSym p q.den ^ 2 = 1 := by
    apply legendreSym.sq_one
    have hdenres' : (q.den : ZMod p) ≠ 0 := by
      simpa only [map_natCast] using hdenres
    exact_mod_cast hdenres'
  rw [oddPrimeUnitCharacter_eq_legendre_num_mul_den_of_valuation_eq_zero hq hv]
  calc
    legendreSym p q.num * legendreSym p q.den =
        (legendreSym p u.zmodRepr * legendreSym p q.den) *
          legendreSym p q.den := by rw [hcharCongr]
    _ = legendreSym p u.zmodRepr := by
      rw [show legendreSym p u.zmodRepr * legendreSym p q.den *
          legendreSym p q.den =
          legendreSym p u.zmodRepr * legendreSym p q.den ^ 2 by ring,
        hdencharSq, mul_one]

private lemma isSquare_padic_iff_isSquare_padicInt_of_valuation_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat p q = 0) :
    let u : ℤ_[p] :=
      ⟨(q : ℚ_[p]), by
        rw [Padic.norm_eq_zpow_neg_valuation]
        · simp [Padic.valuation_ratCast, hv]
        · exact_mod_cast hq⟩
    IsSquare (q : ℚ_[p]) ↔ IsSquare u := by
  let u : ℤ_[p] :=
    ⟨(q : ℚ_[p]), by
      rw [Padic.norm_eq_zpow_neg_valuation]
      · simp [Padic.valuation_ratCast, hv]
      · exact_mod_cast hq⟩
  dsimp only
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hxzero
      apply hq
      exact_mod_cast (by simpa [hxzero] using hx)
    have hvx : x.valuation = 0 := by
      have h := congrArg Padic.valuation hx
      rw [Padic.valuation_ratCast, hv,
        Padic.valuation_mul hx0 hx0] at h
      omega
    have hnx : ‖x‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hx0, hvx]
      simp
    refine ⟨⟨x, hnx.le⟩, ?_⟩
    exact Subtype.ext hx
  · rintro ⟨x, hx⟩
    refine ⟨(x : ℚ_[p]), ?_⟩
    exact congrArg Subtype.val hx

/-- A rational p-adic unit is a square exactly when its explicit unit-part
Legendre character is one. -/
theorem isSquare_padic_iff_oddPrimeUnitCharacter_eq_one_of_valuation_eq_zero
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q = 0) :
    IsSquare (q : ℚ_[p]) ↔ oddPrimeUnitCharacter p q = 1 := by
  let u : ℤ_[p] :=
    ⟨(q : ℚ_[p]), by
      rw [Padic.norm_eq_zpow_neg_valuation]
      · simp [Padic.valuation_ratCast, hv]
      · exact_mod_cast hq⟩
  have hnorm : ‖u‖ = 1 := by
    change ‖(q : ℚ_[p])‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation]
    · simp [Padic.valuation_ratCast, hv]
    · exact_mod_cast hq
  have hu : IsUnit u := PadicInt.isUnit_iff.mpr hnorm
  have hres0 : PadicInt.toZMod u ≠ 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    intro hzero
    have hreszero : IsLocalRing.residue ℤ_[p] u = 0 := by
      apply PadicInt.residueField.injective
      simpa using hzero
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hreszero
  have hzrepr :
      ((u.zmodRepr : ℕ) : ZMod p) = PadicInt.toZMod u := by
    apply ZMod.val_injective
    simp [ZMod.val_natCast_of_lt (PadicInt.zmodRepr_lt_p u),
      PadicInt.val_toZMod_eq_zmodRepr]
  have hpadicInt : IsSquare (q : ℚ_[p]) ↔ IsSquare u := by
    simpa [u] using
      (isSquare_padic_iff_isSquare_padicInt_of_valuation_eq_zero hq hv)
  rw [hpadicInt]
  rw [PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hu]
  rw [← hzrepr]
  have hcast :
      ((u.zmodRepr : ℤ) : ZMod p) = ((u.zmodRepr : ℕ) : ZMod p) := by
    norm_cast
  have hnonzeroNat : ((u.zmodRepr : ℕ) : ZMod p) ≠ 0 :=
    hzrepr.trans_ne hres0
  have hnonzeroInt : ((u.zmodRepr : ℤ) : ZMod p) ≠ 0 := by
    rw [hcast]
    exact hnonzeroNat
  have hleg :
      IsSquare ((u.zmodRepr : ℕ) : ZMod p) ↔
        legendreSym p u.zmodRepr = 1 := by
    rw [← hcast]
    exact (legendreSym.eq_one_iff p hnonzeroInt).symm
  rw [hleg]
  rw [oddPrimeUnitCharacter_eq_legendre_residue_of_valuation_eq_zero hq hv]

/-- A rational element of even p-adic valuation can be multiplied by a
nonzero rational square so that its valuation becomes zero. -/
theorem exists_square_normalization_of_valuationParity_eq_zero
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hpar : valuationParity p q = 0) :
    ∃ x : ℚ, x ≠ 0 ∧ padicValRat p (q * x ^ 2) = 0 := by
  have hem : padicValRat p q % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one (padicValRat p q) with h | h
    · exact h
    · simp [valuationParity, h] at hpar
  have heven : Even (padicValRat p q) := Int.even_iff.mpr hem
  obtain ⟨k, hk⟩ := heven
  let x : ℚ := (p : ℚ) ^ (-k : ℤ)
  have hx : x ≠ 0 := zpow_ne_zero _ (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine ⟨x, hx, ?_⟩
  rw [padicValRat.mul hq (pow_ne_zero 2 hx), padicValRat.pow hx]
  change padicValRat p q + 2 * padicValRat p ((p : ℚ) ^ (-k : ℤ)) = 0
  rw [padicValRat_prime_zpow]
  omega

/-- A rational element of odd p-adic valuation can be multiplied by a
nonzero rational square so that its valuation becomes exactly one. -/
theorem exists_square_normalization_of_valuationParity_eq_one
    {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hpar : valuationParity p q = 1) :
    ∃ x : ℚ, x ≠ 0 ∧ padicValRat p (q * x ^ 2) = 1 := by
  have hem : padicValRat p q % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one (padicValRat p q) with h | h
    · simp [valuationParity, h] at hpar
    · exact h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, padicValRat p q = 2 * k + 1 := by
    exact ⟨padicValRat p q / 2, by omega⟩
  let x : ℚ := (p : ℚ) ^ (-k : ℤ)
  have hx : x ≠ 0 := zpow_ne_zero _ (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine ⟨x, hx, ?_⟩
  rw [padicValRat.mul hq (pow_ne_zero 2 hx), padicValRat.pow hx]
  change padicValRat p q + 2 * padicValRat p ((p : ℚ) ^ (-k : ℤ)) = 1
  rw [padicValRat_prime_zpow, hk]
  omega

/-- Odd-prime square classes of rational elements in `ℚ_[p]` are classified
by valuation parity and the Legendre character of the unit part. -/
theorem isSquare_padic_iff_valuationParity_and_oddPrimeUnitCharacter
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {q : ℚ} (hq : q ≠ 0) :
    IsSquare (q : ℚ_[p]) ↔
      valuationParity p q = 0 ∧ oddPrimeUnitCharacter p q = 1 := by
  constructor
  · intro hsq
    have heven := padicValRat_even_of_isSquare hq hsq
    have hpar : valuationParity p q = 0 := by
      have hem := Int.even_iff.mp heven
      simp [valuationParity, hem]
    refine ⟨hpar, ?_⟩
    obtain ⟨x, hx, hv⟩ :=
      exists_square_normalization_of_valuationParity_eq_zero hq hpar
    have hxsq : IsSquare ((x : ℚ_[p]) ^ 2) :=
      ⟨(x : ℚ_[p]), by simp [pow_two]⟩
    have hnormalized : IsSquare ((q * x ^ 2 : ℚ) : ℚ_[p]) := by
      simpa only [map_mul, map_pow] using hsq.mul hxsq
    have hchar :=
      (isSquare_padic_iff_oddPrimeUnitCharacter_eq_one_of_valuation_eq_zero
        hpodd (mul_ne_zero hq (pow_ne_zero 2 hx)) hv).mp hnormalized
    rw [oddPrimeUnitCharacter_mul_sq q x hq hx] at hchar
    exact hchar
  · rintro ⟨hpar, hchar⟩
    obtain ⟨x, hx, hv⟩ :=
      exists_square_normalization_of_valuationParity_eq_zero hq hpar
    have hxpadic : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx
    have hcharNormalized : oddPrimeUnitCharacter p (q * x ^ 2) = 1 := by
      rw [oddPrimeUnitCharacter_mul_sq q x hq hx]
      exact hchar
    have hnormalized : IsSquare ((q * x ^ 2 : ℚ) : ℚ_[p]) :=
      (isSquare_padic_iff_oddPrimeUnitCharacter_eq_one_of_valuation_eq_zero
        hpodd (mul_ne_zero hq (pow_ne_zero 2 hx)) hv).mpr hcharNormalized
    have hxsq : IsSquare ((x : ℚ_[p]) ^ 2) :=
      ⟨(x : ℚ_[p]), by simp [pow_two]⟩
    have hdiv := hnormalized.div hxsq
    have hcast :
        (((q * x ^ 2 : ℚ) : ℚ_[p])) =
          (q : ℚ_[p]) * (x : ℚ_[p]) ^ 2 := by norm_cast
    rw [hcast] at hdiv
    simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hxpadic)] using hdiv

end Rat
