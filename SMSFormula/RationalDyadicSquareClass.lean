import SMSFormula.RationalPadicNorm

/-!
# Rational dyadic square classes

This module identifies square units in `ℚ_[2]` by their residue modulo eight
and completes the rational square-class bridge to the explicit dyadic unit
representative used by `RationalHilbertSymbol.lean`.
-/

noncomputable section

namespace PadicInt

/-- Every unit modulo eight has square one. -/
lemma zmod_eight_sq_eq_one_of_isUnit
    (x : ZMod 8) (hx : IsUnit x) :
    x ^ 2 = 1 := by
  have hxcast : (x.val : ZMod 8) = x := ZMod.natCast_zmod_val x
  have hcoprime : x.val.Coprime 8 := by
    rw [← ZMod.isUnit_iff_coprime]
    simpa [hxcast] using hx
  rw [← hxcast, ← Nat.cast_pow, ← Nat.cast_one,
    ZMod.natCast_eq_natCast_iff]
  have hxval : x.val < 8 := x.val_lt
  interval_cases h : x.val
  all_goals norm_num at hcoprime
  all_goals norm_num

/-- A 2-adic integral unit is a square exactly when its residue modulo eight
is one. -/
theorem isSquare_coe_iff_toZModPow_three_eq_one_of_isUnit
    {u : ℤ_[2]} (hu : IsUnit u) :
    IsSquare (u : ℚ_[2]) ↔ toZModPow 3 u = 1 := by
  rw [isSquare_coe_iff_isSquare_of_isUnit hu]
  constructor
  · rintro ⟨x, rfl⟩
    have hxunit : IsUnit x := by
      apply (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      simpa [pow_two] using hu
    have hmapunit : IsUnit (toZModPow 3 x) :=
      hxunit.map (toZModPow 3)
    simpa [pow_two] using
      zmod_eight_sq_eq_one_of_isUnit (toZModPow 3 x) hmapunit
  · intro hmod
    let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C u
    have hmem :
        1 - u ∈ (Ideal.span {((2 : ℤ_[2]) ^ 3)} : Ideal ℤ_[2]) := by
      have hker :
          1 - u ∈ RingHom.ker (toZModPow 3 : ℤ_[2] →+* ZMod 8) := by
        rw [RingHom.mem_ker]
        simpa only [map_sub, map_one] using sub_eq_zero.mpr hmod.symm
      rw [ker_toZModPow] at hker
      exact hker
    have hle : ‖1 - u‖ ≤ (2 : ℝ) ^ (-3 : ℤ) :=
      (norm_le_pow_iff_mem_span_pow (1 - u) 3).2 hmem
    have hFeval : F.aeval (1 : ℤ_[2]) = 1 - u := by
      simp [F]
    have hdeval : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
      norm_num [F]
    have hnorm :
        ‖F.aeval (1 : ℤ_[2])‖ <
          ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
      have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ :=
        @norm_p 2 inferInstance
      rw [hFeval, hdeval, hnormTwo]
      exact lt_of_le_of_lt hle (by norm_num)
    obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
    refine ⟨z, ?_⟩
    exact (sub_eq_zero.mp (by simpa [F, pow_two] using hz)).symm

end PadicInt

namespace Rat

private lemma two_not_dvd_num_den_of_padicValRat_eq_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    (¬2 ∣ q.num.natAbs) ∧ (¬2 ∣ q.den) := by
  have hnum0 : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hq
  constructor
  · intro hpnum
    have hpden : ¬2 ∣ q.den :=
      Nat.prime_two.coprime_iff_not_dvd.mp
        (q.reduced.of_dvd_left hpnum)
    have hnumpos := Nat.prime_two.factorization_pos_of_dvd hnum0 hpnum
    rw [padicValRat_def, padicValInt,
      ← Nat.factorization_def _ Nat.prime_two,
      ← Nat.factorization_def _ Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hpden] at hv
    omega
  · intro hpden
    have hpnum : ¬2 ∣ q.num.natAbs :=
      Nat.prime_two.coprime_iff_not_dvd.mp
        (q.reduced.of_dvd_right hpden).symm
    have hdenpos := Nat.prime_two.factorization_pos_of_dvd q.den_nz hpden
    rw [padicValRat_def, padicValInt,
      ← Nat.factorization_def _ Nat.prime_two,
      ← Nat.factorization_def _ Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hpnum] at hv
    omega

private lemma dyadicUnitRepresentative_eq_num_mul_den_of_valuation_eq_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    dyadicUnitRepresentative q = q.num * q.den := by
  obtain ⟨hnum, hden⟩ :=
    two_not_dvd_num_den_of_padicValRat_eq_zero hq hv
  have hnumfac : q.num.natAbs.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnum
  have hdenfac : q.den.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hden
  have hsignNum :
      (if q < 0 then (-1 : ℤ) else 1) * q.num.natAbs = q.num := by
    by_cases hneg : q < 0
    · have hnumneg : q.num < 0 := Rat.num_neg.mpr hneg
      have hnum_eq : q.num = -(q.num.natAbs : ℤ) := by
        rcases Int.natAbs_eq q.num with h | h
        · omega
        · exact h
      rw [if_pos hneg, hnum_eq]
      simp
    · have hqpos : 0 < q :=
        lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hq)
      have hnumpos : 0 < q.num := Rat.num_pos.mpr hqpos
      rw [if_neg hneg, one_mul]
      exact Int.natAbs_of_nonneg hnumpos.le
  simp only [dyadicUnitRepresentative, pFreeNatPart, hnumfac, hdenfac,
    pow_zero, Nat.div_one]
  rw [hsignNum]

/-- A valuation-zero rational has a canonical 2-adic integral-unit
representative whose residue modulo eight is its explicit dyadic unit
representative. -/
theorem exists_padicInt_unit_of_padicValRat_eq_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    ∃ u : ℤ_[2], IsUnit u ∧
      (u : ℚ_[2]) = (q : ℚ_[2]) ∧
      PadicInt.toZModPow 3 u =
        (dyadicUnitRepresentative q : ZMod 8) := by
  let u : ℤ_[2] :=
    ⟨(q : ℚ_[2]), by
      rw [Padic.norm_eq_zpow_neg_valuation]
      · simp [Padic.valuation_ratCast, hv]
      · exact_mod_cast hq⟩
  have hu : IsUnit u := by
    rw [PadicInt.isUnit_iff]
    change ‖(q : ℚ_[2])‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation]
    · simp [Padic.valuation_ratCast, hv]
    · exact_mod_cast hq
  obtain ⟨_, hden⟩ :=
    two_not_dvd_num_den_of_padicValRat_eq_zero hq hv
  have hdenCoprime : q.den.Coprime 8 := by
    have hcop : q.den.Coprime 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hden).symm
    simpa using hcop.pow_right 3
  have hdenUnit : IsUnit (q.den : ZMod 8) :=
    (ZMod.isUnit_iff_coprime q.den 8).2 hdenCoprime
  have hdenSq : (q.den : ZMod 8) ^ 2 = 1 :=
    PadicInt.zmod_eight_sq_eq_one_of_isUnit q.den hdenUnit
  have hmul : u * (q.den : ℤ_[2]) = (q.num : ℤ_[2]) := by
    apply Subtype.ext
    change (q : ℚ_[2]) * q.den = q.num
    exact_mod_cast Rat.mul_den_eq_num q
  have hres := congrArg (PadicInt.toZModPow 3) hmul
  simp only [map_mul, map_natCast, map_intCast] at hres
  refine ⟨u, hu, rfl, ?_⟩
  rw [dyadicUnitRepresentative_eq_num_mul_den_of_valuation_eq_zero hq hv]
  push_cast
  calc
    PadicInt.toZModPow 3 u = PadicInt.toZModPow 3 u * 1 := by ring
    _ = PadicInt.toZModPow 3 u * (q.den : ZMod 8) ^ 2 := by rw [hdenSq]
    _ = (PadicInt.toZModPow 3 u * (q.den : ZMod 8)) * q.den := by ring
    _ = (q.num : ZMod 8) * q.den := by rw [hres]

/-- For a rational 2-adic unit, squarehood is equivalent to its explicit odd
unit representative being one modulo eight. -/
theorem isSquare_padic_iff_dyadicUnitRepresentative_of_valuation_eq_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    IsSquare (q : ℚ_[2]) ↔
      (dyadicUnitRepresentative q : ZMod 8) = 1 := by
  obtain ⟨u, hu, hucast, hmap⟩ :=
    exists_padicInt_unit_of_padicValRat_eq_zero hq hv
  rw [← hucast]
  rw [PadicInt.isSquare_coe_iff_toZModPow_three_eq_one_of_isUnit hu, hmap]

/-- Rational square classes in `ℚ_[2]` are classified by valuation parity and
the residue modulo eight of their explicit odd unit representative. -/
theorem isSquare_padic_iff_valuationParity_and_dyadicUnitRepresentative
    {q : ℚ} (hq : q ≠ 0) :
    IsSquare (q : ℚ_[2]) ↔
      valuationParity 2 q = 0 ∧
        (dyadicUnitRepresentative q : ZMod 8) = 1 := by
  constructor
  · intro hsq
    have heven := padicValRat_even_of_isSquare hq hsq
    have hpar : valuationParity 2 q = 0 := by
      have hem := Int.even_iff.mp heven
      simp [valuationParity, hem]
    refine ⟨hpar, ?_⟩
    obtain ⟨x, hx, hv⟩ :=
      exists_square_normalization_of_valuationParity_eq_zero hq hpar
    have hxsq : IsSquare ((x : ℚ_[2]) ^ 2) :=
      ⟨(x : ℚ_[2]), by simp [pow_two]⟩
    have hnormalized : IsSquare ((q * x ^ 2 : ℚ) : ℚ_[2]) := by
      simpa only [map_mul, map_pow] using hsq.mul hxsq
    have hrep :=
      (isSquare_padic_iff_dyadicUnitRepresentative_of_valuation_eq_zero
        (mul_ne_zero hq (pow_ne_zero 2 hx)) hv).mp hnormalized
    rw [dyadicUnitRepresentative_mul_sq_cast q x hq hx] at hrep
    exact hrep
  · rintro ⟨hpar, hrep⟩
    obtain ⟨x, hx, hv⟩ :=
      exists_square_normalization_of_valuationParity_eq_zero hq hpar
    have hxpadic : (x : ℚ_[2]) ≠ 0 := by exact_mod_cast hx
    have hrepNormalized :
        (dyadicUnitRepresentative (q * x ^ 2) : ZMod 8) = 1 := by
      rw [dyadicUnitRepresentative_mul_sq_cast q x hq hx]
      exact hrep
    have hnormalized : IsSquare ((q * x ^ 2 : ℚ) : ℚ_[2]) :=
      (isSquare_padic_iff_dyadicUnitRepresentative_of_valuation_eq_zero
        (mul_ne_zero hq (pow_ne_zero 2 hx)) hv).mpr hrepNormalized
    have hxsq : IsSquare ((x : ℚ_[2]) ^ 2) :=
      ⟨(x : ℚ_[2]), by simp [pow_two]⟩
    have hdiv := hnormalized.div hxsq
    have hcast :
        (((q * x ^ 2 : ℚ) : ℚ_[2])) =
          (q : ℚ_[2]) * (x : ℚ_[2]) ^ 2 := by norm_cast
    rw [hcast] at hdiv
    simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hxpadic)] using hdiv

end Rat
