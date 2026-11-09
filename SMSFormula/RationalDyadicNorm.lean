import SMSFormula.RationalDyadicSquareClass

/-!
# Dyadic quadratic norms

This module develops the quadratic norm classification over `ℚ_[2]`.  It
handles the unramified nonsplit parameter class whose unit residue is five
modulo eight, then begins the ramified unit classes of residue three and seven.
-/

noncomputable section

namespace Rat

/-- A dyadic unit representative congruent to one modulo eight has epsilon
zero. -/
lemma dyadicUnitEpsilon_eq_zero_of_cast_eq_one
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 1) :
    dyadicUnitEpsilon q = 0 := by
  have hdiv : (8 : ℤ) ∣ 1 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 1 - 8 * k := by omega
  unfold dyadicUnitEpsilon
  rw [hu]
  omega

/-- A dyadic unit representative congruent to one modulo eight has omega
zero. -/
lemma dyadicUnitOmega_eq_zero_of_cast_eq_one
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 1) :
    dyadicUnitOmega q = 0 := by
  have hdiv : (8 : ℤ) ∣ 1 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 1 - 8 * k := by omega
  have hquot :
      (dyadicUnitRepresentative q ^ 2 - 1) / 8 =
        -2 * k + 8 * k ^ 2 := by
    rw [hu]
    apply Int.ediv_eq_of_eq_mul_left
    · norm_num
    · ring
  unfold dyadicUnitOmega
  rw [hquot]
  omega

/-- A dyadic unit representative congruent to five modulo eight has epsilon
zero. -/
lemma dyadicUnitEpsilon_eq_zero_of_cast_eq_five
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 5) :
    dyadicUnitEpsilon q = 0 := by
  have hdiv : (8 : ℤ) ∣ 5 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 5 - 8 * k := by omega
  unfold dyadicUnitEpsilon
  rw [hu]
  omega

/-- A dyadic unit representative congruent to five modulo eight has omega
one. -/
lemma dyadicUnitOmega_eq_one_of_cast_eq_five
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 5) :
    dyadicUnitOmega q = 1 := by
  have hdiv : (8 : ℤ) ∣ 5 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 5 - 8 * k := by omega
  have hquot :
      (dyadicUnitRepresentative q ^ 2 - 1) / 8 =
        3 - 10 * k + 8 * k ^ 2 := by
    rw [hu]
    apply Int.ediv_eq_of_eq_mul_left
    · norm_num
    · ring
  unfold dyadicUnitOmega
  rw [hquot]
  omega

/-- A dyadic unit representative congruent to three modulo eight has epsilon
one. -/
lemma dyadicUnitEpsilon_eq_one_of_cast_eq_three
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 3) :
    dyadicUnitEpsilon q = 1 := by
  have hdiv : (8 : ℤ) ∣ 3 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 3 - 8 * k := by omega
  unfold dyadicUnitEpsilon
  rw [hu]
  omega

/-- A dyadic unit representative congruent to three modulo eight has omega
one. -/
lemma dyadicUnitOmega_eq_one_of_cast_eq_three
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 3) :
    dyadicUnitOmega q = 1 := by
  have hdiv : (8 : ℤ) ∣ 3 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 3 - 8 * k := by omega
  have hquot :
      (dyadicUnitRepresentative q ^ 2 - 1) / 8 =
        1 - 6 * k + 8 * k ^ 2 := by
    rw [hu]
    apply Int.ediv_eq_of_eq_mul_left
    · norm_num
    · ring
  unfold dyadicUnitOmega
  rw [hquot]
  omega

/-- A dyadic unit representative congruent to seven modulo eight has epsilon
one. -/
lemma dyadicUnitEpsilon_eq_one_of_cast_eq_seven
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 7) :
    dyadicUnitEpsilon q = 1 := by
  have hdiv : (8 : ℤ) ∣ 7 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 7 - 8 * k := by omega
  unfold dyadicUnitEpsilon
  rw [hu]
  omega

/-- A dyadic unit representative congruent to seven modulo eight has omega
zero. -/
lemma dyadicUnitOmega_eq_zero_of_cast_eq_seven
    {q : ℚ} (hrep : (dyadicUnitRepresentative q : ZMod 8) = 7) :
    dyadicUnitOmega q = 0 := by
  have hdiv : (8 : ℤ) ∣ 7 - dyadicUnitRepresentative q :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mp hrep
  obtain ⟨k, hk⟩ := hdiv
  have hu : dyadicUnitRepresentative q = 7 - 8 * k := by omega
  have hquot :
      (dyadicUnitRepresentative q ^ 2 - 1) / 8 =
        6 - 14 * k + 8 * k ^ 2 := by
    rw [hu]
    apply Int.ediv_eq_of_eq_mul_left
    · norm_num
    · ring
  unfold dyadicUnitOmega
  rw [hquot]
  omega

/-- Epsilon zero is exactly the pair of odd residues one and five modulo
eight. -/
lemma dyadicUnitEpsilon_eq_zero_iff_cast_eq_one_or_five
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitEpsilon q = 0 ↔
      (dyadicUnitRepresentative q : ZMod 8) = 1 ∨
        (dyadicUnitRepresentative q : ZMod 8) = 5 := by
  constructor
  · intro heps
    rcases dyadicUnitRepresentative_odd hq with ⟨k, hk⟩
    have hkmod : k % 2 = 0 := by
      unfold dyadicUnitEpsilon at heps
      have hquot : (dyadicUnitRepresentative q - 1) / 2 = k := by
        rw [hk]
        omega
      rw [hquot] at heps
      exact Int.natAbs_eq_zero.mp heps
    rcases (Int.even_iff.mpr hkmod) with ⟨m, hm⟩
    rcases Int.emod_two_eq_zero_or_one m with hmmod | hmmod
    · left
      rcases (Int.even_iff.mpr hmmod) with ⟨n, hn⟩
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub
        (dyadicUnitRepresentative q) (1 : ℤ) 8).mpr
      refine ⟨-n, ?_⟩
      rw [hk, hm, hn]
      ring
    · right
      rcases (Int.odd_iff.mpr hmmod) with ⟨n, hn⟩
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub
        (dyadicUnitRepresentative q) (5 : ℤ) 8).mpr
      refine ⟨-n, ?_⟩
      rw [hk, hm, hn]
      ring
  · rintro (hrep | hrep)
    · exact dyadicUnitEpsilon_eq_zero_of_cast_eq_one hrep
    · exact dyadicUnitEpsilon_eq_zero_of_cast_eq_five hrep

/-- Epsilon one is exactly the pair of odd residues three and seven modulo
eight. -/
lemma dyadicUnitEpsilon_eq_one_iff_cast_eq_three_or_seven
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitEpsilon q = 1 ↔
      (dyadicUnitRepresentative q : ZMod 8) = 3 ∨
        (dyadicUnitRepresentative q : ZMod 8) = 7 := by
  constructor
  · intro heps
    rcases dyadicUnitRepresentative_odd hq with ⟨k, hk⟩
    have hkmod : k % 2 = 1 := by
      unfold dyadicUnitEpsilon at heps
      have hquot : (dyadicUnitRepresentative q - 1) / 2 = k := by
        rw [hk]
        omega
      rw [hquot] at heps
      have hkrem : 0 ≤ k % 2 := Int.emod_nonneg _ (by norm_num)
      rcases Int.natAbs_eq_iff.mp heps with h | h <;> omega
    rcases (Int.odd_iff.mpr hkmod) with ⟨m, hm⟩
    rcases Int.emod_two_eq_zero_or_one m with hmmod | hmmod
    · left
      rcases (Int.even_iff.mpr hmmod) with ⟨n, hn⟩
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub
        (dyadicUnitRepresentative q) (3 : ℤ) 8).mpr
      refine ⟨-n, ?_⟩
      rw [hk, hm, hn]
      ring
    · right
      rcases (Int.odd_iff.mpr hmmod) with ⟨n, hn⟩
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub
        (dyadicUnitRepresentative q) (7 : ℤ) 8).mpr
      refine ⟨-n, ?_⟩
      rw [hk, hm, hn]
      ring
  · rintro (hrep | hrep)
    · exact dyadicUnitEpsilon_eq_one_of_cast_eq_three hrep
    · exact dyadicUnitEpsilon_eq_one_of_cast_eq_seven hrep

/-- The dyadic epsilon exponent is represented canonically by zero or one. -/
lemma dyadicUnitEpsilon_eq_zero_or_one (q : ℚ) :
    dyadicUnitEpsilon q = 0 ∨ dyadicUnitEpsilon q = 1 := by
  unfold dyadicUnitEpsilon
  rcases Int.emod_two_eq_zero_or_one
      ((dyadicUnitRepresentative q - 1) / 2) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- The dyadic unit representative of a nonzero rational occupies one of the
four odd residue classes modulo eight. -/
lemma dyadicUnitRepresentative_cast_eq_one_or_three_or_five_or_seven
    {q : ℚ} (hq : q ≠ 0) :
    (dyadicUnitRepresentative q : ZMod 8) = 1 ∨
      (dyadicUnitRepresentative q : ZMod 8) = 3 ∨
      (dyadicUnitRepresentative q : ZMod 8) = 5 ∨
      (dyadicUnitRepresentative q : ZMod 8) = 7 := by
  rcases dyadicUnitEpsilon_eq_zero_or_one q with heps | heps
  · rcases (dyadicUnitEpsilon_eq_zero_iff_cast_eq_one_or_five hq).1 heps with
      hrep | hrep
    · exact Or.inl hrep
    · exact Or.inr (Or.inr (Or.inl hrep))
  · rcases (dyadicUnitEpsilon_eq_one_iff_cast_eq_three_or_seven hq).1 heps with
      hrep | hrep
    · exact Or.inr (Or.inl hrep)
    · exact Or.inr (Or.inr (Or.inr hrep))

private def dyadicResidueEpsilon (u : ZMod 8) : ℕ :=
  if u = 1 ∨ u = 5 then 0 else 1

private def dyadicResidueOmega (u : ZMod 8) : ℕ :=
  if u = 1 ∨ u = 7 then 0 else 1

private lemma dyadicUnitEpsilon_eq_residueEpsilon
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitEpsilon q =
      dyadicResidueEpsilon (dyadicUnitRepresentative q : ZMod 8) := by
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

private lemma dyadicUnitOmega_eq_residueOmega
    {q : ℚ} (hq : q ≠ 0) :
    dyadicUnitOmega q =
      dyadicResidueOmega (dyadicUnitRepresentative q : ZMod 8) := by
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

private lemma dyadicResidue_transport :
    ∀ u v : ZMod 8,
      (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) →
      (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
      (-1 : ℤ) ^
          (dyadicResidueEpsilon u * dyadicResidueEpsilon (-u * v) +
            dyadicResidueOmega (-u * v)) =
        (-1 : ℤ) ^
          (dyadicResidueEpsilon u * dyadicResidueEpsilon v +
            dyadicResidueOmega v + dyadicResidueOmega u) := by
  decide

/-- For two inputs of odd dyadic valuation parity, multiplying the second by
the negative of the first leaves the dyadic Hilbert symbol unchanged. -/
lemma dyadicHilbertSymbol_mul_neg_self_right_of_parity_eq_one
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : valuationParity 2 d = 1)
    (hcpar : valuationParity 2 c = 1) :
    dyadicHilbertSymbol d (-d * c) = dyadicHilbertSymbol d c := by
  have hdc : -d * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hd) hc
  have hdcpar : valuationParity 2 (-d * c) = 0 :=
    valuationParity_neg_mul_eq_zero hd hc hdpar hcpar
  have hdres := dyadicUnitRepresentative_cast_eq_one_or_three_or_five_or_seven hd
  have hcres := dyadicUnitRepresentative_cast_eq_one_or_three_or_five_or_seven hc
  have hmulrep := dyadicUnitRepresentative_neg_mul_cast d c hd hc
  simp only [dyadicHilbertSymbol, hdpar, hcpar, hdcpar, Nat.one_mul,
    Nat.zero_mul, Nat.add_zero]
  rw [dyadicUnitEpsilon_eq_residueEpsilon hd,
    dyadicUnitEpsilon_eq_residueEpsilon hc,
    dyadicUnitEpsilon_eq_residueEpsilon hdc,
    dyadicUnitOmega_eq_residueOmega hd,
    dyadicUnitOmega_eq_residueOmega hc,
    dyadicUnitOmega_eq_residueOmega hdc,
    hmulrep]
  exact dyadicResidue_transport _ _ hdres hcres

end Rat

namespace PadicInt

/-- A root modulo eight whose derivative has 2-adic norm `1 / 2` lifts to an
exact root. -/
theorem exists_polynomial_root_of_root_mod_eight_derivative_norm_half
    (F : Polynomial ℤ_[2]) (a : ℤ_[2])
    (hFa : toZModPow 3 (F.eval a) = 0)
    (hderiv : ‖F.derivative.eval a‖ = (2 : ℝ)⁻¹) :
    ∃ z : ℤ_[2], F.eval z = 0 := by
  have hmem :
      F.eval a ∈ (Ideal.span {((2 : ℤ_[2]) ^ 3)} : Ideal ℤ_[2]) := by
    have hker :
        F.eval a ∈ RingHom.ker (toZModPow 3 : ℤ_[2] →+* ZMod 8) := by
      rw [RingHom.mem_ker]
      exact hFa
    rw [ker_toZModPow] at hker
    exact hker
  have hle : ‖F.eval a‖ ≤ (2 : ℝ) ^ (-3 : ℤ) :=
    (norm_le_pow_iff_mem_span_pow (F.eval a) 3).2 hmem
  have hle' : ‖F.aeval a‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    simpa using hle
  have hderiv' : ‖F.derivative.aeval a‖ = (2 : ℝ)⁻¹ := by
    simpa using hderiv
  have hnorm :
      ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hderiv']
    exact lt_of_le_of_lt hle' (by norm_num)
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  exact ⟨z, hz⟩

/-- For parameter residue five modulo eight, every unit residue is represented
by `x² - d y²`, with one coordinate fixed to one. -/
lemma exists_quadraticNorm_eq_mod_eight_of_parameter_eq_five
    {d c : ZMod 8} (hd : d = 5) (hc : IsUnit c) :
    (∃ y : ZMod 8, 1 - d * y * y = c) ∨
      (∃ x : ZMod 8, x * x - d = c) := by
  subst d
  have hccast : (c.val : ZMod 8) = c := ZMod.natCast_zmod_val c
  have hcoprime : c.val.Coprime 8 := by
    rw [← ZMod.isUnit_iff_coprime]
    simpa [hccast] using hc
  rw [← hccast]
  have hcval : c.val < 8 := c.val_lt
  interval_cases h : c.val
  all_goals norm_num at hcoprime
  · left
    exact ⟨0, by decide⟩
  · right
    exact ⟨0, by decide⟩
  · left
    exact ⟨2, by decide⟩
  · right
    exact ⟨2, by decide⟩

/-- For parameter residue three or seven modulo eight, a unit residue is a
quadratic norm exactly when it is one or five. -/
lemma quadraticNormRepresents_mod_eight_iff_of_parameter_eq_three_or_seven
    {d c : ZMod 8} (hd : d = 3 ∨ d = 7) (hc : IsUnit c) :
    (∃ x y : ZMod 8, x * x - d * y * y = c) ↔ c = 1 ∨ c = 5 := by
  rcases hd with rfl | rfl
  all_goals
    have hccast : (c.val : ZMod 8) = c := ZMod.natCast_zmod_val c
    have hcoprime : c.val.Coprime 8 := by
      rw [← ZMod.isUnit_iff_coprime]
      simpa [hccast] using hc
    rw [← hccast]
    have hcval : c.val < 8 := c.val_lt
    interval_cases h : c.val <;> norm_num at hcoprime
    all_goals decide

/-- In the represented cases of the ramified dyadic unit table, one
coordinate can be fixed to one. -/
lemma exists_quadraticNorm_eq_mod_eight_of_parameter_eq_three_or_seven
    {d c : ZMod 8} (hd : d = 3 ∨ d = 7) (hc : c = 1 ∨ c = 5) :
    (∃ y : ZMod 8, 1 - d * y * y = c) ∨
      (∃ x : ZMod 8, x * x - d = c) := by
  rcases hd with rfl | rfl <;> rcases hc with rfl | rfl
  · left
    exact ⟨0, by decide⟩
  · right
    exact ⟨0, by decide⟩
  · right
    exact ⟨0, by decide⟩
  · right
    exact ⟨2, by decide⟩

/-- Among units modulo eight, `2*u = 6` exactly in residue classes three and
seven. -/
lemma two_mul_eq_six_iff_of_isUnit {u : ZMod 8} (hu : IsUnit u) :
    2 * u = 6 ↔ u = 3 ∨ u = 7 := by
  have hucast : (u.val : ZMod 8) = u := ZMod.natCast_zmod_val u
  have hcoprime : u.val.Coprime 8 := by
    rw [← ZMod.isUnit_iff_coprime]
    simpa [hucast] using hu
  rw [← hucast]
  have huval : u.val < 8 := u.val_lt
  interval_cases h : u.val <;> norm_num at hcoprime
  all_goals decide

/-- Among units modulo eight, `2*u = 2` exactly in residue classes one and
five. -/
lemma two_mul_eq_two_iff_of_isUnit {u : ZMod 8} (hu : IsUnit u) :
    2 * u = 2 ↔ u = 1 ∨ u = 5 := by
  have hucast : (u.val : ZMod 8) = u := ZMod.natCast_zmod_val u
  have hcoprime : u.val.Coprime 8 := by
    rw [← ZMod.isUnit_iff_coprime]
    simpa [hucast] using hu
  rw [← hucast]
  have huval : u.val < 8 := u.val_lt
  interval_cases h : u.val <;> norm_num at hcoprime
  all_goals decide

/-- Unit coordinates and a parameter of residue three or seven give a
quadratic norm bracket of valuation exactly one. -/
theorem quadraticNorm_unit_bracket_valuation_eq_one
    {d x y : ℤ_[2]} (hx : IsUnit x) (hy : IsUnit y)
    (hdres : toZModPow 3 d = 3 ∨ toZModPow 3 d = 7) :
    (x * x - d * y * y).valuation = 1 := by
  let b : ℤ_[2] := x * x - d * y * y
  have hxsq : (toZModPow 3 x) * (toZModPow 3 x) = 1 := by
    simpa [pow_two] using zmod_eight_sq_eq_one_of_isUnit
      (toZModPow 3 x) (hx.map (toZModPow 3))
  have hysq : (toZModPow 3 y) * (toZModPow 3 y) = 1 := by
    simpa [pow_two] using zmod_eight_sq_eq_one_of_isUnit
      (toZModPow 3 y) (hy.map (toZModPow 3))
  have hb8 : toZModPow 3 b = 6 ∨ toZModPow 3 b = 2 := by
    simp only [b, map_sub, map_mul]
    rcases hdres with hdres | hdres
    · left
      rw [hxsq]
      calc
        1 - toZModPow 3 d * toZModPow 3 y * toZModPow 3 y =
            1 - toZModPow 3 d *
              (toZModPow 3 y * toZModPow 3 y) := by ring
        _ = 1 - toZModPow 3 d * 1 := by rw [hysq]
        _ = 6 := by rw [hdres]; decide
    · right
      rw [hxsq]
      calc
        1 - toZModPow 3 d * toZModPow 3 y * toZModPow 3 y =
            1 - toZModPow 3 d *
              (toZModPow 3 y * toZModPow 3 y) := by ring
        _ = 1 - toZModPow 3 d * 1 := by rw [hysq]
        _ = 2 := by rw [hdres]; decide
  have hb4 : toZModPow 2 b = 2 := by
    rw [← cast_toZModPow 2 3 (by omega) b]
    rcases hb8 with hb8 | hb8 <;> rw [hb8] <;> decide
  have hb0 : b ≠ 0 := by
    intro hb
    simp [hb] at hb4
    exact (by decide : (0 : ZMod 4) ≠ 2) hb4
  have hb2 : toZModPow 1 b = 0 := by
    rw [← cast_toZModPow 1 2 (by omega) b, hb4]
    decide
  have hle : 1 ≤ b.valuation := by
    apply (mem_span_pow_iff_le_valuation b hb0 1).1
    rw [← ker_toZModPow, RingHom.mem_ker]
    exact hb2
  have hnle : ¬2 ≤ b.valuation := by
    intro htwo
    have hmem := (mem_span_pow_iff_le_valuation b hb0 2).2 htwo
    rw [← ker_toZModPow, RingHom.mem_ker] at hmem
    rw [hmem] at hb4
    exact (by decide : (0 : ZMod 4) ≠ 2) hb4
  change b.valuation = 1
  omega

/-- For unit coordinates and parameter residue five modulo eight, the
quadratic norm bracket has valuation exactly two. -/
theorem quadraticNorm_unit_bracket_valuation_eq_two
    {d x y : ℤ_[2]} (hx : IsUnit x) (hy : IsUnit y)
    (hdres : toZModPow 3 d = 5) :
    (x * x - d * y * y).valuation = 2 := by
  let b : ℤ_[2] := x * x - d * y * y
  have hxsq : (toZModPow 3 x) * (toZModPow 3 x) = 1 := by
    simpa [pow_two] using zmod_eight_sq_eq_one_of_isUnit
      (toZModPow 3 x) (hx.map (toZModPow 3))
  have hysq : (toZModPow 3 y) * (toZModPow 3 y) = 1 := by
    simpa [pow_two] using zmod_eight_sq_eq_one_of_isUnit
      (toZModPow 3 y) (hy.map (toZModPow 3))
  have hb8 : toZModPow 3 b = 4 := by
    simp only [b, map_sub, map_mul]
    rw [hxsq]
    calc
      1 - toZModPow 3 d * toZModPow 3 y * toZModPow 3 y =
          1 - toZModPow 3 d *
            (toZModPow 3 y * toZModPow 3 y) := by ring
      _ = 1 - toZModPow 3 d * 1 := by rw [hysq]
      _ = 4 := by rw [hdres]; decide
  have hb0 : b ≠ 0 := by
    intro hb
    simp [hb] at hb8
    exact (by decide : (0 : ZMod 8) ≠ 4) hb8
  have hb4 : toZModPow 2 b = 0 := by
    rw [← cast_toZModPow 2 3 (by omega) b, hb8]
    decide
  have hle : 2 ≤ b.valuation := by
    apply (mem_span_pow_iff_le_valuation b hb0 2).1
    rw [← ker_toZModPow, RingHom.mem_ker]
    exact hb4
  have hnle : ¬3 ≤ b.valuation := by
    intro hthree
    have hmem := (mem_span_pow_iff_le_valuation b hb0 3).2 hthree
    rw [← ker_toZModPow, RingHom.mem_ker] at hmem
    rw [hmem] at hb8
    exact (by decide : (0 : ZMod 8) ≠ 4) hb8
  change b.valuation = 2
  omega

end PadicInt

namespace PositiveDefiniteIntegralLattice

/-- A rational parameter of even dyadic valuation has a unit integral
representative of the same prescribed modulo-eight residue, and replacing the
parameter by it preserves every quadratic norm fiber. -/
theorem exists_padicInt_dyadic_unit_parameter_square_normalization
    {d : ℚ} (hd : d ≠ 0) (hdpar : Rat.valuationParity 2 d = 0)
    {r : ZMod 8} (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = r) :
    ∃ x : ℚ, x ≠ 0 ∧ ∃ D : ℤ_[2],
      IsUnit D ∧ PadicInt.toZModPow 3 D = r ∧
      (D : ℚ_[2]) = ((d * x ^ 2 : ℚ) : ℚ_[2]) ∧
      ∀ c : ℚ_[2],
        quadraticNormRepresents (d : ℚ_[2]) c ↔
          quadraticNormRepresents (D : ℚ_[2]) c := by
  obtain ⟨x, hx, hxval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_zero hd hdpar
  obtain ⟨D, hDunit, hDcast, hDres⟩ :=
    Rat.exists_padicInt_unit_of_padicValRat_eq_zero
      (mul_ne_zero hd (pow_ne_zero 2 hx)) hxval
  have hDres' : PadicInt.toZModPow 3 D = r := by
    rw [hDres, Rat.dyadicUnitRepresentative_mul_sq_cast d x hd hx, hdrep]
  refine ⟨x, hx, D, hDunit, hDres', hDcast, ?_⟩
  intro c
  have hxpadic : (x : ℚ_[2]) ≠ 0 := by exact_mod_cast hx
  have htransport := quadraticNormRepresents_iff_mul_sq_parameter
    (K := ℚ_[2]) (d := (d : ℚ_[2])) (c := c) (s := (x : ℚ_[2])) hxpadic
  rw [hDcast]
  simpa using htransport

/-- A rational dyadic-unramified square class has a unit integral parameter
of residue five, and replacing the parameter by it preserves every norm
fiber. -/
theorem exists_padicInt_dyadic_unramified_parameter_square_normalization
    {d : ℚ} (hd : d ≠ 0) (hdpar : Rat.valuationParity 2 d = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 5) :
    ∃ x : ℚ, x ≠ 0 ∧ ∃ D : ℤ_[2],
      IsUnit D ∧ PadicInt.toZModPow 3 D = 5 ∧
      (D : ℚ_[2]) = ((d * x ^ 2 : ℚ) : ℚ_[2]) ∧
      ∀ c : ℚ_[2],
        quadraticNormRepresents (d : ℚ_[2]) c ↔
          quadraticNormRepresents (D : ℚ_[2]) c := by
  exact exists_padicInt_dyadic_unit_parameter_square_normalization
    hd hdpar hdrep

/-- A rational ramified dyadic unit square class has an integral unit
parameter of residue three or seven, with every norm fiber preserved. -/
theorem exists_padicInt_dyadic_ramified_parameter_square_normalization
    {d : ℚ} (hd : d ≠ 0) (hdpar : Rat.valuationParity 2 d = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    ∃ x : ℚ, x ≠ 0 ∧ ∃ D : ℤ_[2],
      IsUnit D ∧
      (PadicInt.toZModPow 3 D = 3 ∨ PadicInt.toZModPow 3 D = 7) ∧
      (D : ℚ_[2]) = ((d * x ^ 2 : ℚ) : ℚ_[2]) ∧
      ∀ c : ℚ_[2],
        quadraticNormRepresents (d : ℚ_[2]) c ↔
          quadraticNormRepresents (D : ℚ_[2]) c := by
  rcases hdrep with hdrep | hdrep
  · obtain ⟨x, hx, D, hDunit, hDres, hDcast, hDnorm⟩ :=
      exists_padicInt_dyadic_unit_parameter_square_normalization
        hd hdpar hdrep
    exact ⟨x, hx, D, hDunit, Or.inl hDres, hDcast, hDnorm⟩
  · obtain ⟨x, hx, D, hDunit, hDres, hDcast, hDnorm⟩ :=
      exists_padicInt_dyadic_unit_parameter_square_normalization
        hd hdpar hdrep
    exact ⟨x, hx, D, hDunit, Or.inr hDres, hDcast, hDnorm⟩

/-- A rational target of even dyadic valuation has a unit integral
representative of the same prescribed modulo-eight residue, and replacing the
target by it preserves every quadratic norm fiber. -/
theorem exists_padicInt_dyadic_unit_target_square_normalization
    {c : ℚ} (hc : c ≠ 0) (hcpar : Rat.valuationParity 2 c = 0)
    {r : ZMod 8} (hcrep : (Rat.dyadicUnitRepresentative c : ZMod 8) = r) :
    ∃ s : ℚ, s ≠ 0 ∧ ∃ C : ℤ_[2],
      IsUnit C ∧ PadicInt.toZModPow 3 C = r ∧
      (C : ℚ_[2]) = ((c * s ^ 2 : ℚ) : ℚ_[2]) ∧
      ∀ d : ℚ_[2],
        quadraticNormRepresents d (c : ℚ_[2]) ↔
          quadraticNormRepresents d (C : ℚ_[2]) := by
  obtain ⟨s, hs, hsval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_zero hc hcpar
  obtain ⟨C, hCunit, hCcast, hCres⟩ :=
    Rat.exists_padicInt_unit_of_padicValRat_eq_zero
      (mul_ne_zero hc (pow_ne_zero 2 hs)) hsval
  have hCres' : PadicInt.toZModPow 3 C = r := by
    rw [hCres, Rat.dyadicUnitRepresentative_mul_sq_cast c s hc hs, hcrep]
  refine ⟨s, hs, C, hCunit, hCres', hCcast, ?_⟩
  intro d
  have hspadic : (s : ℚ_[2]) ≠ 0 := by exact_mod_cast hs
  have htransport := quadraticNormRepresents_iff_mul_sq_target
    (K := ℚ_[2]) (d := d) (c := (c : ℚ_[2])) (s := (s : ℚ_[2])) hspadic
  rw [hCcast]
  simpa using htransport

/-- A rational target of odd dyadic valuation is square-equivalent to twice an
integral unit whose residue is its explicit dyadic unit representative. -/
theorem exists_padicInt_dyadic_twice_unit_target_square_normalization
    {c : ℚ} (hc : c ≠ 0) (hcpar : Rat.valuationParity 2 c = 1) :
    ∃ s : ℚ, s ≠ 0 ∧ ∃ U : ℤ_[2],
      IsUnit U ∧
      PadicInt.toZModPow 3 U =
        (Rat.dyadicUnitRepresentative c : ZMod 8) ∧
      (((2 * U : ℤ_[2]) : ℚ_[2]) = ((c * s ^ 2 : ℚ) : ℚ_[2])) ∧
      ∀ d : ℚ_[2],
        quadraticNormRepresents d (c : ℚ_[2]) ↔
          quadraticNormRepresents d (((2 * U : ℤ_[2]) : ℚ_[2])) := by
  obtain ⟨s, hs, hsval⟩ :=
    Rat.exists_square_normalization_of_valuationParity_eq_one hc hcpar
  have hcs : c * s ^ 2 ≠ 0 := mul_ne_zero hc (pow_ne_zero 2 hs)
  have htwoVal : padicValRat 2 (2 : ℚ) = 1 := by
    have h : padicValInt 2 (2 : ℤ) = 1 :=
      padicValInt.self (by norm_num)
    norm_num [padicValRat, h]
  have huval : padicValRat 2 ((c * s ^ 2) / 2) = 0 := by
    rw [padicValRat.div hcs (by norm_num), hsval, htwoVal]
    norm_num
  obtain ⟨U, hUunit, hUcast, hUres⟩ :=
    Rat.exists_padicInt_unit_of_padicValRat_eq_zero
      (div_ne_zero hcs (by norm_num)) huval
  have hUres' : PadicInt.toZModPow 3 U =
      (Rat.dyadicUnitRepresentative c : ZMod 8) := by
    rw [hUres, Rat.dyadicUnitRepresentative_div_two_cast _ hcs,
      Rat.dyadicUnitRepresentative_mul_sq_cast c s hc hs]
  have htwice : (((2 * U : ℤ_[2]) : ℚ_[2]) =
      ((c * s ^ 2 : ℚ) : ℚ_[2])) := by
    change (2 : ℚ_[2]) * (U : ℚ_[2]) = ((c * s ^ 2 : ℚ) : ℚ_[2])
    rw [hUcast]
    norm_num
    ring
  refine ⟨s, hs, U, hUunit, hUres', htwice, ?_⟩
  intro d
  have hspadic : (s : ℚ_[2]) ≠ 0 := by exact_mod_cast hs
  have htransport := quadraticNormRepresents_iff_mul_sq_target
    (K := ℚ_[2]) (d := d) (c := (c : ℚ_[2])) (s := (s : ℚ_[2])) hspadic
  rw [htwice]
  simpa using htransport

private theorem exists_padicInt_quadraticNorm_eq_of_mod_eight_witness
    {d c : ℤ_[2]} (hd : IsUnit d)
    (hres :
      (∃ y : ZMod 8,
        1 - PadicInt.toZModPow 3 d * y * y = PadicInt.toZModPow 3 c) ∨
      (∃ x : ZMod 8,
        x * x - PadicInt.toZModPow 3 d = PadicInt.toZModPow 3 c)) :
    ∃ x y : ℤ_[2], x * x - d * y * y = c := by
  obtain hleft | hright := hres
  · obtain ⟨yr, hyr⟩ := hleft
    let y0 : ℤ_[2] := (yr.val : ℕ)
    have hy0 : PadicInt.toZModPow 3 y0 = yr := by
      rw [show y0 = (yr.val : ℤ_[2]) by rfl, map_natCast]
      exact ZMod.natCast_zmod_val yr
    let F : Polynomial ℤ_[2] :=
      Polynomial.X ^ 2 - Polynomial.C (d * y0 * y0 + c)
    have hF : PadicInt.toZModPow 3 (F.eval 1) = 0 := by
      have hFeval : F.eval 1 = 1 * 1 - d * y0 * y0 - c := by
        simp [F]
        ring
      rw [hFeval]
      simp only [map_sub, map_mul, map_one, hy0]
      exact sub_eq_zero.mpr (by simpa using hyr)
    have hderiv : ‖F.derivative.eval (1 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
      have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ :=
        @PadicInt.norm_p 2 inferInstance
      have heval : F.derivative.eval (1 : ℤ_[2]) = 2 := by
        norm_num [F]
      rw [heval, hnormTwo]
    obtain ⟨x, hx⟩ :=
      PadicInt.exists_polynomial_root_of_root_mod_eight_derivative_norm_half
        F 1 hF hderiv
    refine ⟨x, y0, ?_⟩
    have hx' : x * x = d * y0 * y0 + c := by
      exact sub_eq_zero.mp (by simpa [F, pow_two] using hx)
    rw [hx']
    ring
  · obtain ⟨xr, hxr⟩ := hright
    let x0 : ℤ_[2] := (xr.val : ℕ)
    have hx0 : PadicInt.toZModPow 3 x0 = xr := by
      rw [show x0 = (xr.val : ℤ_[2]) by rfl, map_natCast]
      exact ZMod.natCast_zmod_val xr
    let F : Polynomial ℤ_[2] :=
      Polynomial.C (x0 * x0) - Polynomial.C d * Polynomial.X ^ 2 -
        Polynomial.C c
    have hF : PadicInt.toZModPow 3 (F.eval 1) = 0 := by
      have hFeval : F.eval 1 = x0 * x0 - d * 1 * 1 - c := by
        simp [F]
      rw [hFeval]
      simp only [map_sub, map_mul, map_one, hx0]
      exact sub_eq_zero.mpr (by simpa using hxr)
    have hderiv : ‖F.derivative.eval (1 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
      have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ :=
        @PadicInt.norm_p 2 inferInstance
      have hnormd : ‖d‖ = 1 := PadicInt.isUnit_iff.mp hd
      have heval : F.derivative.eval (1 : ℤ_[2]) = -(2 * d) := by
        norm_num [F]
        ring
      rw [heval, norm_neg, norm_mul, hnormTwo, hnormd]
      norm_num
    obtain ⟨y, hy⟩ :=
      PadicInt.exists_polynomial_root_of_root_mod_eight_derivative_norm_half
        F 1 hF hderiv
    refine ⟨x0, y, ?_⟩
    apply sub_eq_zero.mp
    calc
      x0 * x0 - d * y * y - c = x0 * x0 - d * (y * y) - c := by ring
      _ = 0 := by simpa [F, pow_two] using hy

/-- Every 2-adic integral unit is a norm from the unramified quadratic class
whose parameter residue is five modulo eight. -/
theorem exists_padicInt_quadraticNorm_eq_of_units_residue_five
    {d c : ℤ_[2]} (hd : IsUnit d) (hc : IsUnit c)
    (hdres : PadicInt.toZModPow 3 d = 5) :
    ∃ x y : ℤ_[2], x * x - d * y * y = c := by
  apply exists_padicInt_quadraticNorm_eq_of_mod_eight_witness hd
  apply PadicInt.exists_quadraticNorm_eq_mod_eight_of_parameter_eq_five hdres
  exact hc.map (PadicInt.toZModPow 3)

/-- For a unit parameter of residue three or seven modulo eight, an integral
unit target is a quadratic norm exactly when its residue is one or five. -/
theorem exists_padicInt_quadraticNorm_eq_iff_of_units_residue_three_or_seven
    {d c : ℤ_[2]} (hd : IsUnit d) (hc : IsUnit c)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7) :
    (∃ x y : ℤ_[2], x * x - d * y * y = c) ↔
      PadicInt.toZModPow 3 c = 1 ∨ PadicInt.toZModPow 3 c = 5 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    apply (PadicInt.quadraticNormRepresents_mod_eight_iff_of_parameter_eq_three_or_seven
      hdres (hc.map (PadicInt.toZModPow 3))).1
    exact ⟨PadicInt.toZModPow 3 x, PadicInt.toZModPow 3 y, by
      simpa using congrArg (PadicInt.toZModPow 3) hxy⟩
  · intro hcres
    apply exists_padicInt_quadraticNorm_eq_of_mod_eight_witness hd
    exact PadicInt.exists_quadraticNorm_eq_mod_eight_of_parameter_eq_three_or_seven
      hdres hcres

/-- With a ramified dyadic unit parameter, nonzero coordinates of equal
valuation give a quadratic norm of valuation `2*v+1`. -/
theorem quadraticNorm_valuation_eq_of_ramified_dyadic_unit_and_equal
    {d : ℤ_[2]} (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7)
    {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hvxy : x.valuation = y.valuation) :
    (x * x - (d : ℚ_[2]) * y * y).valuation = 2 * x.valuation + 1 := by
  let q : ℚ_[2] := x / y
  have hq0 : q ≠ 0 := div_ne_zero hx hy
  have hqval : q.valuation = 0 := by
    rw [show q = x / y by rfl, div_eq_mul_inv,
      Padic.valuation_mul hx (inv_ne_zero hy), Padic.valuation_inv, hvxy]
    omega
  let Q : ℤ_[2] :=
    ⟨q, (Padic.norm_le_one_iff_val_nonneg q).2 (by rw [hqval])⟩
  have hQunit : IsUnit Q := by
    rw [PadicInt.isUnit_iff]
    change ‖q‖ = 1
    rw [Padic.norm_eq_zpow_neg_valuation hq0, hqval]
    simp
  have hbracket := PadicInt.quadraticNorm_unit_bracket_valuation_eq_one
    hQunit isUnit_one hdres
  have hbracketq : (q * q - (d : ℚ_[2])).valuation = 1 := by
    calc
      (q * q - (d : ℚ_[2])).valuation =
          (((Q * Q - d * 1 * 1 : ℤ_[2]) : ℚ_[2])).valuation := by
            congr 1
            simp [Q]
      _ = ((Q * Q - d * 1 * 1).valuation : ℤ) := by
        rw [PadicInt.valuation_coe]
      _ = 1 := by exact_mod_cast hbracket
  have hfactor :
      x * x - (d : ℚ_[2]) * y * y =
        (y * y) * (q * q - (d : ℚ_[2])) := by
    dsimp only [q]
    field_simp
  rw [hfactor, Padic.valuation_mul (mul_ne_zero hy hy)
    (by intro hz; rw [hz] at hbracketq; simp at hbracketq),
    Padic.valuation_mul hy hy, hbracketq, hvxy]
  omega

/-- The accepted normalized odd target residues lift to exact integral
quadratic norm equations. -/
theorem exists_padicInt_quadraticNorm_eq_two_mul_unit_of_ramified_dyadic_residue
    {d U : ℤ_[2]} (hd : IsUnit d)
    (hres :
      (PadicInt.toZModPow 3 d = 3 ∧
        (PadicInt.toZModPow 3 U = 3 ∨ PadicInt.toZModPow 3 U = 7)) ∨
      (PadicInt.toZModPow 3 d = 7 ∧
        (PadicInt.toZModPow 3 U = 1 ∨ PadicInt.toZModPow 3 U = 5))) :
    ∃ x y : ℤ_[2], x * x - d * y * y = 2 * U := by
  apply exists_padicInt_quadraticNorm_eq_of_mod_eight_witness hd
  left
  refine ⟨1, ?_⟩
  simp only [map_mul, map_ofNat]
  rcases hres with ⟨hdres, hUres⟩ | ⟨hdres, hUres⟩ <;>
    rcases hUres with hUres | hUres <;> rw [hdres, hUres] <;> decide

/-- Every representation of a normalized odd target `2*U` by a ramified
dyadic unit parameter has two unit coordinates. -/
theorem quadraticNorm_coordinates_valuation_eq_zero_of_ramified_dyadic_twice_unit
    {d U : ℤ_[2]} (hd : IsUnit d) (hU : IsUnit U)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7)
    {x y : ℚ_[2]}
    (hxy : x * x - (d : ℚ_[2]) * y * y = ((2 * U : ℤ_[2]) : ℚ_[2])) :
    x ≠ 0 ∧ y ≠ 0 ∧ x.valuation = 0 ∧ y.valuation = 0 := by
  have hd0 : d ≠ 0 := IsUnit.ne_zero hd
  have hdq0 : (d : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hd0
  have hdval : (d : ℚ_[2]).valuation = 0 := by
    norm_cast
    exact PadicInt.valuation_eq_zero_of_isUnit hd
  have hU0 : U ≠ 0 := IsUnit.ne_zero hU
  have hUq0 : (U : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hU0
  have hUval : (U : ℚ_[2]).valuation = 0 := by
    norm_cast
    exact PadicInt.valuation_eq_zero_of_isUnit hU
  have htwo0 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have htarget0 : (((2 * U : ℤ_[2]) : ℚ_[2])) ≠ 0 := by
    exact PadicInt.coe_ne_zero.mpr
      (mul_ne_zero (by norm_num : (2 : ℤ_[2]) ≠ 0) hU0)
  have htargetval : (((2 * U : ℤ_[2]) : ℚ_[2])).valuation = 1 := by
    change ((2 : ℚ_[2]) * (U : ℚ_[2])).valuation = 1
    rw [Padic.valuation_mul htwo0 hUq0, hUval,
      show (2 : ℚ_[2]).valuation = 1 from Padic.valuation_p]
    omega
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y ≠ 0 := by
      intro hy
      apply htarget0
      simpa [hy] using hxy.symm
    have hval := congrArg Padic.valuation hxy
    have hdyval : ((d : ℚ_[2]) * y * y).valuation = 2 * y.valuation := by
      rw [Padic.valuation_mul (mul_ne_zero hdq0 hy) hy,
        Padic.valuation_mul hdq0 hy, hdval]
      omega
    simp only [zero_mul, zero_sub] at hval
    rw [Padic.valuation_neg, hdyval, htargetval] at hval
    omega
  · rcases eq_or_ne y 0 with rfl | hy
    · have hval := congrArg Padic.valuation hxy
      simp only [mul_zero, sub_zero] at hval
      rw [Padic.valuation_mul hx hx, htargetval] at hval
      omega
    · have hvalx : (x * x).valuation = 2 * x.valuation := by
        rw [Padic.valuation_mul hx hx]
        omega
      have hvaly : ((d : ℚ_[2]) * y * y).valuation = 2 * y.valuation := by
        rw [Padic.valuation_mul (mul_ne_zero hdq0 hy) hy,
          Padic.valuation_mul hdq0 hy, hdval]
        omega
      by_cases hvxy : x.valuation = y.valuation
      · have hval := quadraticNorm_valuation_eq_of_ramified_dyadic_unit_and_equal
          hdres hx hy hvxy
        rw [hxy, htargetval] at hval
        exact ⟨hx, hy, by omega, by omega⟩
      · have hvals :
            (x * x).valuation ≠ ((d : ℚ_[2]) * y * y).valuation := by
          rw [hvalx, hvaly]
          omega
        have hmin := Padic.valuation_sub_eq_of_ne
          (mul_ne_zero hx hx) (mul_ne_zero (mul_ne_zero hdq0 hy) hy) hvals
        rw [hxy, htargetval, hvalx, hvaly] at hmin
        rcases lt_or_gt_of_ne hvxy with hlt | hgt
        · rw [min_eq_left (by omega)] at hmin
          omega
        · rw [min_eq_right (by omega)] at hmin
          omega

/-- The normalized odd target `2*U` is a ramified dyadic norm exactly in the
two residue classes prescribed by the parameter residue. -/
theorem quadraticNormRepresents_padic_twice_unit_iff_ramified_dyadic_residue
    {d U : ℤ_[2]} (hd : IsUnit d) (hU : IsUnit U)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7) :
    quadraticNormRepresents (d : ℚ_[2]) ((2 * U : ℤ_[2]) : ℚ_[2]) ↔
      (PadicInt.toZModPow 3 d = 3 ∧
        (PadicInt.toZModPow 3 U = 3 ∨ PadicInt.toZModPow 3 U = 7)) ∨
      (PadicInt.toZModPow 3 d = 7 ∧
        (PadicInt.toZModPow 3 U = 1 ∨ PadicInt.toZModPow 3 U = 5)) := by
  constructor
  · rw [quadraticNormRepresents_iff_exists]
    rintro ⟨x, y, hxy⟩
    obtain ⟨hx0, hy0, hxval, hyval⟩ :=
      quadraticNorm_coordinates_valuation_eq_zero_of_ramified_dyadic_twice_unit
        hd hU hdres hxy
    let X : ℤ_[2] :=
      ⟨x, (Padic.norm_le_one_iff_val_nonneg x).2 (by rw [hxval])⟩
    let Y : ℤ_[2] :=
      ⟨y, (Padic.norm_le_one_iff_val_nonneg y).2 (by rw [hyval])⟩
    have hXunit : IsUnit X := by
      rw [PadicInt.isUnit_iff]
      change ‖x‖ = 1
      rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
      simp
    have hYunit : IsUnit Y := by
      rw [PadicInt.isUnit_iff]
      change ‖y‖ = 1
      rw [Padic.norm_eq_zpow_neg_valuation hy0, hyval]
      simp
    have hXY : X * X - d * Y * Y = 2 * U := Subtype.ext hxy
    have hres := congrArg (PadicInt.toZModPow 3) hXY
    have hXsq : PadicInt.toZModPow 3 X * PadicInt.toZModPow 3 X = 1 := by
      simpa [pow_two] using PadicInt.zmod_eight_sq_eq_one_of_isUnit
        (PadicInt.toZModPow 3 X) (hXunit.map (PadicInt.toZModPow 3))
    have hYsq : PadicInt.toZModPow 3 Y * PadicInt.toZModPow 3 Y = 1 := by
      simpa [pow_two] using PadicInt.zmod_eight_sq_eq_one_of_isUnit
        (PadicInt.toZModPow 3 Y) (hYunit.map (PadicInt.toZModPow 3))
    simp only [map_sub, map_mul, map_ofNat] at hres
    rw [hXsq] at hres
    have hres' :
        1 - PadicInt.toZModPow 3 d = 2 * PadicInt.toZModPow 3 U := by
      calc
        1 - PadicInt.toZModPow 3 d =
            1 - PadicInt.toZModPow 3 d * 1 := by ring
        _ = 1 - PadicInt.toZModPow 3 d *
            (PadicInt.toZModPow 3 Y * PadicInt.toZModPow 3 Y) := by
              rw [hYsq]
        _ = 1 - PadicInt.toZModPow 3 d * PadicInt.toZModPow 3 Y *
            PadicInt.toZModPow 3 Y := by ring
        _ = 2 * PadicInt.toZModPow 3 U := hres
    rcases hdres with hdres | hdres
    · left
      refine ⟨hdres, (PadicInt.two_mul_eq_six_iff_of_isUnit
        (hU.map (PadicInt.toZModPow 3))).1 ?_⟩
      rw [← hres', hdres]
      decide
    · right
      refine ⟨hdres, (PadicInt.two_mul_eq_two_iff_of_isUnit
        (hU.map (PadicInt.toZModPow 3))).1 ?_⟩
      rw [← hres', hdres]
      decide
  · intro hres
    rw [quadraticNormRepresents_iff_exists]
    obtain ⟨x, y, hxy⟩ :=
      exists_padicInt_quadraticNorm_eq_two_mul_unit_of_ramified_dyadic_residue
        hd hres
    exact ⟨x, y, congrArg Subtype.val hxy⟩

/-- A 2-adic representation of a unit by a unit parameter of residue three
or seven cannot use nonintegral coordinates. -/
theorem quadraticNorm_coordinates_nonnegative_of_ramified_dyadic_units
    {d c : ℤ_[2]} (hd : IsUnit d) (hc : IsUnit c)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7)
    {x y : ℚ_[2]} (hxy : x * x - (d : ℚ_[2]) * y * y = (c : ℚ_[2])) :
    0 ≤ x.valuation ∧ 0 ≤ y.valuation := by
  have hd0 : d ≠ 0 := IsUnit.ne_zero hd
  have hdq0 : (d : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hd0
  have hdval : (d : ℚ_[2]).valuation = 0 := by
    norm_cast
    exact PadicInt.valuation_eq_zero_of_isUnit hd
  have hcval : (c : ℚ_[2]).valuation = 0 := by
    norm_cast
    exact PadicInt.valuation_eq_zero_of_isUnit hc
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y ≠ 0 := by
      intro hy
      simp [hy] at hxy
      exact IsUnit.ne_zero hc (Subtype.ext hxy.symm)
    have hval := congrArg Padic.valuation hxy
    have hdyval : ((d : ℚ_[2]) * y * y).valuation = 2 * y.valuation := by
      rw [Padic.valuation_mul (mul_ne_zero hdq0 hy) hy,
        Padic.valuation_mul hdq0 hy, hdval]
      omega
    simp only [zero_mul, zero_sub] at hval
    rw [Padic.valuation_neg, hdyval, hcval] at hval
    constructor <;> simp_all
  · rcases eq_or_ne y 0 with rfl | hy
    · have hval := congrArg Padic.valuation hxy
      simp only [mul_zero, sub_zero] at hval
      rw [Padic.valuation_mul hx hx, hcval] at hval
      constructor <;> simp_all
    · have hvalx : (x * x).valuation = 2 * x.valuation := by
        rw [Padic.valuation_mul hx hx]
        omega
      have hvaly : ((d : ℚ_[2]) * y * y).valuation = 2 * y.valuation := by
        rw [Padic.valuation_mul (mul_ne_zero hdq0 hy) hy,
          Padic.valuation_mul hdq0 hy, hdval]
        omega
      by_cases hvxy : x.valuation = y.valuation
      · have hval := quadraticNorm_valuation_eq_of_ramified_dyadic_unit_and_equal
          hdres hx hy hvxy
        rw [hxy, hcval] at hval
        omega
      · have hvals :
            (x * x).valuation ≠ ((d : ℚ_[2]) * y * y).valuation := by
          rw [hvalx, hvaly]
          omega
        have hmin := Padic.valuation_sub_eq_of_ne
          (mul_ne_zero hx hx) (mul_ne_zero (mul_ne_zero hdq0 hy) hy) hvals
        rw [hxy, hcval, hvalx, hvaly] at hmin
        rcases lt_or_gt_of_ne hvxy with hlt | hgt
        · rw [min_eq_left (by omega)] at hmin
          constructor <;> omega
        · rw [min_eq_right (by omega)] at hmin
          constructor <;> omega

/-- For a ramified dyadic unit parameter, the full 2-adic unit-target norm
criterion is the same residue-one-or-five table as for integral coordinates. -/
theorem quadraticNormRepresents_padic_units_iff_residue_one_or_five_of_parameter_residue_three_or_seven
    {d c : ℤ_[2]} (hd : IsUnit d) (hc : IsUnit c)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      PadicInt.toZModPow 3 c = 1 ∨ PadicInt.toZModPow 3 c = 5 := by
  constructor
  · rw [quadraticNormRepresents_iff_exists]
    rintro ⟨x, y, hxy⟩
    obtain ⟨hx, hy⟩ :=
      quadraticNorm_coordinates_nonnegative_of_ramified_dyadic_units
        hd hc hdres hxy
    let X : ℤ_[2] :=
      ⟨x, (Padic.norm_le_one_iff_val_nonneg x).2 hx⟩
    let Y : ℤ_[2] :=
      ⟨y, (Padic.norm_le_one_iff_val_nonneg y).2 hy⟩
    apply (exists_padicInt_quadraticNorm_eq_iff_of_units_residue_three_or_seven
      hd hc hdres).1
    exact ⟨X, Y, Subtype.ext hxy⟩
  · intro hcres
    rw [quadraticNormRepresents_iff_exists]
    obtain ⟨x, y, hxy⟩ :=
      (exists_padicInt_quadraticNorm_eq_iff_of_units_residue_three_or_seven
        hd hc hdres).2 hcres
    exact ⟨x, y, congrArg Subtype.val hxy⟩

/-- A nonzero 2-adic target of even valuation has a canonical integral unit in
its square class, and replacing the target by that unit preserves every
quadratic norm fiber. -/
theorem exists_padicInt_unit_target_square_normalization_of_even_valuation
    {c : ℚ_[2]} (hc : c ≠ 0) (heven : Even c.valuation) :
    ∃ C : ℤ_[2], IsUnit C ∧
      (C : ℚ_[2]) = c * (2 : ℚ_[2]) ^ (-c.valuation) ∧
      ∀ d : ℚ_[2],
        quadraticNormRepresents d c ↔
          quadraticNormRepresents d (C : ℚ_[2]) := by
  let u : ℚ_[2] := c * (2 : ℚ_[2]) ^ (-c.valuation)
  have hu : ‖u‖ = 1 := by
    simp [u, hc, Padic.norm_eq_zpow_neg_valuation]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  let Cu : ℤ_[2]ˣ := PadicInt.mkUnits hu
  let C : ℤ_[2] := Cu
  have hCunit : IsUnit C := by
    exact Units.isUnit Cu
  have hCcast : (C : ℚ_[2]) = u := by
    exact PadicInt.mkUnits_eq hu
  refine ⟨C, hCunit, by simpa [u] using hCcast, ?_⟩
  intro d
  obtain ⟨k, hk⟩ := heven
  have hval : c.valuation = 2 * k := by omega
  let s : ℚ_[2] := (2 : ℚ_[2]) ^ (-k)
  have hs0 : s ≠ 0 := zpow_ne_zero _ (by norm_num)
  have htarget : c * s ^ 2 = u := by
    simp only [s, u]
    rw [hval, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring_nf
  have htransport := quadraticNormRepresents_iff_mul_sq_target
    (K := ℚ_[2]) (d := d) (c := c) (s := s) hs0
  rw [htarget, ← hCcast] at htransport
  exact htransport

/-- For a unit ramified dyadic parameter, an even-valuation target is a norm
exactly when its normalized integral unit has residue one or five. -/
theorem exists_padicInt_unit_norm_criterion_of_ramified_dyadic_parameter_even_target
    {d : ℤ_[2]} (hd : IsUnit d)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7)
    {c : ℚ_[2]} (hc : c ≠ 0) (heven : Even c.valuation) :
    ∃ C : ℤ_[2], IsUnit C ∧
      (C : ℚ_[2]) = c * (2 : ℚ_[2]) ^ (-c.valuation) ∧
      (quadraticNormRepresents (d : ℚ_[2]) c ↔
        PadicInt.toZModPow 3 C = 1 ∨ PadicInt.toZModPow 3 C = 5) := by
  obtain ⟨C, hCunit, hCcast, hCnorm⟩ :=
    exists_padicInt_unit_target_square_normalization_of_even_valuation hc heven
  refine ⟨C, hCunit, hCcast, ?_⟩
  rw [hCnorm]
  exact quadraticNormRepresents_padic_units_iff_residue_one_or_five_of_parameter_residue_three_or_seven
    hd hCunit hdres

/-- A nonzero 2-adic target of odd valuation is square-equivalent to twice its
canonical normalized integral unit, with every quadratic norm fiber
preserved. -/
theorem exists_padicInt_unit_target_square_normalization_of_odd_valuation
    {c : ℚ_[2]} (hc : c ≠ 0) (hodd : Odd c.valuation) :
    ∃ U : ℤ_[2], IsUnit U ∧
      (U : ℚ_[2]) = c * (2 : ℚ_[2]) ^ (-c.valuation) ∧
      ∀ d : ℚ_[2],
        quadraticNormRepresents d c ↔
          quadraticNormRepresents d (((2 * U : ℤ_[2]) : ℚ_[2])) := by
  let u : ℚ_[2] := c * (2 : ℚ_[2]) ^ (-c.valuation)
  have hu : ‖u‖ = 1 := by
    simp [u, hc, Padic.norm_eq_zpow_neg_valuation]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  let Uu : ℤ_[2]ˣ := PadicInt.mkUnits hu
  let U : ℤ_[2] := Uu
  have hUunit : IsUnit U := by
    exact Units.isUnit Uu
  have hUcast : (U : ℚ_[2]) = u := by
    exact PadicInt.mkUnits_eq hu
  refine ⟨U, hUunit, by simpa [u] using hUcast, ?_⟩
  intro d
  obtain ⟨k, hk⟩ := hodd
  have hval : c.valuation = 2 * k + 1 := by omega
  let s : ℚ_[2] := (2 : ℚ_[2]) ^ (-k)
  have hs0 : s ≠ 0 := zpow_ne_zero _ (by norm_num)
  have htarget : c * s ^ 2 = (((2 * U : ℤ_[2]) : ℚ_[2])) := by
    change c * s ^ 2 = (2 : ℚ_[2]) * (U : ℚ_[2])
    rw [hUcast]
    simp only [s, u]
    rw [hval, ← zpow_natCast, ← zpow_mul]
    calc
      c * (2 : ℚ_[2]) ^ (-k * (2 : ℤ)) =
          c * ((2 : ℚ_[2]) ^ (1 : ℤ) *
            (2 : ℚ_[2]) ^ (-(2 * k + 1))) := by
              congr 1
              rw [← zpow_add₀ (by norm_num : (2 : ℚ_[2]) ≠ 0)]
              congr 1
              ring
      _ = (2 : ℚ_[2]) *
          (c * (2 : ℚ_[2]) ^ (-(2 * k + 1))) := by
            rw [zpow_one]
            ring
  have htransport := quadraticNormRepresents_iff_mul_sq_target
    (K := ℚ_[2]) (d := d) (c := c) (s := s) hs0
  rw [htarget] at htransport
  exact htransport

/-- For a ramified dyadic unit parameter, an odd-valuation target is a norm
exactly in the residue classes prescribed for its normalized unit. -/
theorem exists_padicInt_unit_norm_criterion_of_ramified_dyadic_parameter_odd_target
    {d : ℤ_[2]} (hd : IsUnit d)
    (hdres : PadicInt.toZModPow 3 d = 3 ∨
      PadicInt.toZModPow 3 d = 7)
    {c : ℚ_[2]} (hc : c ≠ 0) (hodd : Odd c.valuation) :
    ∃ U : ℤ_[2], IsUnit U ∧
      (U : ℚ_[2]) = c * (2 : ℚ_[2]) ^ (-c.valuation) ∧
      (quadraticNormRepresents (d : ℚ_[2]) c ↔
        (PadicInt.toZModPow 3 d = 3 ∧
          (PadicInt.toZModPow 3 U = 3 ∨ PadicInt.toZModPow 3 U = 7)) ∨
        (PadicInt.toZModPow 3 d = 7 ∧
          (PadicInt.toZModPow 3 U = 1 ∨ PadicInt.toZModPow 3 U = 5))) := by
  obtain ⟨U, hUunit, hUcast, hUnorm⟩ :=
    exists_padicInt_unit_target_square_normalization_of_odd_valuation hc hodd
  refine ⟨U, hUunit, hUcast, ?_⟩
  rw [hUnorm]
  exact quadraticNormRepresents_padic_twice_unit_iff_ramified_dyadic_residue
    hd hUunit hdres

/-- The preceding integral solution represents every 2-adic unit by the norm
from the unramified quadratic algebra. -/
theorem quadraticNormRepresents_padic_units_of_residue_five
    {d c : ℤ_[2]} (hd : IsUnit d) (hc : IsUnit c)
    (hdres : PadicInt.toZModPow 3 d = 5) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) := by
  rw [quadraticNormRepresents_iff_exists]
  obtain ⟨x, y, hxy⟩ :=
    exists_padicInt_quadraticNorm_eq_of_units_residue_five hd hc hdres
  exact ⟨x, y, congrArg Subtype.val hxy⟩

/-- For a unit parameter of residue five modulo eight, every nonzero integral
quadratic norm has even valuation. -/
theorem quadraticNorm_padicInt_valuation_even_of_unit_residue_five
    {d x y : ℤ_[2]} (hd : IsUnit d)
    (hdres : PadicInt.toZModPow 3 d = 5)
    (hnorm : x * x - d * y * y ≠ 0) :
    Even (x * x - d * y * y).valuation := by
  have hd0 : d ≠ 0 := IsUnit.ne_zero hd
  have hdval : d.valuation = 0 := PadicInt.valuation_eq_zero_of_isUnit hd
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y ≠ 0 := by
      intro hy
      apply hnorm
      simp [hy]
    simp only [zero_mul, zero_sub]
    rw [PadicInt.valuation_neg,
      PadicInt.valuation_mul (mul_ne_zero hd0 hy) hy,
      PadicInt.valuation_mul hd0 hy, hdval]
    exact ⟨y.valuation, by omega⟩
  · rcases eq_or_ne y 0 with rfl | hy
    · simp only [mul_zero, sub_zero]
      rw [PadicInt.valuation_mul hx hx]
      exact ⟨x.valuation, by omega⟩
    · by_cases hvxy : x.valuation = y.valuation
      · let ux : ℤ_[2]ˣ := PadicInt.unitCoeff hx
        let uy : ℤ_[2]ˣ := PadicInt.unitCoeff hy
        let b : ℤ_[2] := (ux : ℤ_[2]) * ux - d * (uy : ℤ_[2]) * uy
        have hbval : b.valuation = 2 :=
          PadicInt.quadraticNorm_unit_bracket_valuation_eq_two
            (Units.isUnit ux) (Units.isUnit uy) hdres
        have hb0 : b ≠ 0 := by
          intro hb
          simp [hb] at hbval
        let t : ℤ_[2] := (2 : ℤ_[2]) ^ x.valuation
        have hxspec := PadicInt.unitCoeff_spec hx
        have hyspec := PadicInt.unitCoeff_spec hy
        have hyspec' :
            y = (uy : ℤ_[2]) * (2 : ℤ_[2]) ^ x.valuation := by
          simpa [uy, hvxy] using hyspec
        have hfactor : x * x - d * y * y = b * (t * t) := by
          rw [hxspec, hyspec']
          simp only [ux, uy, t, b]
          ring
        have htwo0 : (2 : ℤ_[2]) ≠ 0 := by norm_num
        rw [hfactor, PadicInt.valuation_mul hb0
          (mul_ne_zero (pow_ne_zero _ htwo0) (pow_ne_zero _ htwo0)),
          hbval, PadicInt.valuation_mul
            (pow_ne_zero _ htwo0) (pow_ne_zero _ htwo0),
          PadicInt.valuation_pow]
        rw [show (2 : ℤ_[2]).valuation = 1 from PadicInt.valuation_p]
        exact ⟨x.valuation + 1, by omega⟩
      · have hxx : x * x ≠ 0 := mul_ne_zero hx hx
        have hdyy : d * y * y ≠ 0 := mul_ne_zero (mul_ne_zero hd0 hy) hy
        have hvalx : (x * x).valuation = 2 * x.valuation := by
          rw [PadicInt.valuation_mul hx hx]
          omega
        have hvaly : (d * y * y).valuation = 2 * y.valuation := by
          rw [PadicInt.valuation_mul (mul_ne_zero hd0 hy) hy,
            PadicInt.valuation_mul hd0 hy, hdval]
          omega
        have hvals : (x * x).valuation ≠ (d * y * y).valuation := by
          rw [hvalx, hvaly]
          omega
        rw [PadicInt.valuation_sub_eq_of_ne hxx hdyy hvals, hvalx, hvaly]
        rcases lt_or_gt_of_ne hvxy with hlt | hgt
        · rw [min_eq_left (by omega)]
          exact ⟨x.valuation, by omega⟩
        · rw [min_eq_right (by omega)]
          exact ⟨y.valuation, by omega⟩

/-- For a unit parameter of residue five modulo eight, every nonzero
quadratic norm over `ℚ_[2]` has even valuation. -/
theorem quadraticNorm_padic_valuation_even_of_unit_residue_five
    {d : ℤ_[2]} {x y : ℚ_[2]} (hd : IsUnit d)
    (hdres : PadicInt.toZModPow 3 d = 5)
    (hnorm : x * x - (d : ℚ_[2]) * y * y ≠ 0) :
    Even (x * x - (d : ℚ_[2]) * y * y).valuation := by
  let q : ℚ_[2] := x * x - (d : ℚ_[2]) * y * y
  let m : ℕ := (max (-x.valuation) (-y.valuation)).toNat
  let s : ℚ_[2] := (2 : ℚ_[2]) ^ m
  have htwo0 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hs0 : s ≠ 0 := pow_ne_zero _ htwo0
  have hmx : -x.valuation ≤ (m : ℤ) :=
    le_trans (le_max_left _ _) (Int.self_le_toNat _)
  have hmy : -y.valuation ≤ (m : ℤ) :=
    le_trans (le_max_right _ _) (Int.self_le_toNat _)
  have hsval : s.valuation = (m : ℤ) := by
    simp [s, Padic.valuation_pow]
  have hsxval : 0 ≤ (s * x).valuation := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [Padic.valuation_mul hs0 hx, hsval]
      omega
  have hsyval : 0 ≤ (s * y).valuation := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [Padic.valuation_mul hs0 hy, hsval]
      omega
  let X : ℤ_[2] := ⟨s * x, (Padic.norm_le_one_iff_val_nonneg _).2 hsxval⟩
  let Y : ℤ_[2] := ⟨s * y, (Padic.norm_le_one_iff_val_nonneg _).2 hsyval⟩
  have hfactor :
      ((X * X - d * Y * Y : ℤ_[2]) : ℚ_[2]) = s ^ 2 * q := by
    change (s * x) * (s * x) - (d : ℚ_[2]) * (s * y) * (s * y) =
      s ^ 2 * (x * x - (d : ℚ_[2]) * y * y)
    ring
  have hq0 : q ≠ 0 := hnorm
  have hscaled0 : X * X - d * Y * Y ≠ 0 := by
    intro hz
    have hz' := congrArg Subtype.val hz
    rw [hfactor] at hz'
    exact (mul_ne_zero (pow_ne_zero _ hs0) hq0) hz'
  have heven := quadraticNorm_padicInt_valuation_even_of_unit_residue_five
    hd hdres hscaled0
  have hvaleq :
      ((X * X - d * Y * Y).valuation : ℤ) =
        2 * (m : ℤ) + q.valuation := by
    rw [← PadicInt.valuation_coe, hfactor,
      Padic.valuation_mul (pow_ne_zero _ hs0) hq0,
      Padic.valuation_pow, hsval]
    omega
  obtain ⟨k, hk⟩ := heven
  have hkz := congrArg (fun n : ℕ => (n : ℤ)) hk
  refine ⟨(k : ℤ) - m, ?_⟩
  change q.valuation = ((k : ℤ) - m) + ((k : ℤ) - m)
  omega

/-- The norm group of the dyadic unramified quadratic algebra consists
exactly of the nonzero 2-adic elements with even valuation. -/
theorem quadraticNormRepresents_padic_dyadic_unramified_iff_valuation_even
    {d : ℤ_[2]} (hd : IsUnit d)
    (hdres : PadicInt.toZModPow 3 d = 5)
    {c : ℚ_[2]} (hc : c ≠ 0) :
    quadraticNormRepresents (d : ℚ_[2]) c ↔ Even c.valuation := by
  constructor
  · rw [quadraticNormRepresents_iff_exists]
    rintro ⟨x, y, hxy⟩
    subst c
    exact quadraticNorm_padic_valuation_even_of_unit_residue_five
      hd hdres hc
  · intro heven
    let u : ℚ_[2] := c * (2 : ℚ_[2]) ^ (-c.valuation)
    have htwo0 : (2 : ℚ_[2]) ≠ 0 := by norm_num
    have hu : ‖u‖ = 1 := by
      simp [u, hc, Padic.norm_eq_zpow_neg_valuation]
      exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
    let cu : ℤ_[2]ˣ := PadicInt.mkUnits hu
    have hcu : IsUnit (cu : ℤ_[2]) := Units.isUnit cu
    have hrep := quadraticNormRepresents_padic_units_of_residue_five
      hd hcu hdres
    rw [quadraticNormRepresents_iff_exists] at hrep ⊢
    obtain ⟨x, y, hxy⟩ := hrep
    obtain ⟨k, hk⟩ := heven
    let t : ℚ_[2] := (2 : ℚ_[2]) ^ k
    refine ⟨t * x, t * y, ?_⟩
    have hcuval : ((cu : ℤ_[2]) : ℚ_[2]) = u := PadicInt.mkUnits_eq hu
    have hval : c.valuation = 2 * k := by omega
    calc
      t * x * (t * x) - (d : ℚ_[2]) * (t * y) * (t * y) =
          t ^ 2 * (x * x - (d : ℚ_[2]) * y * y) := by ring
      _ = t ^ 2 * ((cu : ℤ_[2]) : ℚ_[2]) := by rw [hxy]
      _ = ((2 : ℚ_[2]) ^ k) ^ 2 *
          (c * (2 : ℚ_[2]) ^ (-c.valuation)) := by rw [hcuval]
      _ = c := by
        rw [hval, ← zpow_natCast, ← zpow_mul]
        calc
          (2 : ℚ_[2]) ^ (k * (2 : ℤ)) *
              (c * (2 : ℚ_[2]) ^ (-(2 * k))) =
              c * ((2 : ℚ_[2]) ^ (k * 2) *
                (2 : ℚ_[2]) ^ (-(2 * k))) := by ring
          _ = c * (2 : ℚ_[2]) ^ (k * 2 + -(2 * k)) := by
            rw [← zpow_add₀ htwo0]
          _ = c := by ring_nf; simp

/-- For a rational ramified dyadic unit parameter and an even-valuation
rational target, norm representation is equivalent to target unit residue one
or five. -/
theorem quadraticNormRepresents_rat_padic_dyadic_ramified_even_iff_unitRepresentative
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hcpar : Rat.valuationParity 2 c = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      (Rat.dyadicUnitRepresentative c : ZMod 8) = 1 ∨
        (Rat.dyadicUnitRepresentative c : ZMod 8) = 5 := by
  obtain ⟨_, _, D, hDunit, hDres, _, hDnorm⟩ :=
    exists_padicInt_dyadic_ramified_parameter_square_normalization
      hd hdpar hdrep
  obtain ⟨_, _, C, hCunit, hCres, _, hCnorm⟩ :=
    exists_padicInt_dyadic_unit_target_square_normalization
      hc hcpar (r := (Rat.dyadicUnitRepresentative c : ZMod 8)) rfl
  calc
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        quadraticNormRepresents (D : ℚ_[2]) (c : ℚ_[2]) := hDnorm _
    _ ↔ quadraticNormRepresents (D : ℚ_[2]) (C : ℚ_[2]) := hCnorm _
    _ ↔ PadicInt.toZModPow 3 C = 1 ∨ PadicInt.toZModPow 3 C = 5 :=
      quadraticNormRepresents_padic_units_iff_residue_one_or_five_of_parameter_residue_three_or_seven
        hDunit hCunit hDres
    _ ↔ (Rat.dyadicUnitRepresentative c : ZMod 8) = 1 ∨
        (Rat.dyadicUnitRepresentative c : ZMod 8) = 5 := by rw [hCres]

/-- For a rational ramified dyadic unit parameter and an odd-valuation
rational target, norm representation is equivalent to the explicit pair of
parameter and target unit residues. -/
theorem quadraticNormRepresents_rat_padic_dyadic_ramified_odd_iff_unitRepresentatives
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hcpar : Rat.valuationParity 2 c = 1)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      ((Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∧
        ((Rat.dyadicUnitRepresentative c : ZMod 8) = 3 ∨
          (Rat.dyadicUnitRepresentative c : ZMod 8) = 7)) ∨
      ((Rat.dyadicUnitRepresentative d : ZMod 8) = 7 ∧
        ((Rat.dyadicUnitRepresentative c : ZMod 8) = 1 ∨
          (Rat.dyadicUnitRepresentative c : ZMod 8) = 5)) := by
  obtain ⟨_, _, D, hDunit, hDres, _, hDnorm⟩ :=
    exists_padicInt_dyadic_unit_parameter_square_normalization
      hd hdpar (r := (Rat.dyadicUnitRepresentative d : ZMod 8)) rfl
  have hDram : PadicInt.toZModPow 3 D = 3 ∨
      PadicInt.toZModPow 3 D = 7 := by
    rw [hDres]
    exact hdrep
  obtain ⟨_, _, U, hUunit, hUres, _, hUnorm⟩ :=
    exists_padicInt_dyadic_twice_unit_target_square_normalization hc hcpar
  calc
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        quadraticNormRepresents (D : ℚ_[2]) (c : ℚ_[2]) := hDnorm _
    _ ↔ quadraticNormRepresents (D : ℚ_[2])
        (((2 * U : ℤ_[2]) : ℚ_[2])) := hUnorm _
    _ ↔ (PadicInt.toZModPow 3 D = 3 ∧
          (PadicInt.toZModPow 3 U = 3 ∨ PadicInt.toZModPow 3 U = 7)) ∨
        (PadicInt.toZModPow 3 D = 7 ∧
          (PadicInt.toZModPow 3 U = 1 ∨ PadicInt.toZModPow 3 U = 5)) :=
      quadraticNormRepresents_padic_twice_unit_iff_ramified_dyadic_residue
        hDunit hUunit hDram
    _ ↔ ((Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∧
          ((Rat.dyadicUnitRepresentative c : ZMod 8) = 3 ∨
            (Rat.dyadicUnitRepresentative c : ZMod 8) = 7)) ∨
        ((Rat.dyadicUnitRepresentative d : ZMod 8) = 7 ∧
          ((Rat.dyadicUnitRepresentative c : ZMod 8) = 1 ∨
            (Rat.dyadicUnitRepresentative c : ZMod 8) = 5)) := by
      rw [hDres, hUres]

/-- For a rational ramified dyadic unit parameter and an even-valuation
rational target, the quadratic norm criterion agrees with the explicit
dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_ramified_even_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hcpar : Rat.valuationParity 2 c = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  have hepsd : Rat.dyadicUnitEpsilon d = 1 := by
    rcases hdrep with hdrep | hdrep
    · exact Rat.dyadicUnitEpsilon_eq_one_of_cast_eq_three hdrep
    · exact Rat.dyadicUnitEpsilon_eq_one_of_cast_eq_seven hdrep
  have hsymbol : Rat.dyadicHilbertSymbol d c =
      (-1 : ℤ) ^ Rat.dyadicUnitEpsilon c := by
    simp [Rat.dyadicHilbertSymbol, hdpar, hcpar, hepsd]
  rw [quadraticNormRepresents_rat_padic_dyadic_ramified_even_iff_unitRepresentative
      hd hc hdpar hcpar hdrep,
    ← Rat.dyadicUnitEpsilon_eq_zero_iff_cast_eq_one_or_five hc]
  constructor
  · intro heps
    rw [hsymbol, heps]
    norm_num
  · intro hs
    rcases Rat.dyadicUnitEpsilon_eq_zero_or_one c with heps | heps
    · exact heps
    · rw [hsymbol, heps] at hs
      norm_num at hs

/-- For a rational ramified dyadic unit parameter and an odd-valuation
rational target, the quadratic norm criterion agrees with the explicit
dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_ramified_odd_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hcpar : Rat.valuationParity 2 c = 1)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  rcases hdrep with hdthree | hdseven
  · have hnorm : quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        (Rat.dyadicUnitRepresentative c : ZMod 8) = 3 ∨
          (Rat.dyadicUnitRepresentative c : ZMod 8) = 7 := by
      have h37 : (3 : ZMod 8) ≠ 7 := by decide
      rw [quadraticNormRepresents_rat_padic_dyadic_ramified_odd_iff_unitRepresentatives
        hd hc hdpar hcpar (Or.inl hdthree)]
      simp [hdthree, h37]
    have hepsd : Rat.dyadicUnitEpsilon d = 1 :=
      Rat.dyadicUnitEpsilon_eq_one_of_cast_eq_three hdthree
    have homegad : Rat.dyadicUnitOmega d = 1 :=
      Rat.dyadicUnitOmega_eq_one_of_cast_eq_three hdthree
    have hsymbol : Rat.dyadicHilbertSymbol d c =
        (-1 : ℤ) ^ (Rat.dyadicUnitEpsilon c + 1) := by
      simp [Rat.dyadicHilbertSymbol, hdpar, hcpar, hepsd, homegad]
    rw [hnorm, ← Rat.dyadicUnitEpsilon_eq_one_iff_cast_eq_three_or_seven hc]
    constructor
    · intro heps
      rw [hsymbol, heps]
      norm_num
    · intro hs
      rcases Rat.dyadicUnitEpsilon_eq_zero_or_one c with heps | heps
      · rw [hsymbol, heps] at hs
        norm_num at hs
      · exact heps
  · have hnorm : quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        (Rat.dyadicUnitRepresentative c : ZMod 8) = 1 ∨
          (Rat.dyadicUnitRepresentative c : ZMod 8) = 5 := by
      have h73 : (7 : ZMod 8) ≠ 3 := by decide
      rw [quadraticNormRepresents_rat_padic_dyadic_ramified_odd_iff_unitRepresentatives
        hd hc hdpar hcpar (Or.inr hdseven)]
      simp [hdseven, h73]
    have hepsd : Rat.dyadicUnitEpsilon d = 1 :=
      Rat.dyadicUnitEpsilon_eq_one_of_cast_eq_seven hdseven
    have homegad : Rat.dyadicUnitOmega d = 0 :=
      Rat.dyadicUnitOmega_eq_zero_of_cast_eq_seven hdseven
    have hsymbol : Rat.dyadicHilbertSymbol d c =
        (-1 : ℤ) ^ Rat.dyadicUnitEpsilon c := by
      simp [Rat.dyadicHilbertSymbol, hdpar, hcpar, hepsd, homegad]
    rw [hnorm, ← Rat.dyadicUnitEpsilon_eq_zero_iff_cast_eq_one_or_five hc]
    constructor
    · intro heps
      rw [hsymbol, heps]
      norm_num
    · intro hs
      rcases Rat.dyadicUnitEpsilon_eq_zero_or_one c with heps | heps
      · exact heps
      · rw [hsymbol, heps] at hs
        norm_num at hs

/-- For every rational ramified dyadic unit parameter, the quadratic norm
criterion agrees with the explicit dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_ramified_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
      (Rat.dyadicUnitRepresentative d : ZMod 8) = 7) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  rcases Rat.valuationParity_eq_zero_or_one 2 c with hcpar | hcpar
  · exact quadraticNormRepresents_rat_padic_dyadic_ramified_even_iff_hilbertSymbol
      hd hc hdpar hcpar hdrep
  · exact quadraticNormRepresents_rat_padic_dyadic_ramified_odd_iff_hilbertSymbol
      hd hc hdpar hcpar hdrep

/-- For a rational dyadic-unramified parameter, the quadratic norm criterion
agrees with the explicit dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_unramified_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0)
    (hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 5) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  obtain ⟨x, hx, D, hDunit, hDres, hDcast, hDnorm⟩ :=
    exists_padicInt_dyadic_unramified_parameter_square_normalization
      hd hdpar hdrep
  have hnorm :
      quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        Even (padicValRat 2 c) := by
    have hcp : (c : ℚ_[2]) ≠ 0 := by exact_mod_cast hc
    rw [hDnorm]
    simpa [Padic.valuation_ratCast] using
      (quadraticNormRepresents_padic_dyadic_unramified_iff_valuation_even
        hDunit hDres hcp)
  have heps : Rat.dyadicUnitEpsilon d = 0 :=
    Rat.dyadicUnitEpsilon_eq_zero_of_cast_eq_five hdrep
  have homega : Rat.dyadicUnitOmega d = 1 :=
    Rat.dyadicUnitOmega_eq_one_of_cast_eq_five hdrep
  have hsymbol :
      Rat.dyadicHilbertSymbol d c =
        (-1 : ℤ) ^ Rat.valuationParity 2 c := by
    simp [Rat.dyadicHilbertSymbol, hdpar, heps, homega]
  rw [hnorm]
  constructor
  · intro heven
    have hpar : Rat.valuationParity 2 c = 0 := by
      have hem := Int.even_iff.mp heven
      simp [Rat.valuationParity, hem]
    rw [hsymbol, hpar]
    norm_num
  · intro hs
    rcases Rat.valuationParity_eq_zero_or_one 2 c with hpar | hpar
    · exact Int.even_iff.mpr (by simpa [Rat.valuationParity] using hpar)
    · rw [hsymbol, hpar] at hs
      norm_num at hs

/-- For every nonzero rational parameter of even dyadic valuation parity and
every nonzero rational target, the quadratic norm criterion over `ℚ_[2]`
agrees with the explicit dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_even_parameter_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 0) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  rcases Rat.dyadicUnitEpsilon_eq_zero_or_one d with heps | heps
  · rcases (Rat.dyadicUnitEpsilon_eq_zero_iff_cast_eq_one_or_five hd).1 heps with
      hdrep | hdrep
    · have hdsquare : IsSquare (d : ℚ_[2]) :=
        (Rat.isSquare_padic_iff_valuationParity_and_dyadicUnitRepresentative
          hd).2 ⟨hdpar, hdrep⟩
      have hdp0 : (d : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
      have hnorm : quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) :=
        quadraticNormRepresents_of_isSquare (d : ℚ_[2]) (c : ℚ_[2])
          (by rw [ringChar.eq_zero]; norm_num) hdp0 hdsquare
      have homega : Rat.dyadicUnitOmega d = 0 :=
        Rat.dyadicUnitOmega_eq_zero_of_cast_eq_one hdrep
      have hsymbol : Rat.dyadicHilbertSymbol d c = 1 := by
        simp [Rat.dyadicHilbertSymbol, hdpar, heps, homega]
      exact iff_of_true hnorm hsymbol
    · exact quadraticNormRepresents_rat_padic_dyadic_unramified_iff_hilbertSymbol
        hd hc hdpar hdrep
  · have hdrep : (Rat.dyadicUnitRepresentative d : ZMod 8) = 3 ∨
        (Rat.dyadicUnitRepresentative d : ZMod 8) = 7 :=
      (Rat.dyadicUnitEpsilon_eq_one_iff_cast_eq_three_or_seven hd).1 heps
    exact quadraticNormRepresents_rat_padic_dyadic_ramified_iff_hilbertSymbol
      hd hc hdpar hdrep

/-- For a rational dyadic parameter and target both of odd valuation parity,
the quadratic norm criterion agrees with the explicit dyadic Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_odd_parameter_odd_target_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 1)
    (hcpar : Rat.valuationParity 2 c = 1) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  have hdc : -d * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hd) hc
  have hdpadic : (d : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hdcpadic : ((-d * c : ℚ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hdc
  have hdcpar : Rat.valuationParity 2 (-d * c) = 0 :=
    Rat.valuationParity_neg_mul_eq_zero hd hc hdpar hcpar
  calc
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        quadraticNormRepresents (d : ℚ_[2]) ((-d * c : ℚ) : ℚ_[2]) := by
      simpa using
        (quadraticNormRepresents_iff_mul_neg_parameter hdpadic)
    _ ↔ quadraticNormRepresents ((-d * c : ℚ) : ℚ_[2]) (d : ℚ_[2]) :=
      quadraticNormRepresents_symm
        (by rw [ringChar.eq_zero]; norm_num) hdpadic hdcpadic
    _ ↔ Rat.dyadicHilbertSymbol (-d * c) d = 1 :=
      quadraticNormRepresents_rat_padic_dyadic_even_parameter_iff_hilbertSymbol
        hdc hd hdcpar
    _ ↔ Rat.dyadicHilbertSymbol d (-d * c) = 1 := by
      rw [Rat.dyadicHilbertSymbol_symm]
    _ ↔ Rat.dyadicHilbertSymbol d c = 1 := by
      rw [Rat.dyadicHilbertSymbol_mul_neg_self_right_of_parity_eq_one
        hd hc hdpar hcpar]

/-- For a rational dyadic target of even valuation parity, norm symmetry
reduces the criterion to the completed even-parameter case. -/
theorem quadraticNormRepresents_rat_padic_dyadic_even_target_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hcpar : Rat.valuationParity 2 c = 0) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  have hdpadic : (d : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hcpadic : (c : ℚ_[2]) ≠ 0 := by exact_mod_cast hc
  calc
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
        quadraticNormRepresents (c : ℚ_[2]) (d : ℚ_[2]) :=
      quadraticNormRepresents_symm
        (by rw [ringChar.eq_zero]; norm_num) hdpadic hcpadic
    _ ↔ Rat.dyadicHilbertSymbol c d = 1 :=
      quadraticNormRepresents_rat_padic_dyadic_even_parameter_iff_hilbertSymbol
        hc hd hcpar
    _ ↔ Rat.dyadicHilbertSymbol d c = 1 := by
      rw [Rat.dyadicHilbertSymbol_symm]

/-- For every nonzero rational dyadic parameter of odd valuation parity, the
quadratic norm criterion agrees with the explicit Hilbert symbol. -/
theorem quadraticNormRepresents_rat_padic_dyadic_odd_parameter_iff_hilbertSymbol
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0)
    (hdpar : Rat.valuationParity 2 d = 1) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  rcases Rat.valuationParity_eq_zero_or_one 2 c with hcpar | hcpar
  · exact
      quadraticNormRepresents_rat_padic_dyadic_even_target_iff_hilbertSymbol
        hd hc hcpar
  · exact
      quadraticNormRepresents_rat_padic_dyadic_odd_parameter_odd_target_iff_hilbertSymbol
        hd hc hdpar hcpar

/-- The complete rational dyadic quadratic norm criterion: representation over
`ℚ_[2]` is equivalent to the explicit dyadic Hilbert symbol being one. -/
theorem quadraticNormRepresents_rat_padic_iff_dyadicHilbertSymbol_eq_one
    {d c : ℚ} (hd : d ≠ 0) (hc : c ≠ 0) :
    quadraticNormRepresents (d : ℚ_[2]) (c : ℚ_[2]) ↔
      Rat.dyadicHilbertSymbol d c = 1 := by
  rcases Rat.valuationParity_eq_zero_or_one 2 d with hdpar | hdpar
  · exact
      quadraticNormRepresents_rat_padic_dyadic_even_parameter_iff_hilbertSymbol
        hd hc hdpar
  · exact
      quadraticNormRepresents_rat_padic_dyadic_odd_parameter_iff_hilbertSymbol
        hd hc hdpar

end PositiveDefiniteIntegralLattice
