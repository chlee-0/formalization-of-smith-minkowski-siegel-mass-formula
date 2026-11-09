import SMSFormula.RationalDyadicNorm
import SMSFormula.RationalPadicHighRankIsotropy

/-!
# High-rank isotropy over the dyadic field

This file develops the remaining local input for rational intrinsic `GSpin`
similitudes.  The finite core is a modulo-eight zero for five diagonal
coefficients of valuation zero or one, with at least three unit coefficients.
The chosen zero has a unit coordinate at a unit coefficient, so the existing
dyadic Hensel theorem lifts it to an exact nontrivial 2-adic zero.
-/

noncomputable section

open Matrix

namespace PadicInt

/-- The modulo-eight Hensel lift stays a unit when its approximate root is a
unit.  This strengthens the existing root theorem only by retaining the
distance estimate already supplied by `hensels_lemma`. -/
theorem exists_unit_polynomial_root_of_unit_root_mod_eight
    (F : Polynomial ℤ_[2]) (a : ℤ_[2]) (ha : IsUnit a)
    (hFa : toZModPow 3 (F.eval a) = 0)
    (hderiv : ‖F.derivative.eval a‖ = (2 : ℝ)⁻¹) :
    ∃ z : ℤ_[2], IsUnit z ∧ F.eval z = 0 := by
  have hmem :
      F.eval a ∈ (Ideal.span {((2 : ℤ_[2]) ^ 3)} : Ideal ℤ_[2]) := by
    have hker : F.eval a ∈ RingHom.ker (toZModPow 3 : ℤ_[2] →+* ZMod 8) := by
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
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hderiv']
    exact lt_of_le_of_lt hle' (by norm_num)
  obtain ⟨z, hz, hza, _⟩ := hensels_lemma hnorm
  have haNorm : ‖a‖ = 1 := isUnit_iff.mp ha
  have hzaOne : ‖z - a‖ < 1 := by
    calc
      ‖z - a‖ < ‖F.derivative.aeval a‖ := hza
      _ = (2 : ℝ)⁻¹ := hderiv'
      _ < 1 := by norm_num
  have hzNorm : ‖z‖ = 1 := by
    have hcast : ‖(z : ℚ_[2]) - (a : ℚ_[2])‖ < ‖(a : ℚ_[2])‖ := by
      simpa [haNorm] using hzaOne
    simpa [haNorm] using Padic.norm_eq_of_norm_sub_lt_right hcast
  exact ⟨z, isUnit_iff.mpr hzNorm, hz⟩

end PadicInt

namespace PositiveDefiniteIntegralLattice

private def DyadicNormalizedResidue (c : ZMod 8) : Bool :=
  c.val % 4 != 0

private def DyadicUnitResidue (c : ZMod 8) : Bool :=
  c.val % 2 == 1

private theorem exists_modFour_quinary_zero_selection :
    ∀ c : Fin 5 → ZMod 4,
      (∀ i, c i ≠ 0) →
      3 ≤ (Finset.univ.filter fun i ↦ IsUnit (c i)).card →
      ∃ b : Fin 5 → Bool,
        (∃ i, IsUnit (c i) ∧ b i = true) ∧
        (∃ j, IsUnit (c j) ∧ b j = false) ∧
          (∑ i, if b i then c i else 0) = 0 := by
  set_option maxRecDepth 5000 in
    decide

private def reduceModFour : ZMod 8 →+* ZMod 4 :=
  ZMod.castHom (by norm_num) (ZMod 4)

private lemma reduceModFour_ne_zero_of_normalized
    (c : ZMod 8) (hc : DyadicNormalizedResidue c = true) :
    reduceModFour c ≠ 0 := by
  revert c
  decide

private lemma dyadicUnitResidue_eq_true_of_reduceModFour_isUnit
    (c : ZMod 8) (hc : IsUnit (reduceModFour c)) :
    DyadicUnitResidue c = true := by
  revert c
  decide

private lemma eq_zero_or_four_of_reduceModFour_eq_zero
    (c : ZMod 8) (hc : reduceModFour c = 0) : c = 0 ∨ c = 4 := by
  revert c
  decide

private lemma mul_four_eq_four_of_reduceModFour_isUnit
    (c : ZMod 8) (hc : IsUnit (reduceModFour c)) : c * 4 = 4 := by
  revert c
  decide

private theorem exists_modEight_quinary_zero_of_three_units
    (c : Fin 5 → ZMod 8)
    (hcNormalized : ∀ i, DyadicNormalizedResidue (c i) = true)
    (hthree : ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      IsUnit (c i) ∧ IsUnit (c j) ∧ IsUnit (c k)) :
    ∃ v : Fin 5 → Fin 3,
      (∃ i, DyadicUnitResidue (c i) = true ∧ v i = 1) ∧
        ∑ i, c i * (((v i : ℕ) : ZMod 8) ^ 2) = 0 := by
  classical
  let r : Fin 5 → ZMod 4 := fun i ↦ reduceModFour (c i)
  have hr0 : ∀ i, r i ≠ 0 := fun i ↦
    reduceModFour_ne_zero_of_normalized _ (hcNormalized i)
  have hrThree : 3 ≤ (Finset.univ.filter fun i ↦ IsUnit (r i)).card := by
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := hthree
    have hsubset : ({i, j, k} : Finset (Fin 5)) ⊆
        Finset.univ.filter fun t ↦ IsUnit (r t) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, r] <;>
        apply IsUnit.map <;> assumption
    calc
      3 = ({i, j, k} : Finset (Fin 5)).card := by simp [hij, hik, hjk]
      _ ≤ _ := Finset.card_le_card hsubset
  obtain ⟨b, ⟨i, hiUnit, hbi⟩, ⟨j, hjUnit, hbj⟩, hbzero⟩ :=
    exists_modFour_quinary_zero_selection r hr0 hrThree
  let S : ZMod 8 := ∑ t, if b t then c t else 0
  have hSmod : reduceModFour S = 0 := by
    change reduceModFour (∑ t, if b t then c t else 0) = 0
    rw [map_sum]
    calc
      ∑ t, reduceModFour (if b t then c t else 0) =
          ∑ t, if b t then reduceModFour (c t) else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            by_cases hbt : b t <;> simp [hbt]
      _ = 0 := by simpa only [r] using hbzero
  have hiDyadic : DyadicUnitResidue (c i) = true :=
    dyadicUnitResidue_eq_true_of_reduceModFour_isUnit _ hiUnit
  rcases eq_zero_or_four_of_reduceModFour_eq_zero S hSmod with hS | hS
  · let v : Fin 5 → Fin 3 := fun t ↦ if b t then 1 else 0
    refine ⟨v, ⟨i, hiDyadic, by simp [v, hbi]⟩, ?_⟩
    calc
      ∑ t, c t * (((v t : ℕ) : ZMod 8) ^ 2) = S := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : b t <;> simp [v, ht]
      _ = 0 := hS
  · let v : Fin 5 → Fin 3 := fun t ↦
      if b t then 1 else if t = j then 2 else 0
    refine ⟨v, ⟨i, hiDyadic, by simp [v, hbi]⟩, ?_⟩
    have hjFour : c j * 4 = 4 :=
      mul_four_eq_four_of_reduceModFour_isUnit _ hjUnit
    calc
      ∑ t, c t * (((v t : ℕ) : ZMod 8) ^ 2) =
          ∑ t, ((if b t then c t else 0) +
            if t = j then c j * 4 else 0) := by
              apply Finset.sum_congr rfl
              intro t _
              by_cases hbt : b t
              · have htj : t ≠ j := by
                  intro ht
                  subst t
                  simp [hbj] at hbt
                simp [v, hbt, htj]
              · by_cases htj : t = j
                · subst t
                  simp [v, hbj]
                  ring
                · simp [v, hbt, htj]
      _ = S + c j * 4 := by
        rw [Finset.sum_add_distrib]
        simp [S]
      _ = 0 := by rw [hS, hjFour]; decide

private lemma dyadicUnitResidue_eq_true_of_isUnit
    (c : ZMod 8) (hc : IsUnit c) : DyadicUnitResidue c = true := by
  revert c
  decide

private lemma dyadicNormalizedResidue_eq_true_of_isUnit
    (c : ZMod 8) (hc : IsUnit c) : DyadicNormalizedResidue c = true := by
  revert c
  decide

private lemma dyadicNormalizedResidue_eq_true_of_two_mul_isUnit
    (u : ZMod 8) (hu : IsUnit u) :
    DyadicNormalizedResidue (2 * u) = true := by
  revert u
  decide

private lemma dyadicUnitResidue_eq_false_of_two_mul_isUnit
    (u : ZMod 8) (hu : IsUnit u) :
    DyadicUnitResidue (2 * u) = false := by
  revert u
  decide

private lemma valuationParity_two_mul_eq_one
    {q : ℚ} (hq : q ≠ 0) (hqpar : Rat.valuationParity 2 q = 0) :
    Rat.valuationParity 2 (2 * q) = 1 := by
  unfold Rat.valuationParity at hqpar ⊢
  rw [padicValRat.mul (by norm_num) hq]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    have h : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by norm_num)
    norm_num [padicValRat, h]
  rw [htwo]
  have hmod : padicValRat 2 q % 2 = 0 := by
    have hnonneg : 0 ≤ padicValRat 2 q % 2 := Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hqpar with h | h <;> omega
  rw [Int.add_emod, hmod]
  norm_num

private lemma valuationParity_two_mul_eq_zero
    {q : ℚ} (hq : q ≠ 0) (hqpar : Rat.valuationParity 2 q = 1) :
    Rat.valuationParity 2 (2 * q) = 0 := by
  unfold Rat.valuationParity at hqpar ⊢
  rw [padicValRat.mul (by norm_num) hq]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    have h : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by norm_num)
    norm_num [padicValRat, h]
  rw [htwo]
  have hmod : padicValRat 2 q % 2 = 1 := by
    have hnonneg : 0 ≤ padicValRat 2 q % 2 := Int.emod_nonneg _ (by norm_num)
    rcases Int.natAbs_eq_iff.mp hqpar with h | h <;> omega
  rw [Int.add_emod, hmod]
  norm_num

private theorem exists_dyadic_integral_diagonal_normalization
    {q : ℚ} (hq : q ≠ 0) :
    ∃ s : ℚ, s ≠ 0 ∧ ∃ C : ℤ_[2],
      (IsUnit C ∨ ∃ u : ℤ_[2], IsUnit u ∧ C = 2 * u) ∧
      (C : ℚ_[2]) = ((q * s ^ 2 : ℚ) : ℚ_[2]) ∧
      (Rat.valuationParity 2 q = 0 → IsUnit C) := by
  rcases Rat.valuationParity_eq_zero_or_one 2 q with hpar | hpar
  · obtain ⟨s, hs, C, hC, _, hcast, _⟩ :=
      exists_padicInt_dyadic_unit_target_square_normalization
        hq hpar (r := Rat.dyadicUnitRepresentative q) rfl
    exact ⟨s, hs, C, Or.inl hC, hcast, fun _ ↦ hC⟩
  · obtain ⟨s, hs, U, hU, _, hcast, _⟩ :=
      exists_padicInt_dyadic_twice_unit_target_square_normalization hq hpar
    refine ⟨s, hs, 2 * U, Or.inr ⟨U, hU, rfl⟩, hcast, ?_⟩
    intro hzero
    omega

/-- Five dyadic integral diagonal coefficients, each normalized to a unit or
twice a unit and with at least three units, have a nontrivial zero over
`ℚ_[2]`.  The modulo-eight witness is lifted in a unit coordinate. -/
theorem quinaryDiagonal_gramIsotropic_dyadic_of_integral_normalized
    (C : Fin 5 → ℤ_[2])
    (hnormalized : ∀ i, IsUnit (C i) ∨
      ∃ u : ℤ_[2], IsUnit u ∧ C i = 2 * u)
    (hthree : ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      IsUnit (C i) ∧ IsUnit (C j) ∧ IsUnit (C k)) :
    GramIsotropic (Matrix.diagonal fun i ↦ (C i : ℚ_[2])) := by
  classical
  let c : Fin 5 → ZMod 8 := fun i ↦ PadicInt.toZModPow 3 (C i)
  have hcNormalized : ∀ i, DyadicNormalizedResidue (c i) = true := by
    intro i
    rcases hnormalized i with hi | ⟨u, hu, hi⟩
    · exact dyadicNormalizedResidue_eq_true_of_isUnit _
        (hi.map (PadicInt.toZModPow 3))
    · change DyadicNormalizedResidue
        (PadicInt.toZModPow 3 (C i)) = true
      rw [hi, map_mul, map_ofNat]
      exact dyadicNormalizedResidue_eq_true_of_two_mul_isUnit _
        (hu.map (PadicInt.toZModPow 3))
  have hcThree : ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      IsUnit (c i) ∧ IsUnit (c j) ∧ IsUnit (c k) := by
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := hthree
    exact ⟨i, j, k, hij, hik, hjk,
      by simpa [c] using hi.map (PadicInt.toZModPow 3),
      by simpa [c] using hj.map (PadicInt.toZModPow 3),
      by simpa [c] using hk.map (PadicInt.toZModPow 3)⟩
  obtain ⟨v, ⟨i, hciUnit, hvi⟩, hvzero⟩ :=
    exists_modEight_quinary_zero_of_three_units c hcNormalized hcThree
  have hCi : IsUnit (C i) := by
    rcases hnormalized i with hi | ⟨u, hu, hi⟩
    · exact hi
    · have hfalse : DyadicUnitResidue (c i) = false := by
        change DyadicUnitResidue (PadicInt.toZModPow 3 (C i)) = false
        rw [hi, map_mul, map_ofNat]
        exact dyadicUnitResidue_eq_false_of_two_mul_isUnit _
          (hu.map (PadicInt.toZModPow 3))
      rw [hfalse] at hciUnit
      contradiction
  let x : Fin 5 → ℤ_[2] := fun r ↦ (v r : ℕ)
  have hxi : x i = 1 := by simp [x, hvi]
  let S : ℤ_[2] := ∑ r, C r * x r ^ 2
  let F : Polynomial ℤ_[2] :=
    Polynomial.C (S - C i * x i ^ 2) + Polynomial.C (C i) * Polynomial.X ^ 2
  have hFeval_xi : F.eval (x i) = S := by
    simp [F]
  have hxres : ∀ r, PadicInt.toZModPow 3 (x r) = ((v r : ℕ) : ZMod 8) := by
    intro r
    simp [x]
  have hFmod : PadicInt.toZModPow 3 (F.eval (x i)) = 0 := by
    rw [hFeval_xi]
    change PadicInt.toZModPow 3 (∑ r, C r * x r ^ 2) = 0
    rw [map_sum]
    simp only [map_mul, map_pow, hxres]
    exact hvzero
  have hderiv : ‖F.derivative.eval (x i)‖ = (2 : ℝ)⁻¹ := by
    have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ :=
      @PadicInt.norm_p 2 inferInstance
    have hnormCi : ‖C i‖ = 1 := PadicInt.isUnit_iff.mp hCi
    have heval : F.derivative.eval (x i) = 2 * C i := by
      simp [F, hxi]
      ring
    rw [heval, norm_mul, hnormTwo, hnormCi]
    norm_num
  obtain ⟨z, hzUnit, hz⟩ :=
    PadicInt.exists_unit_polynomial_root_of_unit_root_mod_eight
      F (x i) (hxi ▸ isUnit_one) hFmod hderiv
  let y : Fin 5 → ℤ_[2] := fun r ↦ if r = i then z else x r
  have hyne : y ≠ 0 := by
    intro hy
    have hyi := congrFun hy i
    have hz0 : z = 0 := by simpa [y] using hyi
    exact hzUnit.ne_zero hz0
  refine ⟨fun r ↦ (y r : ℚ_[2]), ?_, ?_⟩
  · intro hy
    apply hyne
    funext r
    exact Subtype.ext (congrFun hy r)
  · simp only [gramQuadraticValue, Matrix.mulVec_diagonal, dotProduct]
    have hiMem : i ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ i
    have hsum : ∑ r, C r * y r ^ 2 = F.eval z := by
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hiMem]
      have hrest :
          ∑ r ∈ (Finset.univ : Finset (Fin 5)) \ {i}, C r * y r ^ 2 =
            S - C i * x i ^ 2 := by
        rw [show S = ∑ r, C r * x r ^ 2 by rfl]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hiMem]
        simp only [add_sub_cancel_left]
        apply Finset.sum_congr rfl
        intro r hr
        have hri : r ≠ i := by simpa using hr
        simp [y, hri]
      rw [hrest]
      simp [F, y]
      ring
    have hsum0 : ∑ r, C r * y r ^ 2 = 0 := hsum.trans hz
    have hsum0q := congrArg Subtype.val hsum0
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsum0q

private theorem quinaryDiagonal_gramIsotropic_dyadic_of_three_even
    (d : Fin 5 → ℚ) (hd : ∀ r, d r ≠ 0)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : Rat.valuationParity 2 (d i) = 0)
    (hj : Rat.valuationParity 2 (d j) = 0)
    (hk : Rat.valuationParity 2 (d k) = 0) :
    GramIsotropic (Matrix.diagonal fun r ↦ (d r : ℚ_[2])) := by
  classical
  choose s hs C hCnormalized hCcast hCeven using
    fun r ↦ exists_dyadic_integral_diagonal_normalization (hd r)
  have hCiso : GramIsotropic (Matrix.diagonal fun r ↦ (C r : ℚ_[2])) :=
    quinaryDiagonal_gramIsotropic_dyadic_of_integral_normalized C
      hCnormalized
      ⟨i, j, k, hij, hik, hjk, hCeven i hi, hCeven j hj, hCeven k hk⟩
  obtain ⟨x, hx, hzero⟩ := hCiso
  let y : Fin 5 → ℚ_[2] := fun r ↦ (s r : ℚ_[2]) * x r
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx
    funext r
    have hyr := congrFun hy r
    have hsr : (s r : ℚ_[2]) ≠ 0 := by exact_mod_cast hs r
    exact (mul_eq_zero.mp (by simpa [y] using hyr)).resolve_left hsr
  · simp only [gramQuadraticValue, Matrix.mulVec_diagonal, dotProduct] at hzero ⊢
    calc
      ∑ r, y r * ((d r : ℚ_[2]) * y r) =
          ∑ r, x r * ((C r : ℚ_[2]) * x r) := by
            apply Finset.sum_congr rfl
            intro r _
            have hcast : (C r : ℚ_[2]) =
                (d r : ℚ_[2]) * (s r : ℚ_[2]) ^ 2 := by
              simpa only [map_mul, map_pow] using hCcast r
            rw [hcast]
            simp [y]
            ring
      _ = 0 := hzero

private theorem exists_three_equal_finTwo :
    ∀ f : Fin 5 → Fin 2,
      ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        f i = f j ∧ f i = f k := by
  decide

private theorem diagonal_gramIsotropic_of_mul_scalar
    {K : Type*} [Field K] (d : Fin 5 → K) (a : K) (ha : a ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal fun r ↦ a * d r)) :
    GramIsotropic (Matrix.diagonal d) := by
  obtain ⟨x, hx, hzero⟩ := hiso
  refine ⟨x, hx, ?_⟩
  simp only [gramQuadraticValue, Matrix.mulVec_diagonal, dotProduct] at hzero ⊢
  apply (mul_left_cancel₀ ha)
  calc
    a * ∑ r, x r * (d r * x r) =
        ∑ r, x r * ((a * d r) * x r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = a * 0 := by simpa using hzero

/-- Every nondegenerate rational diagonal rank-five form is isotropic over
the dyadic field.  A majority of three coefficients has the same valuation
parity.  In the odd-majority case, multiplying the whole form by two toggles
that majority to even parity before integral modulo-eight normalization. -/
theorem quinaryDiagonal_gramIsotropic_dyadic_of_rat
    (d : Fin 5 → ℚ) (hd : ∀ r, d r ≠ 0) :
    GramIsotropic (Matrix.diagonal fun r ↦ (d r : ℚ_[2])) := by
  let par : Fin 5 → Fin 2 := fun r ↦
    ⟨Rat.valuationParity 2 (d r), by
      rcases Rat.valuationParity_eq_zero_or_one 2 (d r) with h | h <;> omega⟩
  obtain ⟨i, j, k, hij, hik, hjk, hijpar, hikpar⟩ :=
    exists_three_equal_finTwo par
  have hijval : Rat.valuationParity 2 (d i) =
      Rat.valuationParity 2 (d j) := congrArg Fin.val hijpar
  have hikval : Rat.valuationParity 2 (d i) =
      Rat.valuationParity 2 (d k) := congrArg Fin.val hikpar
  rcases Rat.valuationParity_eq_zero_or_one 2 (d i) with hi | hi
  · exact quinaryDiagonal_gramIsotropic_dyadic_of_three_even d hd i j k
      hij hik hjk hi (hijval ▸ hi) (hikval ▸ hi)
  · let d' : Fin 5 → ℚ := fun r ↦ 2 * d r
    have hd' : ∀ r, d' r ≠ 0 := fun r ↦ mul_ne_zero (by norm_num) (hd r)
    have hi' : Rat.valuationParity 2 (d' i) = 0 :=
      valuationParity_two_mul_eq_zero (hd i) hi
    have hjpar : Rat.valuationParity 2 (d j) = 1 := hijval.symm.trans hi
    have hkpar : Rat.valuationParity 2 (d k) = 1 := hikval.symm.trans hi
    have hj' : Rat.valuationParity 2 (d' j) = 0 :=
      valuationParity_two_mul_eq_zero (hd j) hjpar
    have hk' : Rat.valuationParity 2 (d' k) = 0 :=
      valuationParity_two_mul_eq_zero (hd k) hkpar
    have hiso' : GramIsotropic (Matrix.diagonal fun r ↦ (d' r : ℚ_[2])) :=
      quinaryDiagonal_gramIsotropic_dyadic_of_three_even d' hd' i j k
        hij hik hjk hi' hj' hk'
    apply diagonal_gramIsotropic_of_mul_scalar
      (fun r ↦ (d r : ℚ_[2])) (2 : ℚ_[2]) (by norm_num)
    simpa [d'] using hiso'

/-- Every nonsingular symmetric rational rank-five form becomes isotropic
over the dyadic field. -/
theorem quinary_gramIsotropic_dyadic_of_rat
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    GramIsotropic (A.map (algebraMap ℚ ℚ_[2])) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det (by norm_num)
  have hdiag : GramIsotropic (Matrix.diagonal fun i ↦ (d i : ℚ_[2])) :=
    quinaryDiagonal_gramIsotropic_dyadic_of_rat d hd
  have hcongr : (A.map (algebraMap ℚ ℚ_[2])).IsCongruent
      ((Matrix.diagonal d).map (algebraMap ℚ ℚ_[2])) :=
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩).map
      (algebraMap ℚ ℚ_[2])
  apply (gramIsotropic_iff_of_isCongruent hcongr).2
  simpa using hdiag

/-- Every nonsingular symmetric rational form of rank at least five becomes
isotropic over the dyadic field.  A rational diagonalization reduces the
claim to its first five coordinates. -/
theorem gramIsotropic_dyadic_of_rat_of_five_le
    {n : ℕ} (hn : 5 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0) :
    GramIsotropic (A.map (algebraMap ℚ ℚ_[2])) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det (by norm_num)
  let dp : Fin (5 + k) → ℚ_[2] := fun i ↦ (d i : ℚ_[2])
  let A₅ : Matrix (Fin 5) (Fin 5) ℚ_[2] :=
    Matrix.diagonal fun i ↦ dp (Fin.castAdd k i)
  let B : Matrix (Fin k) (Fin k) ℚ_[2] :=
    Matrix.diagonal fun i ↦ -dp (Fin.natAdd 5 i)
  have hA₅iso : GramIsotropic A₅ := by
    apply quinaryDiagonal_gramIsotropic_dyadic_of_rat
      (fun i ↦ d (Fin.castAdd k i))
    intro i
    exact hd (Fin.castAdd k i)
  have hblock : GramIsotropic (differenceGramBlock A₅ B) :=
    (gramIsotropic_differenceGramBlock_iff A₅ B).2 (Or.inl hA₅iso)
  have hdiag : GramIsotropic (Matrix.diagonal dp) := by
    rw [← differenceGramBlock_diagonal_split dp]
    exact hblock
  have hcongr : (A.map (algebraMap ℚ ℚ_[2])).IsCongruent
      ((Matrix.diagonal d).map (algebraMap ℚ ℚ_[2])) :=
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩).map
      (algebraMap ℚ ℚ_[2])
  apply (gramIsotropic_iff_of_isCongruent hcongr).2
  simpa [dp] using hdiag

end PositiveDefiniteIntegralLattice
