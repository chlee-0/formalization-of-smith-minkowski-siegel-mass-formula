import SMSFormula.QuadraticPadicCayleyGoodPlaceAlmostAll
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRangeGoodPlace

/-!
# Good places of the block control the good places of the lower form

For `B = W ⊕ ⟨a⟩`: if the place `v` is not an odd-unimodular bad place of `B` and `a` is a
`v`-adic unit, then `v` is not an odd-unimodular bad place of `W`, its prime is not one of the
exceptional primes of `(W, a)`, and it is odd.  Uses `det F_B = det F_W · a` and the factorisation of
the block's entry-denominator product.  Nothing is chosen.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

/-- `‖q‖_p = 1` iff `p` divides neither the numerator nor the denominator. -/
theorem not_dvd_num_den_of_norm_eq_one {p : ℕ} [Fact p.Prime] {q : ℚ}
    (h : ‖(algebraMap ℚ ℚ_[p] q)‖ = 1) : ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hnum : ‖((q.num : ℤ) : ℚ_[p])‖ ≤ 1 := by
    exact_mod_cast PadicInt.norm_le_one (q.num : ℤ_[p])
  have hden : ‖((q.den : ℕ) : ℚ_[p])‖ ≤ 1 := by
    exact_mod_cast PadicInt.norm_le_one (q.den : ℤ_[p])
  have hden0 : ((q.den : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast q.den_nz
  have hnorm : ‖(algebraMap ℚ ℚ_[p] q)‖ = ‖((q.num : ℤ) : ℚ_[p])‖ / ‖((q.den : ℕ) : ℚ_[p])‖ := by
    conv_lhs => rw [hq]
    rw [map_div₀, norm_div]
    simp
  have hcop := q.reduced
  constructor
  · intro hp
    have hpz : (p : ℤ) ∣ q.num := Int.natCast_dvd.mpr hp
    have hlt : ‖((q.num : ℤ) : ℚ_[p])‖ < 1 := by
      have := (PadicInt.norm_int_lt_one_iff_dvd q.num).mpr hpz
      exact_mod_cast this
    have hpd : ¬ p ∣ q.den := fun hd ↦ (Fact.out : p.Prime).not_dvd_one
      (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hp hd)
    have hd1 : ‖((q.den : ℕ) : ℚ_[p])‖ = 1 := by
      have h1 : ¬ ‖((q.den : ℤ) : ℚ_[p])‖ < 1 := fun hlt' ↦
        hpd (Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt')))
      exact le_antisymm hden (by exact_mod_cast not_lt.mp h1)
    rw [hnorm, hd1, div_one] at h
    linarith
  · intro hp
    have hlt : ‖((q.den : ℕ) : ℚ_[p])‖ < 1 := by
      have := (PadicInt.norm_int_lt_one_iff_dvd (q.den : ℤ)).mpr (Int.natCast_dvd_natCast.mpr hp)
      exact_mod_cast this
    have hpos : 0 < ‖((q.den : ℕ) : ℚ_[p])‖ := norm_pos_iff.mpr hden0
    rw [hnorm, div_eq_one_iff_eq hpos.ne'] at h
    have hnlt : ‖((q.num : ℤ) : ℚ_[p])‖ < 1 := h ▸ hlt
    have hpn : (p : ℤ) ∣ q.num := (PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hnlt)
    exact (Fact.out : p.Prime).not_dvd_one
      (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd (Int.natCast_dvd.mp hpn) hp)

theorem norm_eq_one_of_not_dvd_num_den {p : ℕ} [Fact p.Prime] {q : ℚ}
    (h1 : ¬ p ∣ q.num.natAbs) (h2 : ¬ p ∣ q.den) : ‖(algebraMap ℚ ℚ_[p] q)‖ = 1 := by
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hn : ‖((q.num : ℤ) : ℚ_[p])‖ = 1 := by
    have hle : ‖((q.num : ℤ) : ℚ_[p])‖ ≤ 1 := by exact_mod_cast PadicInt.norm_le_one (q.num : ℤ_[p])
    refine le_antisymm hle (not_lt.mp fun hlt ↦ h1 ?_)
    exact Int.natCast_dvd.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt))
  have hd : ‖((q.den : ℕ) : ℚ_[p])‖ = 1 := by
    have hle : ‖((q.den : ℕ) : ℚ_[p])‖ ≤ 1 := by exact_mod_cast PadicInt.norm_le_one (q.den : ℤ_[p])
    refine le_antisymm hle (not_lt.mp fun hlt ↦ h2 ?_)
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt))
  conv_lhs => rw [hq]
  rw [map_div₀, norm_div]
  simp only [map_intCast, map_natCast] at *
  rw [hn, hd, div_one]

/-- The entry-denominator product of the block `diag(F, a)`. -/
theorem matrixDenominatorProduct_nonisotropicLastBlockMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ)
    (a : ℚ) :
    Rat.matrixDenominatorProduct (nonisotropicLastBlockMatrix F a) =
      Rat.matrixDenominatorProduct F * a.den := by
  unfold Rat.matrixDenominatorProduct
  rw [Fin.prod_univ_castSucc]
  simp [Fin.prod_univ_castSucc]

set_option maxHeartbeats 800000 in
/-- Good places of the block: off the odd-unimodular bad set of `B = W ⊕ ⟨a⟩`, with `a` a unit,
the place is odd, not odd-unimodular bad for `W`, and not an exceptional prime of `(W, a)`. -/
theorem goodConditions_of_not_mem_oddUnimodular_block {n : ℕ} (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hau : letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
      ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] a‖ = 1) :
    v ∉ W.cliffordSpinCandidateOddUnimodularBadPlaces ∧
      (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha ∧
      (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2 := by
  set p := (Rat.HeightOneSpectrum.primesEquiv v).1 with hpdef
  haveI : Fact (Nat.Prime p) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hpp : p.Prime := Fact.out
  set FB := (W.nonisotropicLastExtension a ha).pairingMatrix
  set FW := W.pairingMatrix
  have hFB : FB = nonisotropicLastBlockMatrix FW a := rfl
  have hdetB : FB.det = FW.det * a := by rw [hFB]; exact nonisotropicLastBlockMatrix_det _ _
  have hdB0 : FB.det ≠ 0 := (W.nonisotropicLastExtension a ha).form_det_ne_zero
  have hdW0 : FW.det ≠ 0 := W.form_det_ne_zero
  -- the block support is not divisible by p
  rw [mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff] at hv
  have hSB : ¬ p ∣ Rat.matrixPairBadPrimeSupportNat FB FB := by
    intro hd
    apply hv
    unfold Rat.matrixPairBadPrimeSet
    refine Nat.mem_primeFactors.mpr ⟨hpp, hd, ?_⟩
    unfold Rat.matrixPairBadPrimeSupportNat Rat.matrixDenominatorProduct
    have h1 : FB.det.num.natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero]; exact Rat.num_ne_zero.mpr hdB0
    have h2 := FB.det.den_nz
    have h3 : ∏ i, ∏ j, (FB i j).den ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j _ ↦ (FB i j).den_nz
    positivity
  unfold Rat.matrixPairBadPrimeSupportNat at hSB
  simp only [hpp.dvd_mul, not_or] at hSB
  obtain ⟨⟨⟨⟨⟨⟨h2, hdp⟩, -⟩, hnum⟩, hden⟩, -⟩, -⟩ := hSB
  have hp2 : p ≠ 2 := fun h ↦ h2 (h ▸ dvd_refl _)
  have hdpW : ¬ p ∣ Rat.matrixDenominatorProduct FW := fun h ↦ hdp (by
    rw [hFB, matrixDenominatorProduct_nonisotropicLastBlockMatrix]; exact h.mul_right _)
  have hnB := norm_eq_one_of_not_dvd_num_den (p := p) hnum hden
  have hnW : ‖algebraMap ℚ ℚ_[p] FW.det‖ = 1 := by
    rw [hdetB, map_mul, norm_mul, hau, mul_one] at hnB
    exact hnB
  obtain ⟨hWn, hWd⟩ := not_dvd_num_den_of_norm_eq_one hnW
  obtain ⟨han, had⟩ := not_dvd_num_den_of_norm_eq_one (p := p) hau
  refine ⟨?_, ?_, hp2⟩
  · rw [mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff]
    unfold Rat.matrixPairBadPrimeSet
    intro hmem
    have hd : p ∣ Rat.matrixPairBadPrimeSupportNat FW FW := (Nat.mem_primeFactors.mp hmem).2.1
    unfold Rat.matrixPairBadPrimeSupportNat at hd
    simp only [hpp.dvd_mul] at hd
    rcases hd with ((((((h | h) | h) | h) | h) | h) | h)
    · exact h2 h
    · exact hdpW h
    · exact hdpW h
    · exact hWn h
    · exact hWd h
    · exact hWn h
    · exact hWd h
  · unfold goodPlaceExceptionalPrimes
    rw [show (W.nonisotropicLastExtension a ha).pairingMatrix = FB from rfl]
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Nat.mem_primeFactors, not_or, not_exists, not_and]
    refine ⟨⟨⟨⟨⟨hp2, fun i _ hd _ ↦ hdp (hd.trans (Rat.matrix_entry_den_dvd_denominatorProduct FB
      i.1 i.2))⟩, fun _ hd _ ↦ hnum hd⟩, fun _ hd _ ↦ hden hd⟩, fun _ hd _ ↦ han hd⟩,
      fun _ hd _ ↦ had hd⟩

end RationalQuadraticSpaceMatrix
