import SMSFormula.LocalDensity
import SMSFormula.StandardAxiomsGuard

/-!
# The literal local-density quotient in rank one

These reductions keep the arbitrary quadratic coefficient and the current
`F`-dual denominator. In particular, a quotient solution is characterized
by its actual scalar representative, rather than by a stabilizer count.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

lemma quadForm_rank_one (L : PositiveDefiniteIntegralLattice 1) (x : Fin 1 → ℤ) :
    L.quadForm x = L.pairingMatrix 0 0 * x 0 ^ 2 := by
  rw [quadForm_eq_dotProduct]
  simp [dotProduct, Matrix.mulVec, pow_two]
  ring

/-- Membership in the actual integral integral model of the `F`-dual denominator
is one scalar divisibility condition. No unit-coefficient assumption occurs. -/
theorem mem_localDualPadicDenominatorIntegralPreimage_rank_one_iff
    (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime] (d : Fin 1 → ℤ) :
    d ∈ localDualPadicDenominatorIntegralPreimage L p k ↔
      (p : ℤ) ^ k ∣ L.pairingMatrix 0 0 * d 0 := by
  rw [localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule,
    localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule]
  change matrixModLinearMap L.pairingMatrix p k d = 0 ↔ _
  simp only [funext_iff, Fin.forall_fin_one]
  change ((matrixMod L.pairingMatrix (primePowModulus p k)).mulVec
    (fun i => (d i : ZMod (primePowModulus p k : ℕ)) )) 0 = 0 ↔ _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, matrixMod, Matrix.map_apply]
  rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

/-- A rank-one family represented by `t` is a solution exactly when
`a * (t^2 - 1)` vanishes modulo the original prime-power modulus. -/
theorem scalar_mem_localDualQuotientSolutionFamilies_rank_one_iff
    (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime] (t : ℤ) :
    (fun _ : Fin 1 =>
      (localDualPadicDenominatorIntegralPreimage L p k).mkQ (fun _ => t)) ∈
        localDualQuotientSolutionFamilies L p k
          (localDualPadicDenominatorIntegralPreimage L p k)
          (localDualPadicDenominatorIntegralPreimage_rank L p k) ↔
      (p : ℤ) ^ k ∣ L.pairingMatrix 0 0 * (t ^ 2 - 1) := by
  let D := localDualPadicDenominatorIntegralPreimage L p k
  have hmap (x : Fin 1 → ℤ) :
      quotientBasisFamilyMap D (fun _ => D.mkQ (fun _ : Fin 1 => t)) x =
        D.mkQ (fun _ => t * x 0) := by
    simp only [quotientBasisFamilyMap, Fin.sum_univ_one]
    rw [← map_smul]
    congr 1
    ext i
    simp [mul_comm]
  rw [mem_localDualQuotientSolutionFamilies_iff]
  constructor
  · intro h
    have hunit := h (fun _ => 1) (fun _ => t) (by simpa using hmap (fun _ => 1))
    simp only [quadForm_rank_one, one_pow, mul_one] at hunit
    have hz : ((L.pairingMatrix 0 0 * (t ^ 2 - 1) : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0 := by
      push_cast
      rw [mul_sub, mul_one, sub_eq_zero]
      simpa using hunit
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  · intro ht x y hxy
    have hy : y - (fun _ : Fin 1 => t * x 0) ∈ D := by
      apply (Submodule.Quotient.eq D).mp
      exact (hmap x).symm.trans hxy |>.symm
    have hrep := (localDualPadicDenominatorIntegralPreimage_admissible L p k).2 hy
    apply hrep.trans
    simp only [quadForm_rank_one]
    have hz : ((L.pairingMatrix 0 0 * (t ^ 2 - 1) : ℤ) :
        ZMod (primePowModulus p k : ℕ)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ht
    push_cast at hz ⊢
    calc
      _ = (L.pairingMatrix 0 0 : ZMod (primePowModulus p k : ℕ)) *
          (t ^ 2 - 1) * (x 0) ^ 2 + L.pairingMatrix 0 0 * (x 0) ^ 2 := by ring
      _ = _ := by rw [hz]; ring

/-- In rank one the determinant exponent is zero and the two dyadic
conversion factors cancel. The separate full-O factor `1/2` remains. -/
theorem normalizedLocalDensity_eq_half_localDualQuotientCount_rank_one
    (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime]
    (hk : IsLocalDensityHenselExponent L p k) :
    normalizedLocalDensity L p = (localDualQuotientCount L p k : ℝ) / 2 := by
  rw [normalizedLocalDensity_eq_fixedK L p k hk,
    normalizedLocalDensityAtExponent_eq_localDualQuotientCount]
  unfold gramDetPadicNormFactor localDensityDenominatorExponent
    dualCountNormalizationFactor twoPadicNormInvPow
  split_ifs <;> norm_num <;> ring

private lemma prime_pow_dvd_mul_rank_one_iff (p k : ℕ) [Fact p.Prime]
    (a t : ℤ) (ha : a ≠ 0) :
    (p : ℤ) ^ k ∣ a * t ↔ (p : ℤ) ^ (k - padicValInt p a) ∣ t := by
  by_cases ht : t = 0
  · simp [ht]
  rw [padicValInt_dvd_iff, padicValInt_dvd_iff,
    padicValInt.mul ha ht]
  simp only [mul_ne_zero ha ht, ht, false_or]
  omega

/-- The actual rank-one `F`-dual quotient has the reduced modulus
`p^(k-v_p(a))`, including depths at or below the coefficient valuation. -/
theorem localDualPadicDenominatorIntegralPreimage_rank_one_eq_primePow
    (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime] :
    localDualPadicDenominatorIntegralPreimage L p k =
      primePowCoordinateSubmodule (n := 1) p (k - padicValInt p (L.pairingMatrix 0 0)) := by
  have ha : L.pairingMatrix 0 0 ≠ 0 := by
    have h := L.pairingDeterminant_pos
    simpa [pairingDeterminant, Matrix.det_fin_one] using ne_of_gt h
  ext d
  rw [mem_localDualPadicDenominatorIntegralPreimage_rank_one_iff,
    mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  simp only [Fin.forall_fin_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact prime_pow_dvd_mul_rank_one_iff p k _ _ ha

private def rankOneScalarFamily (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime]
    (t : ℤ) : Fin 1 → localDualQuotientTarget
      (localDualPadicDenominatorIntegralPreimage L p k) :=
  fun _ => (localDualPadicDenominatorIntegralPreimage L p k).mkQ (fun _ => t)

private lemma rankOneScalarFamily_eq_iff (L : PositiveDefiniteIntegralLattice 1)
    (p k : ℕ) [Fact p.Prime] (s t : ℤ) :
    rankOneScalarFamily L p k s = rankOneScalarFamily L p k t ↔
      (s : ZMod (p ^ (k - padicValInt p (L.pairingMatrix 0 0)))) = t := by
  rw [funext_iff, Fin.forall_fin_one]
  change Submodule.Quotient.mk (fun _ : Fin 1 => s) =
    Submodule.Quotient.mk (fun _ : Fin 1 => t) ↔ _
  rw [Submodule.Quotient.eq,
    localDualPadicDenominatorIntegralPreimage_rank_one_eq_primePow,
    mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  simp only [Fin.forall_fin_one, Pi.sub_apply, primePowModulus]
  change ((s - t : ℤ) : ZMod (p ^ (k - padicValInt p (L.pairingMatrix 0 0)))) = 0 ↔ _
  rw [Int.cast_sub, sub_eq_zero]

private lemma rankOneScalarFamily_mem_iff (L : PositiveDefiniteIntegralLattice 1)
    (p k : ℕ) [Fact p.Prime] (t : ℤ) :
    rankOneScalarFamily L p k t ∈ localDualQuotientSolutionFamilies L p k
      (localDualPadicDenominatorIntegralPreimage L p k)
      (localDualPadicDenominatorIntegralPreimage_rank L p k) ↔
      (t : ZMod (p ^ (k - padicValInt p (L.pairingMatrix 0 0)))) ^ 2 = 1 := by
  have ha : L.pairingMatrix 0 0 ≠ 0 := by
    simpa [pairingDeterminant, Matrix.det_fin_one] using
      ne_of_gt L.pairingDeterminant_pos
  unfold rankOneScalarFamily
  rw [scalar_mem_localDualQuotientSolutionFamilies_rank_one_iff,
    prime_pow_dvd_mul_rank_one_iff p k _ _ ha]
  change ((p ^ (k - padicValInt p (L.pairingMatrix 0 0)) : ℕ) : ℤ) ∣ t ^ 2 - 1 ↔ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [sub_eq_zero]

/-- The actual quotient solution families, for an arbitrary positive
coefficient, are exactly the square roots of one modulo `p^(k-v_p(a))`.
This statement includes `k <= v_p(a)` and does not assume Hensel depth. -/
theorem localDualQuotientCount_rank_one_eq_card_roots
    (L : PositiveDefiniteIntegralLattice 1) (p k : ℕ) [Fact p.Prime] :
    localDualQuotientCount L p k =
      Nat.card {z : ZMod (p ^ (k - padicValInt p (L.pairingMatrix 0 0))) // z ^ 2 = 1} := by
  classical
  let r := k - padicValInt p (L.pairingMatrix 0 0)
  let R := {z : ZMod (p ^ r) // z ^ 2 = 1}
  let f : R → localDualQuotientSolutionFamily L p k := fun z =>
    ⟨rankOneScalarFamily L p k (ZMod.cast z.1 : ℤ),
      (rankOneScalarFamily_mem_iff L p k _).mpr (by
        simpa [r, ZMod.intCast_zmod_cast] using z.2)⟩
  have hinj : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    have hcast := (rankOneScalarFamily_eq_iff L p k _ _).mp
      (congrArg Subtype.val h)
    simpa [r, ZMod.intCast_zmod_cast] using hcast
  have hsurj : Function.Surjective f := by
    intro Y
    obtain ⟨x, hx⟩ := (localDualPadicDenominatorIntegralPreimage L p k).mkQ_surjective (Y.1 0)
    have hY : rankOneScalarFamily L p k (x 0) = Y.1 := by
      ext i
      fin_cases i
      change (localDualPadicDenominatorIntegralPreimage L p k).mkQ
        (fun _ : Fin 1 => x 0) = Y.1 0
      calc
        _ = (localDualPadicDenominatorIntegralPreimage L p k).mkQ x := by
          congr 1
          ext j
          fin_cases j
          rfl
        _ = _ := hx
    have hroot := (rankOneScalarFamily_mem_iff L p k (x 0)).mp (hY ▸ Y.2)
    refine ⟨⟨(x 0 : ZMod (p ^ r)), hroot⟩, ?_⟩
    apply Subtype.ext
    change rankOneScalarFamily L p k (ZMod.cast (x 0 : ZMod (p ^ r)) : ℤ) = Y.1
    rw [← hY, rankOneScalarFamily_eq_iff]
    exact ZMod.intCast_zmod_cast _
  rw [localDualQuotientCount_eq_natCard_solutionFamily]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

private lemma square_eq_one_zmod_odd_prime_pow_iff
    (p r : ℕ) [Fact p.Prime] (hp : p ≠ 2) (z : ZMod (p ^ r)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    let t : ℤ := ZMod.cast z
    have hcast : (t : ZMod (p ^ r)) = z := ZMod.intCast_zmod_cast _
    have hprod : (p : ℤ) ^ r ∣ (t - 1) * (t + 1) := by
      change ((p ^ r : ℕ) : ℤ) ∣ (t - 1) * (t + 1)
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcast]
      calc
        _ = z ^ 2 - 1 := by ring
        _ = 0 := by rw [hz]; ring
    have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    have hp2 : ¬ (p : ℤ) ∣ 2 := by
      intro h
      have hnat : p ∣ 2 := by exact_mod_cast h
      exact hp (((Nat.Prime.dvd_iff_eq Nat.prime_two
        (Fact.out : p.Prime).ne_one).mp hnat).symm)
    have heither : (p : ℤ) ^ r ∣ t - 1 ∨ (p : ℤ) ^ r ∣ t + 1 := by
      by_cases hminus : (p : ℤ) ∣ t - 1
      · left
        have hplus : ¬ (p : ℤ) ∣ t + 1 := by
          intro h
          apply hp2
          convert dvd_sub h hminus using 1
          ring
        exact ((Prime.coprime_iff_not_dvd hpprime).mpr hplus).pow_left.dvd_of_dvd_mul_right hprod
      · right
        exact ((Prime.coprime_iff_not_dvd hpprime).mpr hminus).pow_left.dvd_of_dvd_mul_left hprod
    rcases heither with h | h
    · left
      have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (t - 1) (p ^ r)).mpr h
      simpa [Int.cast_sub, hcast, sub_eq_zero] using hc
    · right
      have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (t + 1) (p ^ r)).mpr h
      simpa [Int.cast_add, hcast, add_eq_zero_iff_eq_neg] using hc
  · rintro (rfl | rfl) <;> norm_num

private lemma card_roots_odd_prime_cube (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card {z : ZMod (p ^ 3) // z ^ 2 = 1} = 2 := by
  have hlarge : 2 < p ^ 3 := lt_of_lt_of_le (by norm_num : 2 < 2 ^ 3)
    (pow_le_pow_left' (Fact.out : p.Prime).two_le 3)
  letI : Fact (2 < p ^ 3) := ⟨hlarge⟩
  let f : Bool → {z : ZMod (p ^ 3) // z ^ 2 = 1} := fun b =>
    if b then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩
  have hinj : Function.Injective f := by
    intro b c h
    cases b <;> cases c <;> simp_all [f, ZMod.neg_one_ne_one,
      Ne.symm (ZMod.neg_one_ne_one (n := p ^ 3))]
  have hsurj : Function.Surjective f := by
    intro z
    rcases (square_eq_one_zmod_odd_prime_pow_iff p 3 hp z.1).mp z.2 with h | h
    · exact ⟨true, Subtype.ext (by simpa [f] using h.symm)⟩
    · exact ⟨false, Subtype.ext (by simpa [f] using h.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simp

private lemma preferred_rank_one_gap (L : PositiveDefiniteIntegralLattice 1)
    (p : ℕ) [Fact p.Prime] :
    localDensityHenselExponent L p - padicValInt p (L.pairingMatrix 0 0) =
      if p = 2 then 4 else 3 := by
  unfold localDensityHenselExponent
  rw [polarDeterminant_eq_two_pow_mul_pairingDeterminant]
  simp only [pow_one]
  rw [padicValInt.mul (by norm_num : (2 : ℤ) ≠ 0)
    (ne_of_gt L.pairingDeterminant_pos)]
  simp only [pairingDeterminant, Matrix.det_fin_one]
  by_cases hp : p = 2
  · subst p
    have htwo : padicValInt 2 (2 : ℤ) = 1 := padicValInt_self
    rw [htwo]
    simp only [ite_true]
    omega
  · have htwo := padicValInt_two_pow_eq_zero_of_ne_two p 1 hp
    simp only [pow_one] at htwo
    simp [hp, htwo]

private def rankOneRootCount (m : ℕ) : ℕ :=
  Nat.card {z : ZMod m // z ^ 2 = 1}

/-- The normalized local density of every positive rank-one integral lattice
is one at an odd prime and two at the dyadic prime.  The statement uses the
definition with all its dual conversion and Hensel conditions. -/
theorem normalizedLocalDensity_rank_one (L : PositiveDefiniteIntegralLattice 1)
    (p : ℕ) [Fact p.Prime] :
    normalizedLocalDensity L p = if p = 2 then 2 else 1 := by
  rw [normalizedLocalDensity_eq_half_localDualQuotientCount_rank_one
    L p (localDensityHenselExponent L p) (isLocalDensityHenselExponent_preferred L p),
    localDualQuotientCount_rank_one_eq_card_roots]
  change (rankOneRootCount
    (p ^ (localDensityHenselExponent L p - padicValInt p (L.pairingMatrix 0 0))) : ℝ) / 2 = _
  rw [preferred_rank_one_gap]
  by_cases hp : p = 2
  · subst p
    simp only [ite_true]
    change (Nat.card {z : ZMod 16 // z ^ 2 = 1} : ℝ) / 2 = 2
    have hcard : Nat.card {z : ZMod 16 // z ^ 2 = 1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hcard]
    norm_num
  · simp only [hp, ite_false]
    change (Nat.card {z : ZMod (p ^ 3) // z ^ 2 = 1} : ℝ) / 2 = 1
    rw [card_roots_odd_prime_cube p hp]
    norm_num

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.quadForm_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.mem_localDualPadicDenominatorIntegralPreimage_rank_one_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.scalar_mem_localDualQuotientSolutionFamilies_rank_one_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.normalizedLocalDensity_eq_half_localDualQuotientCount_rank_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.localDualPadicDenominatorIntegralPreimage_rank_one_eq_primePow
#assert_standard_axioms PositiveDefiniteIntegralLattice.localDualQuotientCount_rank_one_eq_card_roots
#assert_standard_axioms PositiveDefiniteIntegralLattice.normalizedLocalDensity_rank_one
