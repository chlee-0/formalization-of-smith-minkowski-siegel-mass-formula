import SMSFormula.IntegralQuadraticFormCompatibility

/-!
# Even-character compatibility for the integral-quadratic-form conversion

For a lattice form matrix `F`, the scaled integral model of its integral-quadratic-form conversion
stores `2F`.  In even dimension its Dirichlet discriminant is therefore the
discriminant of `F` multiplied by the square `(2^s)^2`.  This module
keeps that square explicit and compares the fixed-modulus character packages through
an explicit `DirichletCharacter.changeLevel`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- In dimension `2s`, the converted scaled integral model's bilinear discriminant is
the old bilinear discriminant multiplied by `(2^s)^2`. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_polarDeterminant_even
    (s : ℕ) (hn : n = 2 * s) :
    L.toIntegralQuadraticForm.latticeOfPolarForm.polarDeterminant =
      ((2 : ℤ) ^ s) ^ 2 * L.polarDeterminant := by
  rw [L.toIntegralQuadraticForm.latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant,
    L.toIntegralQuadraticForm_polarDeterminant]
  have hpow : (2 : ℤ) ^ n = ((2 : ℤ) ^ s) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [hpow]

/-- The even Dirichlet discriminants differ by the same displayed square. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterDiscriminant
    (s : ℕ) (hn : n = 2 * s) :
    goodPrimeEvenCharacterDiscriminant
        L.toIntegralQuadraticForm.latticeOfPolarForm s =
      ((2 : ℤ) ^ s) ^ 2 *
        goodPrimeEvenCharacterDiscriminant L s := by
  unfold goodPrimeEvenCharacterDiscriminant
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_polarDeterminant_even s hn]
  ring

/-- The fixed integral model modulus is the old fixed modulus multiplied by
`2^(2s)`. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus
    (s : ℕ) (hn : n = 2 * s) :
    goodPrimeEvenDirichletModulus
        L.toIntegralQuadraticForm.latticeOfPolarForm s =
      2 ^ (2 * s) * goodPrimeEvenDirichletModulus L s := by
  rw [goodPrimeEvenDirichletModulus,
    goodPrimeEvenDirichletModulus,
    L.toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterDiscriminant s hn,
    Int.natAbs_mul, Int.natAbs_pow]
  norm_num [pow_two, ← pow_add]
  ring

/-- The old fixed modulus divides the converted scaled-integral model modulus. -/
theorem toIntegralQuadraticForm_evenDirichletModulus_dvd_latticeOfPolarForm
    (s : ℕ) (hn : n = 2 * s) :
    goodPrimeEvenDirichletModulus L s ∣
      goodPrimeEvenDirichletModulus
        L.toIntegralQuadraticForm.latticeOfPolarForm s := by
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus s hn]
  exact dvd_mul_left _ _

/-- Multiplying the numerator by the displayed square does not change its
Jacobi value at an odd denominator. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterJacobi_of_odd
    (s a : ℕ) (hn : n = 2 * s) (ha : Odd a) :
    jacobiSym
        (goodPrimeEvenCharacterDiscriminant
          L.toIntegralQuadraticForm.latticeOfPolarForm s) a =
      jacobiSym (goodPrimeEvenCharacterDiscriminant L s) a := by
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterDiscriminant s hn,
    jacobiSym.mul_left]
  have hcop : ((2 : ℤ) ^ s).gcd a = 1 := by
    rw [Int.gcd_eq_natAbs]
    norm_num
    exact (ha.coprime_two_left.pow_left s).gcd_eq_one
  rw [jacobiSym.sq_one' hcop, one_mul]

/-- In the active even-rank branch, the converted scaled-integral model character is
the explicit level change of the original fixed-modulus character. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_eq_changeLevel
    (s : ℕ) (hn : n = 2 * s) :
    goodPrimeEvenDirichletCharacter
        L.toIntegralQuadraticForm.latticeOfPolarForm s =
      DirichletCharacter.changeLevel
        (L.toIntegralQuadraticForm_evenDirichletModulus_dvd_latticeOfPolarForm
          s hn)
        (goodPrimeEvenDirichletCharacter L s) := by
  let S := L.toIntegralQuadraticForm.latticeOfPolarForm
  let m := goodPrimeEvenDirichletModulus L s
  let M := goodPrimeEvenDirichletModulus S s
  let hdiv : m ∣ M :=
    L.toIntegralQuadraticForm_evenDirichletModulus_dvd_latticeOfPolarForm s hn
  letI : NeZero m :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos L s)⟩
  letI : NeZero M :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos S s)⟩
  rw [goodPrimeEvenDirichletCharacter, dif_pos hn,
    goodPrimeEvenDirichletCharacter, dif_pos hn]
  apply MulChar.ext
  intro u
  let v : (ZMod m)ˣ := ZMod.unitsMap hdiv u
  rw [goodPrimeEvenJacobiDirichletCharacter_apply_unit]
  change
    (((jacobiSym (goodPrimeEvenCharacterDiscriminant S s)
      (u : ZMod M).val : ℝ) : ℂ)) =
      (DirichletCharacter.changeLevel hdiv
        (goodPrimeEvenJacobiDirichletCharacter L s))
          (u : ZMod M)
  rw [show (u : ZMod M) = (u : ZMod M) by rfl,
    ← u.isUnit.unit_spec,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]
  change
    (((jacobiSym (goodPrimeEvenCharacterDiscriminant S s)
      (u : ZMod M).val : ℝ) : ℂ)) =
      goodPrimeEvenJacobiDirichletCharacter L s
        (v : ZMod m)
  rw [goodPrimeEvenJacobiDirichletCharacter_apply_unit]
  have hu_odd : Odd (u : ZMod M).val :=
    odd_of_coprime_goodPrimeEvenDirichletModulus
      S s _ (ZMod.val_coe_unit_coprime u)
  have hv_odd : Odd (v : ZMod m).val :=
    odd_of_coprime_goodPrimeEvenDirichletModulus
      L s _ (ZMod.val_coe_unit_coprime v)
  have hcast : ((v : ZMod m).val : ZMod m) = ((u : ZMod M).val : ZMod m) := by
    calc
      ((v : ZMod m).val : ZMod m) = (v : ZMod m) := ZMod.natCast_zmod_val _
      _ = ZMod.cast (u : ZMod M) := ZMod.unitsMap_val hdiv u
      _ = ZMod.cast ((u : ZMod M).val : ZMod M) := by
        rw [ZMod.natCast_zmod_val]
      _ = ((u : ZMod M).val : ZMod m) := ZMod.cast_natCast hdiv _
  have hmod : (u : ZMod M).val % m = (v : ZMod m).val := by
    have hv_lt : (v : ZMod m).val < m := ZMod.val_lt _
    have hmod' : (v : ZMod m).val % m = (u : ZMod M).val % m := by
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    exact hmod'.symm.trans (Nat.mod_eq_of_lt hv_lt)
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterJacobi_of_odd
    s _ hn hu_odd]
  rw [jacobiSym.mod_right _ hu_odd, jacobiSym.mod_right _ hv_odd]
  dsimp [m] at hmod
  unfold goodPrimeEvenDirichletModulus at hmod
  exact congrArg
    (fun t : ℕ => ((jacobiSym (goodPrimeEvenCharacterDiscriminant L s) t : ℝ) : ℂ))
    (hmod.trans (Nat.mod_eq_of_lt (ZMod.val_lt (v : ZMod m))).symm)

/-- The old and scaled-integral model fixed moduli have the same prime support; the
level increase is purely an additional power of two, while the old modulus
already contains four. -/
theorem prime_dvd_toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus_iff
    (s p : ℕ) (hn : n = 2 * s) (hp : Nat.Prime p) :
    p ∣ goodPrimeEvenDirichletModulus
        L.toIntegralQuadraticForm.latticeOfPolarForm s ↔
      p ∣ goodPrimeEvenDirichletModulus L s := by
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus s hn]
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with hpow | hm
    · have hp_two : p ∣ 2 := hp.dvd_of_dvd_pow hpow
      have hp_eq_two : p = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hp_two with hp_one | hp_two
        · exact False.elim (hp.ne_one hp_one)
        · exact hp_two
      rw [hp_eq_two, goodPrimeEvenDirichletModulus]
      exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) _
    · exact hm
  · exact fun h => dvd_mul_of_dvd_right h _

/-- The old and converted scaled-integral model fixed-modulus characters have equal
values at every prime. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_apply_prime
    (s p : ℕ) (hn : n = 2 * s) (hp : Nat.Prime p) :
    goodPrimeEvenDirichletCharacter
        L.toIntegralQuadraticForm.latticeOfPolarForm s p =
      goodPrimeEvenDirichletCharacter L s p := by
  let S := L.toIntegralQuadraticForm.latticeOfPolarForm
  let m := goodPrimeEvenDirichletModulus L s
  let M := goodPrimeEvenDirichletModulus S s
  let hdiv : m ∣ M :=
    L.toIntegralQuadraticForm_evenDirichletModulus_dvd_latticeOfPolarForm s hn
  let χ := goodPrimeEvenDirichletCharacter L s
  letI : NeZero m :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos L s)⟩
  letI : NeZero M :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos S s)⟩
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_eq_changeLevel
    s hn]
  change (DirichletCharacter.changeLevel hdiv χ) p = χ p
  by_cases hpm : p ∣ m
  · have hpM : p ∣ M := by
      exact
        (L.prime_dvd_toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus_iff
          s p hn hp).2 hpm
    have hnonunit_m : ¬ IsUnit (p : ZMod m) := by
      intro hu
      exact (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpm
    have hnonunit_M : ¬ IsUnit (p : ZMod M) := by
      intro hu
      exact (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpM
    rw [MulChar.map_nonunit _ hnonunit_M, MulChar.map_nonunit _ hnonunit_m]
  · have hpM : ¬ p ∣ M := by
      intro hpM
      exact hpm
        ((L.prime_dvd_toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus_iff
          s p hn hp).1 hpM)
    have hunit_M : IsUnit (p : ZMod M) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hp]
      exact hpM
    rw [← hunit_M.unit_spec,
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact congrArg χ (ZMod.cast_natCast hdiv p)

/-- In the absolute-convergence half-plane, the level change introduces no
Euler correction: every prime in the enlarged modulus already divides the old
modulus, so the old character vanishes there. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_LSeries
    (s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    LSeries
        (fun a : ℕ =>
          (goodPrimeEvenDirichletCharacter
            L.toIntegralQuadraticForm.latticeOfPolarForm s a : ℂ))
        ((s : ℕ) : ℂ) =
      LSeries
        (fun a : ℕ =>
          (goodPrimeEvenDirichletCharacter L s a : ℂ))
        ((s : ℕ) : ℂ) := by
  let S := L.toIntegralQuadraticForm.latticeOfPolarForm
  let m := goodPrimeEvenDirichletModulus L s
  let M := goodPrimeEvenDirichletModulus S s
  let hdiv : m ∣ M :=
    L.toIntegralQuadraticForm_evenDirichletModulus_dvd_latticeOfPolarForm s hn
  let χ := goodPrimeEvenDirichletCharacter L s
  letI : NeZero m :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos L s)⟩
  letI : NeZero M :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos S s)⟩
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_eq_changeLevel
    s hn]
  change LSeries (fun a : ℕ => ((DirichletCharacter.changeLevel hdiv χ) a : ℂ))
      ((s : ℕ) : ℂ) =
    LSeries (fun a : ℕ => (χ a : ℂ)) ((s : ℕ) : ℂ)
  have hsC : 1 < (((s : ℕ) : ℂ)).re := by
    norm_num
    exact_mod_cast hs
  rw [DirichletCharacter.LSeries_changeLevel hdiv χ hsC]
  have hprod :
      (∏ p ∈ M.primeFactors,
        (1 - χ p * (p : ℂ) ^ (-((s : ℕ) : ℂ)))) = 1 := by
    apply Finset.prod_eq_one
    intro p hpMmem
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpMmem
    have hpM : p ∣ M := Nat.dvd_of_mem_primeFactors hpMmem
    have hpm : p ∣ m :=
      (L.prime_dvd_toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletModulus_iff
        s p hn hp).1 hpM
    have hnonunit : ¬ IsUnit (p : ZMod m) := by
      intro hu
      exact (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpm
    rw [MulChar.map_nonunit χ hnonunit]
    simp
  rw [hprod, mul_one]

/-- The cutoff-removed complex Dirichlet tails agree in the non-endpoint
half-plane. Both the `LSeries` numerator and every finite cutoff Euler factor
are compared explicitly. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletComplexTailFactor
    (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    goodPrimeEvenDirichletComplexTailFactor
        L.toIntegralQuadraticForm.latticeOfPolarForm N s =
      goodPrimeEvenDirichletComplexTailFactor L N s := by
  unfold goodPrimeEvenDirichletComplexTailFactor
  dsimp
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_LSeries
    s hn hs]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletCharacter_apply_prime
    s p hn (Nat.prime_of_mem_primesBelow hp)]

/-- The real non-endpoint Dirichlet tails agree as the real parts of the
completed complex comparison. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletTailFactorOfCharacter
    (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    goodPrimeEvenDirichletTailFactorOfCharacter
        L.toIntegralQuadraticForm.latticeOfPolarForm N s =
      goodPrimeEvenDirichletTailFactorOfCharacter L N s := by
  unfold goodPrimeEvenDirichletTailFactorOfCharacter
  rw [L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletComplexTailFactor
    N s hn hs]

/-- In the canonical non-endpoint even range, the full endpoint-aware real
Dirichlet tail packages agree. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterDirichletTailFactor
    (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    goodPrimeEvenCharacterDirichletTailFactor
        L.toIntegralQuadraticForm.latticeOfPolarForm N s =
      goodPrimeEvenCharacterDirichletTailFactor L N s := by
  rw [goodPrimeEvenCharacterDirichletTailFactor,
    goodPrimeEvenCharacterDirichletTailFactor,
    if_neg (Nat.ne_of_gt hs), if_neg (Nat.ne_of_gt hs)]
  exact
    L.toIntegralQuadraticForm_latticeOfPolarForm_evenDirichletTailFactorOfCharacter
      N s hn hs

/-- The direct named even limit of the integral quadratic form of a converted lattice
reduces to the original named even limit in the canonical non-endpoint range. -/
theorem toIntegralQuadraticForm_evenRankOrdinaryMassProductLimit
    (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    L.toIntegralQuadraticForm.evenRankOrdinaryMassProductLimit N s =
      L.evenRankOrdinaryMassProductLimit N s := by
  unfold PositiveDefiniteIntegralQuadraticForm.evenRankOrdinaryMassProductLimit
    evenRankOrdinaryMassProductLimit
  rw [L.toIntegralQuadraticForm_massPartialPrimeInverseProduct,
    L.toIntegralQuadraticForm_latticeOfPolarForm_evenCharacterDirichletTailFactor
      N s hn hs]

/-- The complete explicit even product side, including its named limit,
reduces to the original integral-lattice product side. -/
theorem toIntegralQuadraticForm_evenRankExplicitProductSide
    (N s : ℕ) (hn : n = 2 * s) (hs : 1 < s) :
    L.toIntegralQuadraticForm.massFormulaProductSide
        (L.toIntegralQuadraticForm.evenRankOrdinaryMassProductLimit
          N s) =
      L.massFormulaProductSide
        (L.evenRankOrdinaryMassProductLimit N s) := by
  rw [L.toIntegralQuadraticForm_evenRankOrdinaryMassProductLimit
      N s hn hs,
    L.toIntegralQuadraticForm_massFormulaProductSide]

end PositiveDefiniteIntegralLattice

end
