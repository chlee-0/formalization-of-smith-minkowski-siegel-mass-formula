import SMSFormula.RationalLatticeCosetResidueCount

/-!
# Coset Gauss–Ramanujan coefficients: orthogonality, multiplicativity and good primes


For `u ∈ ℤⁿ⁺¹`, `λ ∈ ℤ` and the coset polynomial `P_u(z) = q(z) + uᵀz`:

* the level term `N⁻ⁿ⁻¹ Σ_{z mod N} e(j(λ - P_u(z))/N)` depends only on the rational `j/N`
  (`cosetLevelTerm_eq_cosetTerm`, via uniform fibres of `(ℤ/N)ⁿ⁺¹ → (ℤ/den)ⁿ⁺¹`);
* the coefficients `A^{cos}_c = Σ*_{a mod c} cosetTerm(a/c)` (`cosetGRCoeff`) satisfy the orthogonality
  identity (4.6) `Σ_{c ∣ N} A^{cos}_c = R_N(u, λ)` (`sum_divisors_cosetGRCoeff`);
* hence `A^{cos} = R * μ` is multiplicative, `A^{cos}_1 = 1` and
  `A^{cos}_{p^{k+1}} = R_{p^{k+1}} - R_{p^k}`;
* at every prime `p ∤ D`, `A^{cos}_{p^k}(u, λ) = A_{p^k}(q(adj(S) u) + D²λ)`, the standard coefficient at
  the fixed target (`cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient`), by the good-level reduction of the
  counts.
The explicit form `A^{cos}_c = c⁻ⁿ⁻¹ Σ*_a e(λa/c) G_u(c, a)` of the row identity (4.2) is
`cosetGRCoeff_eq_cosetGaussRamanujanCoefficient`.  Nothing is chosen.
-/

noncomputable section

open Matrix Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The level term and its level independence -/

/-- The level-`N` coset term `N⁻ᵏ Σ_{z mod N} e(j (λ - P_u(z)) / N)` in rank `k`. -/
def cosetLevelTerm {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ) (N : ℕ) [NeZero N]
    (j : ℤ) : ℂ :=
  ((N : ℂ) ^ k)⁻¹ * ∑ z : Fin k → ZMod N,
    ZMod.stdAddChar ((j : ZMod N) * ((lam : ZMod N) - L.zmodCosetPoly u N z))

/-- The coset term as a function of the rational `t`, computed at the level `den t`. -/
def cosetTerm {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ) (t : ℚ) : ℂ :=
  haveI : NeZero t.den := ⟨t.den_nz⟩
  L.cosetLevelTerm u lam t.den t.num

theorem zmodPiCast_apply {k m c : ℕ} (h : c ∣ m) (z : Fin k → ZMod m) :
    zmodPiCast h z = fun i ↦ ZMod.castHom h (ZMod c) (z i) :=
  rfl

/-- The character at `j/N` is the character at the reduced fraction `a/c`. -/
theorem stdAddChar_mul_eq_of_dvd {N c : ℕ} [NeZero N] [NeZero c] (h : c ∣ N) {j a : ℤ}
    (hja : a * N = j * c) (x : ZMod N) :
    ZMod.stdAddChar ((j : ZMod N) * x) = ZMod.stdAddChar ((a : ZMod c) * ZMod.castHom h (ZMod c) x) := by
  have hx : x = (((x.val : ℕ) : ℤ) : ZMod N) := by simp
  have hcx : ZMod.castHom h (ZMod c) x = (((x.val : ℕ) : ℤ) : ZMod c) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]
  rw [hcx]
  conv_lhs => rw [hx]
  rw [← Int.cast_mul, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hja' : (a : ℂ) * N = j * c := by exact_mod_cast hja
  rw [div_eq_div_iff hN hc]
  push_cast
  linear_combination (-(2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ))) * hja'

/-- Level independence: the level term at `j/N` is the coset term of the rational `j/N`. -/
theorem cosetLevelTerm_eq_cosetTerm {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ)
    (N : ℕ) [NeZero N] (j : ℤ) :
    L.cosetLevelTerm u lam N j = L.cosetTerm u lam ((j : ℚ) / N) := by
  set t : ℚ := (j : ℚ) / N with ht
  haveI : NeZero t.den := ⟨t.den_nz⟩
  have hdvd : t.den ∣ N := by
    have h := Rat.den_dvd j N
    rw [Rat.divInt_eq_div, Int.cast_natCast] at h
    exact Int.natCast_dvd_natCast.1 h
  have hja : t.num * N = j * t.den := by
    have h1 : (t.num : ℚ) / t.den = (j : ℚ) / N := Rat.num_div_den t
    have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hc : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
    rw [div_eq_div_iff hc hN] at h1
    exact_mod_cast h1
  unfold cosetTerm cosetLevelTerm
  have hpt : ∀ z : Fin k → ZMod N,
      ZMod.stdAddChar ((j : ZMod N) * ((lam : ZMod N) - L.zmodCosetPoly u N z)) =
        ZMod.stdAddChar ((t.num : ZMod t.den) *
          ((lam : ZMod t.den) - L.zmodCosetPoly u t.den (zmodPiCast hdvd z))) := by
    intro z
    rw [stdAddChar_mul_eq_of_dvd hdvd hja, map_sub, map_intCast, L.zmodCosetPoly_map u, zmodPiCast_apply]
  simp_rw [hpt]
  rw [sum_comp_eq_card_ker_smul (zmodPiCast (k := k) hdvd)
    (fun w ↦ ZMod.stdAddChar ((t.num : ZMod t.den) * ((lam : ZMod t.den) - L.zmodCosetPoly u t.den w)))
    (fun w hw ↦ absurd (zmodPiCast_surjective hdvd w) hw), nsmul_eq_mul, ← mul_assoc]
  congr 1
  have hK := card_ker_zmodPiCast_mul (k := k) hdvd
  have hK' : ((univ.filter fun y ↦ zmodPiCast (k := k) hdvd y = 0).card : ℂ) * (t.den : ℂ) ^ k =
      (N : ℂ) ^ k := by exact_mod_cast hK
  have hN : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  have hc : (t.den : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast t.den_nz)
  have hK0 : ((univ.filter fun y ↦ zmodPiCast (k := k) hdvd y = 0).card : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hK'
    exact hN hK'.symm
  rw [← hK']
  field_simp

/-! ## The coefficients and the orthogonality identity (4.6) -/

/-- The coset Gauss–Ramanujan coefficient `A^{cos}_c(u, λ) = Σ*_{a mod c} cosetTerm(a/c)`. -/
def cosetGRCoeff {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ) (c : ℕ) : ℂ :=
  ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a), L.cosetTerm u lam ((a : ℚ) / c)

/-- The explicit form used by the row identity (4.2). -/
theorem cosetGRCoeff_eq_cosetGaussRamanujanCoefficient {k : ℕ} (L : PositiveDefiniteIntegralLattice k)
    (u : Fin k → ℤ) (lam : ℤ) (c : ℕ) [NeZero c] :
    L.cosetGRCoeff u lam c = L.cosetGaussRamanujanCoefficient u lam c := by
  unfold cosetGRCoeff cosetGaussRamanujanCoefficient
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h := L.cosetLevelTerm_eq_cosetTerm u lam c (a : ℤ)
  rw [Int.cast_natCast] at h
  rw [← h]
  unfold cosetLevelTerm cosetGaussSum
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  ring

/-- The orthogonality identity (4.6): `Σ_{c ∣ N} A^{cos}_c(u, λ) = R_N(u, λ)`. -/
theorem sum_divisors_cosetGRCoeff (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ)
    {N : ℕ} (hN : N ≠ 0) :
    ∑ c ∈ N.divisors, L.cosetGRCoeff u lam c = (L.cosetResidueCount u lam N : ℂ) := by
  haveI : NeZero N := ⟨hN⟩
  classical
  unfold cosetGRCoeff
  rw [← sum_range_div_eq_sum_divisors N (L.cosetTerm u lam)]
  have hterm : ∀ j ∈ range N, L.cosetTerm u lam ((j : ℚ) / N) = L.cosetLevelTerm u lam N (j : ℤ) := by
    intro j _
    rw [L.cosetLevelTerm_eq_cosetTerm u lam N (j : ℤ), Int.cast_natCast]
  rw [Finset.sum_congr rfl hterm]
  unfold cosetLevelTerm
  rw [← Finset.mul_sum]
  simp_rw [Int.cast_natCast]
  rw [sum_range_natCast_eq_sum_zmod N (fun x ↦ ∑ z : Fin (n + 1) → ZMod N,
      ZMod.stdAddChar (x * ((lam : ZMod N) - L.zmodCosetPoly u N z))), Finset.sum_comm]
  have horth : ∀ z : Fin (n + 1) → ZMod N,
      ∑ x : ZMod N, ZMod.stdAddChar (x * ((lam : ZMod N) - L.zmodCosetPoly u N z)) =
        if L.zmodCosetPoly u N z = (lam : ZMod N) then (N : ℂ) else 0 := by
    intro z
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
    by_cases h : L.zmodCosetPoly u N z = (lam : ZMod N)
    · rw [if_pos (by rw [h, sub_self]), if_pos h]
    · rw [if_neg (fun h' ↦ h (sub_eq_zero.1 h').symm), if_neg h, Nat.cast_zero]
  rw [Finset.sum_congr rfl fun z _ ↦ horth z, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  unfold cosetResidueCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

/-! ## Level one, prime powers, multiplicativity -/

theorem cosetGRCoeff_one (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ) :
    L.cosetGRCoeff u lam 1 = 1 := by
  have h := L.sum_divisors_cosetGRCoeff u lam one_ne_zero
  rw [Nat.divisors_one, Finset.sum_singleton, L.cosetResidueCount_one] at h
  rw [h, Complex.ofReal_one]

theorem sum_range_cosetGRCoeff_primePow (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ)
    (lam : ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ i ∈ range (k + 1), L.cosetGRCoeff u lam (p ^ i) = (L.cosetResidueCount u lam (p ^ k) : ℂ) := by
  rw [← L.sum_divisors_cosetGRCoeff u lam (pow_ne_zero k hp.ne_zero), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  rfl

theorem cosetGRCoeff_primePow_succ (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    L.cosetGRCoeff u lam (p ^ (k + 1)) =
      (L.cosetResidueCount u lam (p ^ (k + 1)) : ℂ) - L.cosetResidueCount u lam (p ^ k) := by
  rw [← L.sum_range_cosetGRCoeff_primePow u lam hp (k + 1),
    ← L.sum_range_cosetGRCoeff_primePow u lam hp k, Finset.sum_range_succ]
  ring

/-- The coset counts as an arithmetic function. -/
def cosetResidueCountArith (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ) :
    ArithmeticFunction ℂ :=
  ⟨fun N ↦ if N = 0 then 0 else (L.cosetResidueCount u lam N : ℂ), by simp⟩

/-- The coset coefficients as an arithmetic function. -/
def cosetGRArith {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun c ↦ L.cosetGRCoeff u lam c, by simp [cosetGRCoeff]⟩

@[simp]
theorem cosetGRArith_apply {k : ℕ} (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (lam : ℤ) (c : ℕ) :
    L.cosetGRArith u lam c = L.cosetGRCoeff u lam c :=
  rfl

theorem isMultiplicative_cosetResidueCountArith (L : PositiveDefiniteIntegralLattice (n + 1))
    (u : Fin (n + 1) → ℤ) (lam : ℤ) : (L.cosetResidueCountArith u lam).IsMultiplicative := by
  refine ⟨?_, fun {m₁ m₂} h ↦ ?_⟩
  · simp [cosetResidueCountArith, L.cosetResidueCount_one]
  · simp only [cosetResidueCountArith, ArithmeticFunction.coe_mk, mul_eq_zero]
    by_cases h₁ : m₁ = 0
    · simp [h₁]
    by_cases h₂ : m₂ = 0
    · simp [h₂]
    rw [if_neg (by simp [h₁, h₂]), if_neg h₁, if_neg h₂,
      L.cosetResidueCount_mul_of_coprime u h lam, Complex.ofReal_mul]

theorem cosetGRArith_mul_zeta (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ) :
    L.cosetGRArith u lam * (ζ : ArithmeticFunction ℂ) = L.cosetResidueCountArith u lam := by
  ext N
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  simp only [cosetGRArith_apply, cosetResidueCountArith, ArithmeticFunction.coe_mk, if_neg hN.ne']
  exact L.sum_divisors_cosetGRCoeff u lam hN.ne'

/-- The coset coefficients are multiplicative (Möbius inversion `A^{cos} = R * μ`). -/
theorem isMultiplicative_cosetGRArith (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ)
    (lam : ℤ) : (L.cosetGRArith u lam).IsMultiplicative := by
  have h : L.cosetGRArith u lam = L.cosetResidueCountArith u lam * (μ : ArithmeticFunction ℂ) := by
    rw [← L.cosetGRArith_mul_zeta u lam, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius,
      mul_one]
  rw [h]
  exact (L.isMultiplicative_cosetResidueCountArith u lam).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

theorem cosetGRCoeff_mul_of_coprime (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ)
    {c₁ c₂ : ℕ} (h : c₁.Coprime c₂) :
    L.cosetGRCoeff u lam (c₁ * c₂) = L.cosetGRCoeff u lam c₁ * L.cosetGRCoeff u lam c₂ :=
  (L.isMultiplicative_cosetGRArith u lam).map_mul_of_coprime h

/-! ## Good primes: the standard coefficients at the fixed target -/

/-- At a prime `p ∤ D`, `A^{cos}_{p^k}(u, λ) = A_{p^k}(q(adj(S) u) + D² λ)`. -/
theorem cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient (L : PositiveDefiniteIntegralLattice (n + 1))
    (u : Fin (n + 1) → ℤ) (lam : ℤ) {p : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ L.polarGramMatrix.det.natAbs)
    (k : ℕ) :
    L.cosetGRCoeff u lam (p ^ k) =
      L.gaussRamanujanCoefficient (p ^ k) (L.cosetStandardTarget u lam) := by
  have hcop : ∀ j : ℕ, Nat.Coprime L.polarGramMatrix.det.natAbs (p ^ j) := fun j ↦
    Nat.Coprime.pow_right j ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpD))
  have hR : ∀ j : ℕ, L.cosetResidueCount u lam (p ^ j) =
      L.normalizedResidueCount (L.cosetStandardTarget u lam) (p ^ j) := fun j ↦ by
    haveI : NeZero (p ^ j) := ⟨pow_ne_zero j hp.ne_zero⟩
    exact L.cosetResidueCount_eq_normalizedResidueCount u lam (hcop j)
  rcases k with _ | k
  · rw [pow_zero, L.cosetGRCoeff_one, L.gaussRamanujanCoefficient_one]
  · rw [L.cosetGRCoeff_primePow_succ u lam hp k, L.gaussRamanujanCoefficient_primePow_succ hp _ k,
      hR, hR]

end PositiveDefiniteIntegralLattice
