import SMSFormula.RationalAdeleFiniteLocalResidueCount
import SMSFormula.RationalAdeleSingularSeriesEulerProduct
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Gauss--Ramanujan coefficients and the residue-count orthogonality

For the standard finite quadratic Gauss integral `G(r) = ∫_{Ẑ^n} ψ_f(r Q(x)) dx` of an integral
lattice, the grouped coefficient of the rank-four Hecke route is

`A_q(M) = Σ*_{a mod q} G(a/q) e(M a/q)`   (`a` coprime to `q`, `e(x) = exp(2πix)`).

This file proves, in every rank, the finite character-orthogonality identity (3.7):

`Σ_{q ∣ N} A_q(M) = N^{-(n-1)} #{z mod N : Q(z) ≡ M}`,

i.e. the divisor sums of the coefficients are exactly the normalized residue counts
(`normalizedResidueCount`).  Three ingredients:

* the regrouping of `j/N` (`0 ≤ j < N`) by reduced denominator (`sum_range_div_eq_sum_divisors`);
* the Gauss integral at `j/N` as a level-`N` character sum
  (`rationalFiniteAdeleQuadraticGaussIntegral_intDiv_eq_levelSum`): the phase is periodic
  modulo `N Ẑ^n`, the section-free quotient averaging applies, and the residue model
  reindexes;
* orthogonality of the primitive character of `ZMod N` (Mathlib `AddChar.sum_mulShift`).

The sign convention is the repository's: `ψ_f(s) = e(s)⁻¹` on rationals, so `G(j/N)` is the sum of
`e(-j Q(z)/N)`, paired with `e(+M j/N)`.  No convergence, no bound and no Euler product is asserted
here; this is the finite identity only.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace PositiveDefiniteIntegralLattice

/-! ## Regrouping `j/N` by reduced denominator -/

/-- Regrouping by reduced denominator: `Σ_{0 ≤ j < N} f(j/N) = Σ_{q ∣ N} Σ*_{a mod q} f(a/q)`. -/
theorem sum_range_div_eq_sum_divisors {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℚ → M) :
    ∑ j ∈ range N, f ((j : ℚ) / N) =
      ∑ q ∈ N.divisors, ∑ a ∈ (range q).filter (fun a ↦ q.Coprime a), f ((a : ℚ) / q) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  rw [← Nat.sum_div_divisors N
      (fun q ↦ ∑ a ∈ (range q).filter (fun a ↦ q.Coprime a), f ((a : ℚ) / q)),
    ← Finset.sum_fiberwise_of_maps_to (s := range N) (t := N.divisors) (g := fun j ↦ N.gcd j)
      (fun j _ ↦ Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hN.ne'⟩)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨hdN, -⟩ := Nat.mem_divisors.1 hd
  obtain ⟨q, hq⟩ := hdN
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨q, hq⟩ hN
  have hNd : N / d = q := by rw [hq, Nat.mul_div_cancel_left _ hd0]
  rw [hNd]
  symm
  refine Finset.sum_nbij' (fun a ↦ d * a) (fun j ↦ j / d) (fun a ha ↦ ?_) (fun j hj ↦ ?_)
    (fun a _ ↦ ?_) (fun j hj ↦ ?_) (fun a ha ↦ ?_)
  · simp only [mem_filter, mem_range] at ha ⊢
    refine ⟨?_, ?_⟩
    · rw [hq]
      exact Nat.mul_lt_mul_of_pos_left ha.1 hd0
    · rw [hq, Nat.gcd_mul_left, ha.2, mul_one]
  · simp only [mem_filter, mem_range] at hj ⊢
    obtain ⟨hjN, hjg⟩ := hj
    have hdj : d ∣ j := hjg ▸ Nat.gcd_dvd_right N j
    obtain ⟨b, rfl⟩ := hdj
    rw [Nat.mul_div_cancel_left _ hd0]
    refine ⟨?_, ?_⟩
    · rw [hq] at hjN
      exact (Nat.mul_lt_mul_left hd0).1 hjN
    · rw [hq, Nat.gcd_mul_left] at hjg
      exact (Nat.mul_eq_left hd0.ne').1 hjg
  · exact Nat.mul_div_cancel_left _ hd0
  · simp only [mem_filter, mem_range] at hj
    have hdj : d ∣ j := hj.2 ▸ Nat.gcd_dvd_right N j
    exact Nat.mul_div_cancel' hdj
  · congr 1
    have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [hq]
    push_cast
    field_simp

/-- The sum over `0 ≤ j < N` of a function of the residue `j mod N` is the sum over `ZMod N`. -/
theorem sum_range_natCast_eq_sum_zmod {M : Type*} [AddCommMonoid M] (N : ℕ) [NeZero N]
    (g : ZMod N → M) :
    ∑ j ∈ range N, g (j : ZMod N) = ∑ x : ZMod N, g x := by
  refine Finset.sum_nbij' (fun j ↦ (j : ZMod N)) (fun x ↦ x.val) (fun _ _ ↦ mem_univ _)
    (fun x _ ↦ mem_range.2 (ZMod.val_lt x)) (fun j hj ↦ ZMod.val_cast_of_lt (mem_range.1 hj))
    (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)

/-! ## Characters at rational points of level `N` -/

/-- `e(k/N) = stdAddChar(k mod N)` for an integer `k`. -/
theorem fourierChar_intDiv_eq_stdAddChar (N : ℕ) [NeZero N] (k : ℤ) :
    ((Real.fourierChar (((k : ℚ) / N : ℚ) : ℝ) : Circle) : ℂ) = ZMod.stdAddChar (k : ZMod N) := by
  rw [ZMod.stdAddChar_coe, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- `e(k/N)⁻¹ = stdAddChar(-(k mod N))` for an integer `k`. -/
theorem fourierChar_intDiv_inv_eq_stdAddChar (N : ℕ) [NeZero N] (k : ℤ) :
    (((Real.fourierChar (((k : ℚ) / N : ℚ) : ℝ))⁻¹ : Circle) : ℂ) =
      ZMod.stdAddChar (-(k : ZMod N)) := by
  rw [← AddChar.map_neg_eq_inv, ← Int.cast_neg, ← fourierChar_intDiv_eq_stdAddChar N (-k)]
  congr 3
  push_cast
  ring

/-! ## The Gauss integral at `j/N` as a level-`N` character sum -/

variable {n : ℕ}

/-- The integral quadratic phase at `j/N` is periodic modulo `N Ẑ^n`. -/
theorem rationalFiniteAdeleIntegralQuadraticPhase_intDiv_add_dilation (L : PositiveDefiniteIntegralLattice n)
    (N : ℕ) (j : ℤ) (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n N).range) :
    rationalFiniteAdeleIntegralQuadraticPhase L ((j : ℚ) / N) (x + z) =
      rationalFiniteAdeleIntegralQuadraticPhase L ((j : ℚ) / N) x := by
  refine rationalFiniteAdeleIntegralQuadraticPhase_add_denDilation L _ x z ?_
  set D := (((j : ℚ) / N : ℚ)).den with hD
  have hden : (D : ℤ) ∣ (N : ℤ) := by
    have h := Rat.den_dvd j N
    rwa [Rat.divInt_eq_div, Int.cast_natCast] at h
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.1 hden
  obtain ⟨w, rfl⟩ := hz
  refine ⟨integralFiniteAdeleCoordinateNatDilation n k w, ?_⟩
  funext i
  apply Subtype.ext
  simp only [integralFiniteAdeleCoordinateNatDilation, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    integralFiniteAdeleNatDilation_apply, smul_smul]
  congr 1
  rw [hk]

/-- The integral phase at an integer vector is `e(t Q(z))⁻¹`. -/
theorem rationalFiniteAdeleIntegralQuadraticPhase_integerVector (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (z : Fin n → ℤ) :
    rationalFiniteAdeleIntegralQuadraticPhase L t (integerToIntegralFiniteAdeleVector n z) =
      (((Real.fourierChar ((t * ((L.quadForm z : ℤ) : ℚ) : ℚ) : ℝ))⁻¹ : Circle) : ℂ) := by
  unfold rationalFiniteAdeleIntegralQuadraticPhase
    RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase
  have hcoe : (fun i => ((integerToIntegralFiniteAdeleVector n z i : IntegralFiniteAdele) :
      RationalFiniteAdele)) =
      fun i => algebraMap ℚ RationalFiniteAdele ((z i : ℤ) : ℚ) := by
    funext i
    rfl
  rw [hcoe, L.finiteAdelicQuadraticFormValue_intVector z, ← map_mul,
    rationalFiniteAdeleFourierChar_algebraMap]

set_option maxHeartbeats 2000000 in
/-- The Gauss integral at `j/N` as a level-`N` character sum:
`G(j/N) = N^{-n} Σ_{z mod N} e(-j Q(z)/N)`. -/
theorem rationalFiniteAdeleQuadraticGaussIntegral_intDiv_eq_levelSum (L : PositiveDefiniteIntegralLattice n)
    (N : ℕ) [NeZero N] (j : ℤ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((j : ℚ) / N) =
      (((N : ℝ) ^ n : ℂ))⁻¹ *
        ∑ z : Fin n → ZMod N, ZMod.stdAddChar (-((j : ZMod N) * L.zmodQuadForm N z)) := by
  have hN : N ≠ 0 := NeZero.ne N
  classical
  rw [rationalFiniteAdeleQuadraticGaussIntegral_eq_integralQuadraticPhase,
    integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum n N
      (rationalFiniteAdeleIntegralQuadraticPhase L ((j : ℚ) / N))
      (L.rationalFiniteAdeleIntegralQuadraticPhase_intDiv_add_dilation N j)]
  congr 1
  rw [← Equiv.sum_comp (coordinateResidueEquivIntegralFiniteAdeleModDilation n N hN).toEquiv]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hrep : (fun i => (((((z i).val : ℕ) : ℤ)) : ZMod N)) = z := by
    funext i
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  set zi : Fin n → ℤ := fun i ↦ (((z i).val : ℕ) : ℤ) with hzi
  rw [← hrep]
  change addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n N).range _ _
      (coordinateResidueEquivIntegralFiniteAdeleModDilation n N hN (fun i ↦ ((zi i : ℤ) : ZMod N))) =
    ZMod.stdAddChar (-((j : ZMod N) * L.zmodQuadForm N (fun i ↦ ((zi i : ℤ) : ZMod N))))
  rw [coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast,
    addQuotientPeriodicLift_coe]
  change rationalFiniteAdeleIntegralQuadraticPhase L ((j : ℚ) / N)
      (integerToIntegralFiniteAdeleVector n zi) = _
  rw [rationalFiniteAdeleIntegralQuadraticPhase_integerVector, zmodQuadForm_intCast,
    ← Int.cast_mul, show ((j : ℚ) / N * ((L.quadForm zi : ℤ) : ℚ)) =
      (((j * L.quadForm zi : ℤ) : ℚ) / N) by push_cast; ring,
    fourierChar_intDiv_inv_eq_stdAddChar]

/-! ## Gauss--Ramanujan coefficients and the orthogonality identity (3.7) -/

/-- The summand `r ↦ G(r) e(M r)` of the Gauss--Ramanujan coefficients. -/
def gaussRamanujanTerm (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (r : ℚ) : ℂ :=
  L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r *
    ((Real.fourierChar (((M : ℚ) * r : ℚ) : ℝ) : Circle) : ℂ)

/-- The Gauss--RAMANUJAN coefficient `A_q(M) = Σ*_{a mod q} G(a/q) e(M a/q)`. -/
def gaussRamanujanCoefficient (L : PositiveDefiniteIntegralLattice n) (q : ℕ) (M : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a ↦ q.Coprime a), L.gaussRamanujanTerm M ((a : ℚ) / q)

/-- At `r = j/N` the summand is a level-`N` character sum. -/
theorem gaussRamanujanTerm_intDiv (L : PositiveDefiniteIntegralLattice n) (N : ℕ) [NeZero N] (M j : ℤ) :
    L.gaussRamanujanTerm M ((j : ℚ) / N) =
      (((N : ℝ) ^ n : ℂ))⁻¹ *
        ∑ z : Fin n → ZMod N, ZMod.stdAddChar ((j : ZMod N) * ((M : ZMod N) - L.zmodQuadForm N z)) := by
  rw [gaussRamanujanTerm, L.rationalFiniteAdeleQuadraticGaussIntegral_intDiv_eq_levelSum N j,
    show ((M : ℚ) * ((j : ℚ) / N)) = (((M * j : ℤ) : ℚ) / N) by push_cast; ring,
    fourierChar_intDiv_eq_stdAddChar, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  ring

/-- The orthogonality identity (3.7), in every rank: the divisor sums of the Gauss--Ramanujan
coefficients are the normalized residue counts,
`Σ_{q ∣ N} A_q(M) = N^{-n} #{z ∈ (ℤ/N)^{n+1} : Q(z) ≡ M}`. -/
theorem sum_divisors_gaussRamanujanCoefficient (L : PositiveDefiniteIntegralLattice (n + 1)) {N : ℕ} (hN : N ≠ 0)
    (M : ℤ) :
    ∑ q ∈ N.divisors, L.gaussRamanujanCoefficient q M = (L.normalizedResidueCount M N : ℂ) := by
  haveI : NeZero N := ⟨hN⟩
  classical
  unfold gaussRamanujanCoefficient
  rw [← sum_range_div_eq_sum_divisors N (L.gaussRamanujanTerm M)]
  have hterm : ∀ j ∈ range N, L.gaussRamanujanTerm M ((j : ℚ) / N) =
      (((N : ℝ) ^ (n + 1) : ℂ))⁻¹ *
        ∑ z : Fin (n + 1) → ZMod N,
          ZMod.stdAddChar (((j : ℕ) : ZMod N) * ((M : ZMod N) - L.zmodQuadForm N z)) := by
    intro j _
    have h := L.gaussRamanujanTerm_intDiv N M (j : ℤ)
    simp only [Int.cast_natCast] at h
    exact h
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_range_natCast_eq_sum_zmod N (fun x ↦ ∑ z : Fin (n + 1) → ZMod N,
      ZMod.stdAddChar (x * ((M : ZMod N) - L.zmodQuadForm N z))),
    Finset.sum_comm]
  have horth : ∀ z : Fin (n + 1) → ZMod N,
      ∑ x : ZMod N, ZMod.stdAddChar (x * ((M : ZMod N) - L.zmodQuadForm N z)) =
        if L.zmodQuadForm N z = (M : ZMod N) then (N : ℂ) else 0 := by
    intro z
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
    by_cases h : L.zmodQuadForm N z = (M : ZMod N)
    · rw [if_pos (by rw [h, sub_self]), if_pos h]
    · rw [if_neg (fun h' ↦ h (sub_eq_zero.1 h').symm), if_neg h, Nat.cast_zero]
  rw [Finset.sum_congr rfl fun z _ ↦ horth z, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  unfold normalizedResidueCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

/-! ## Level one, prime powers and multiplicativity -/

/-- The normalized residue count at level one is one. -/
theorem normalizedResidueCount_one (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    L.normalizedResidueCount M 1 = 1 := by
  unfold normalizedResidueCount
  rw [L.card_residueSet_one M]
  simp

/-- `A_1(M) = 1`. -/
theorem gaussRamanujanCoefficient_one (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    L.gaussRamanujanCoefficient 1 M = 1 := by
  have h := L.sum_divisors_gaussRamanujanCoefficient one_ne_zero M
  rw [Nat.divisors_one, Finset.sum_singleton, L.normalizedResidueCount_one] at h
  rw [h, Complex.ofReal_one]

/-- The prime-power divisor sums: `Σ_{i ≤ k} A_{p^i}(M) = r_{p^k}(M)`. -/
theorem sum_range_gaussRamanujanCoefficient_primePow (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ}
    (hp : p.Prime) (M : ℤ) (k : ℕ) :
    ∑ i ∈ range (k + 1), L.gaussRamanujanCoefficient (p ^ i) M =
      (L.normalizedResidueCount M (p ^ k) : ℂ) := by
  rw [← L.sum_divisors_gaussRamanujanCoefficient (pow_ne_zero k hp.ne_zero) M,
    Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

/-- The prime-power coefficient is a difference of residue counts:
`A_{p^{k+1}}(M) = r_{p^{k+1}}(M) - r_{p^k}(M)`. -/
theorem gaussRamanujanCoefficient_primePow_succ (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ}
    (hp : p.Prime) (M : ℤ) (k : ℕ) :
    L.gaussRamanujanCoefficient (p ^ (k + 1)) M =
      (L.normalizedResidueCount M (p ^ (k + 1)) : ℂ) - L.normalizedResidueCount M (p ^ k) := by
  rw [← L.sum_range_gaussRamanujanCoefficient_primePow hp M (k + 1),
    ← L.sum_range_gaussRamanujanCoefficient_primePow hp M k, Finset.sum_range_succ]
  ring

/-- The normalized residue count is multiplicative over coprime levels. -/
theorem normalizedResidueCount_mul_of_coprime (L : PositiveDefiniteIntegralLattice (n + 1)) {m₁ m₂ : ℕ}
    (h : m₁.Coprime m₂) (M : ℤ) :
    L.normalizedResidueCount M (m₁ * m₂) =
      L.normalizedResidueCount M m₁ * L.normalizedResidueCount M m₂ := by
  unfold normalizedResidueCount
  rw [L.card_residueSet_mul_of_coprime h M]
  push_cast
  rw [mul_pow, mul_inv]
  ring

/-- The normalized residue counts as an arithmetic function (zero at `0`). -/
def normalizedResidueCountArith (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    ArithmeticFunction ℂ :=
  ⟨fun N ↦ if N = 0 then 0 else (L.normalizedResidueCount M N : ℂ), by simp⟩

/-- The Gauss--Ramanujan coefficients as an arithmetic function (`A_0 = 0`: empty sum). -/
def gaussRamanujanArith (L : PositiveDefiniteIntegralLattice n) (M : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun q ↦ L.gaussRamanujanCoefficient q M, by simp [gaussRamanujanCoefficient]⟩

@[simp]
theorem gaussRamanujanArith_apply (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (q : ℕ) :
    L.gaussRamanujanArith M q = L.gaussRamanujanCoefficient q M :=
  rfl

theorem isMultiplicative_normalizedResidueCountArith (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    (L.normalizedResidueCountArith M).IsMultiplicative := by
  refine ⟨?_, fun {m₁ m₂} h ↦ ?_⟩
  · simp [normalizedResidueCountArith, L.normalizedResidueCount_one]
  · simp only [normalizedResidueCountArith, ArithmeticFunction.coe_mk, mul_eq_zero]
    by_cases h₁ : m₁ = 0
    · simp [h₁]
    by_cases h₂ : m₂ = 0
    · simp [h₂]
    rw [if_neg (by simp [h₁, h₂]), if_neg h₁, if_neg h₂,
      L.normalizedResidueCount_mul_of_coprime h M, Complex.ofReal_mul]

/-- (3.7) as a Dirichlet convolution: `A * ζ = r`. -/
theorem gaussRamanujanArith_mul_zeta (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    L.gaussRamanujanArith M * (ζ : ArithmeticFunction ℂ) = L.normalizedResidueCountArith M := by
  ext N
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  simp only [gaussRamanujanArith_apply, normalizedResidueCountArith, ArithmeticFunction.coe_mk,
    if_neg hN.ne']
  exact L.sum_divisors_gaussRamanujanCoefficient hN.ne' M

/-- MÖBIUS inversion: `A = r * μ`. -/
theorem gaussRamanujanArith_eq_mul_moebius (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    L.gaussRamanujanArith M = L.normalizedResidueCountArith M * (μ : ArithmeticFunction ℂ) := by
  rw [← L.gaussRamanujanArith_mul_zeta M, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius,
    mul_one]

/-- The Gauss--RAMANUJAN coefficients are multiplicative in `q`. -/
theorem isMultiplicative_gaussRamanujanArith (L : PositiveDefiniteIntegralLattice (n + 1)) (M : ℤ) :
    (L.gaussRamanujanArith M).IsMultiplicative := by
  rw [L.gaussRamanujanArith_eq_mul_moebius M]
  exact (L.isMultiplicative_normalizedResidueCountArith M).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

/-- `A_{q₁ q₂}(M) = A_{q₁}(M) A_{q₂}(M)` for coprime `q₁, q₂`. -/
theorem gaussRamanujanCoefficient_mul_of_coprime (L : PositiveDefiniteIntegralLattice (n + 1)) {q₁ q₂ : ℕ}
    (h : q₁.Coprime q₂) (M : ℤ) :
    L.gaussRamanujanCoefficient (q₁ * q₂) M =
      L.gaussRamanujanCoefficient q₁ M * L.gaussRamanujanCoefficient q₂ M :=
  (L.isMultiplicative_gaussRamanujanArith M).map_mul_of_coprime h

end PositiveDefiniteIntegralLattice
