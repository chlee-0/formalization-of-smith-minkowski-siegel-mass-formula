import SMSFormula.RationalAdeleGaussRamanujanCoefficient
import SMSFormula.RationalFiniteAdeleQuadraticGaussDenominatorDecay
import SMSFormula.RationalAdeleSingularSeriesLocalDensity
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The grouped Gauss--Ramanujan estimate in rank at least four

The individual Gauss values are not absolutely summable in rank four (`Σ φ(q) q^{-2}` diverges), so
the rank-five Bruhat interchange fails.  After grouping the unit numerators at each denominator,
the coefficients `A_q(M) = Σ*_{a mod q} G(a/q) e(M a/q)` are absolutely summable for `M ≠ 0`, with a
bound polynomial in `|M|`:

`Σ_q ‖A_q(M)‖ ≤ K · |M|^c`   (rank `≥ 4`, `M ≠ 0`, constants depending only on the lattice).

Ingredients, all except the assembly:

* `A` is multiplicative (`gaussRamanujanCoefficient_mul_of_coprime`), so its norm is too;
* the denominator decay `‖G(t)‖ ≤ √gcd(den t, polarDeterminant)ⁿ · √den tⁿ⁻¹`, so
  `‖A_q(M)‖ ≤ D · φ(q)/q²` with `D = √discⁿ` in rank `n ≥ 4`;
* at an odd prime `p ∤ M` the level stability gives `A_{p^k}(M) = 0` for `k ≥ 2`, and if also
  `p ∤ det` the finite-field count gives `‖A_p(M)‖ ≤ 1/p²`;
* Mathlib's Euler product over smooth numbers bounds the partial sums by the product of the local
  sums, which is at most `e² · ∏_{p ∣ 2 M det} p^c ≤ e² (2 |M| |det|)^c`.

No Euler-product value is asserted here beyond the finite smooth-number products; the identification
`Σ_q A_q(M) = ∏'_p δ_p(M)` is a separate step.  Nothing is chosen.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The general termwise bound -/

theorem den_natCast_div_of_coprime {q a : ℕ} (hq : 0 < q) (h : q.Coprime a) :
    ((a : ℚ) / q).den = q := by
  have h' : Nat.Coprime (a : ℤ).natAbs (q : ℤ).natAbs := by
    simpa [Int.natAbs_natCast] using h.symm
  have := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (q : ℤ)) (by exact_mod_cast hq) h'
  exact_mod_cast (by simpa using this)

/-- In rank at least four, `‖G(a/q)‖ ≤ √discⁿ / q²` for `a` coprime to `q`. -/
theorem norm_gaussIntegral_coprime_le (L : PositiveDefiniteIntegralLattice n) (hn : 4 ≤ n) {q a : ℕ} (hq : 0 < q)
    (h : q.Coprime a) :
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((a : ℚ) / q)‖ ≤
      Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n / (q : ℝ) ^ 2 := by
  have hb := L.norm_quadraticGaussIntegral_le_polarDeterminant_sqrt_pow_mul_inv_den_sqrt_pow ((a : ℚ) / q)
  rw [den_natCast_div_of_coprime hq h] at hb
  refine hb.trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hq1 : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hq
  have hsq : Real.sqrt (q : ℝ) ^ 4 = (q : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [inv_pow, ← hsq]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq1 hn)

/-- The general termwise bound in rank at least four: `‖A_q(M)‖ ≤ √discⁿ · φ(q) / q²`. -/
theorem norm_gaussRamanujanCoefficient_le (L : PositiveDefiniteIntegralLattice n) (hn : 4 ≤ n) {q : ℕ}
    (hq : 0 < q) (M : ℤ) :
    ‖L.gaussRamanujanCoefficient q M‖ ≤
      Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n * (q.totient : ℝ) / (q : ℝ) ^ 2 := by
  unfold gaussRamanujanCoefficient gaussRamanujanTerm
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a ∈ (range q).filter (fun a ↦ q.Coprime a),
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((a : ℚ) / q) *
          ((Real.fourierChar (((M : ℚ) * ((a : ℚ) / q) : ℚ) : ℝ) : Circle) : ℂ)‖ ≤
        Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n / (q : ℝ) ^ 2 := by
    intro a ha
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact L.norm_gaussIntegral_coprime_le hn hq (mem_filter.1 ha).2
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]
  ring_nf
  rfl

/-- At a prime power: `‖A_{p^k}(M)‖ ≤ √discⁿ / p^k`. -/
theorem norm_gaussRamanujanCoefficient_primePow_le (L : PositiveDefiniteIntegralLattice n) (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (M : ℤ) (k : ℕ) :
    ‖L.gaussRamanujanCoefficient (p ^ k) M‖ ≤ Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n / (p : ℝ) ^ k := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  refine (L.norm_gaussRamanujanCoefficient_le hn hpk M).trans ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htot : ((p ^ k).totient : ℝ) ≤ (p : ℝ) ^ k := by
    exact_mod_cast Nat.totient_le (p ^ k)
  rw [Nat.cast_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hD : 0 ≤ Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n := by positivity
  calc Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n * ((p ^ k).totient : ℝ) * (p : ℝ) ^ k
      ≤ Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n * (p : ℝ) ^ k * (p : ℝ) ^ k := by
        gcongr
    _ = Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ n * ((p : ℝ) ^ k) ^ 2 := by ring

/-! ## Odd primes not dividing `M` -/

/-- At an odd prime `p ∤ M`, `A_{p^k}(M) = 0` for `k ≥ 2` (level stability). -/
theorem gaussRamanujanCoefficient_primePow_eq_zero (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) {k : ℕ} (hk : 2 ≤ k) :
    L.gaussRamanujanCoefficient (p ^ k) M = 0 := by
  haveI := Fact.mk hp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 = (j + 1) + 1 from rfl, L.gaussRamanujanCoefficient_primePow_succ hp M (j + 1),
    L.normalizedResidueCount_primePow_eq hp2 hM (by omega : 1 ≤ j + 1 + 1),
    L.normalizedResidueCount_primePow_eq hp2 hM (by omega : 1 ≤ j + 1), sub_self]

/-- At an odd prime `p ∤ M det` in rank at least four, `‖A_p(M)‖ ≤ 1/p²` (finite-field count). -/
theorem norm_gaussRamanujanCoefficient_prime_le (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M)
    (hdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det) :
    ‖L.gaussRamanujanCoefficient p M‖ ≤ 1 / (p : ℝ) ^ 2 := by
  haveI := Fact.mk hp
  have h := L.gaussRamanujanCoefficient_primePow_succ hp M 0
  rw [zero_add, pow_one, pow_zero, L.normalizedResidueCount_one] at h
  rw [h, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have := L.abs_normalizedResidueCount_prime_sub_one_le_of_three_le hn hp2 hM hdet
  rwa [pow_one] at this

/-! ## The local sums -/

/-- Every prime-power series is dominated by `(1 + √discⁿ) (1/2)^k`. -/
theorem norm_gaussRamanujanCoefficient_primePow_le_geometric (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (M : ℤ) (k : ℕ) :
    ‖L.gaussRamanujanCoefficient (p ^ k) M‖ ≤
      (1 + Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1)) * (1 / 2 : ℝ) ^ k := by
  have hD : 0 ≤ Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1) := by positivity
  refine (L.norm_gaussRamanujanCoefficient_primePow_le (by omega) hp M k).trans ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [div_eq_mul_inv, one_div, inv_pow]
  have h1 : ((p : ℝ) ^ k)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 k)
  calc Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1) * ((p : ℝ) ^ k)⁻¹
      ≤ Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1) * ((2 : ℝ) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hD
    _ ≤ (1 + Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1)) * ((2 : ℝ) ^ k)⁻¹ := by
        gcongr
        linarith

theorem summable_norm_gaussRamanujanCoefficient_primePow (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (M : ℤ) :
    Summable fun k : ℕ ↦ ‖L.gaussRamanujanCoefficient (p ^ k) M‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (L.norm_gaussRamanujanCoefficient_primePow_le_geometric hn hp M)
    ((summable_geometric_two).mul_left _)

/-- Every local sum is at most `2 (1 + √discⁿ)`. -/
theorem tsum_norm_gaussRamanujanCoefficient_primePow_le (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (M : ℤ) :
    ∑' k : ℕ, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ ≤
      2 * (1 + Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1)) := by
  refine (Summable.tsum_le_tsum (L.norm_gaussRamanujanCoefficient_primePow_le_geometric hn hp M)
    (L.summable_norm_gaussRamanujanCoefficient_primePow hn hp M)
    ((summable_geometric_two).mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_two]
  ring

/-- At an odd prime `p ∤ M det` in rank at least four the local sum is `≤ 1 + 1/p²`. -/
theorem tsum_norm_gaussRamanujanCoefficient_primePow_le_good (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M)
    (hdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det) :
    ∑' k : ℕ, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ ≤ 1 + 1 / (p : ℝ) ^ 2 := by
  have hsupp : ∀ k ∉ range 2, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ = 0 := by
    intro k hk
    rw [mem_range, not_lt] at hk
    rw [L.gaussRamanujanCoefficient_primePow_eq_zero hp hp2 hM hk, norm_zero]
  rw [tsum_eq_sum hsupp, sum_range_succ, sum_range_one, pow_zero, pow_one,
    L.gaussRamanujanCoefficient_one, norm_one]
  gcongr
  exact L.norm_gaussRamanujanCoefficient_prime_le hn hp hp2 hM hdet

/-! ## The Euler-product assembly -/

/-- Partial sums are bounded by the local product (Mathlib's smooth-number Euler product applied to
the multiplicative function `q ↦ ‖A_q(M)‖`). -/
theorem sum_range_norm_gaussRamanujanCoefficient_le_prod (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) (M : ℤ) (N : ℕ) :
    ∑ q ∈ range N, ‖L.gaussRamanujanCoefficient q M‖ ≤
      ∏ p ∈ N.primesBelow, ∑' k : ℕ, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ := by
  classical
  set f : ℕ → ℝ := fun q ↦ ‖L.gaussRamanujanCoefficient q M‖ with hf
  have hf₁ : f 1 = 1 := by simp [hf, L.gaussRamanujanCoefficient_one]
  have hmul : ∀ {a b : ℕ}, a.Coprime b → f (a * b) = f a * f b := fun h ↦ by
    simp only [hf, L.gaussRamanujanCoefficient_mul_of_coprime h M, norm_mul]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖f (p ^ k)‖) := fun hp ↦ by
    simpa [hf] using L.summable_norm_gaussRamanujanCoefficient_primePow hn hp M
  obtain ⟨-, hHas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul hsum N
  have hf0 : f 0 = 0 := by simp [hf, gaussRamanujanCoefficient]
  have hsplit : ∑ q ∈ range N, f q = ∑ q ∈ (range N).subtype (· ∈ N.smoothNumbers), f q := by
    rw [Finset.sum_subtype_eq_sum_filter]
    symm
    refine Finset.sum_filter_of_ne fun q hq hne ↦ ?_
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h ↦ hne (by rw [h, hf0])
    exact Nat.mem_smoothNumbers_of_lt hq0 (mem_range.1 hq)
  change ∑ q ∈ range N, f q ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p ^ k)
  rw [hsplit]
  exact sum_le_hasSum _ (fun _ _ ↦ norm_nonneg _) hHas

/-- The local product is polynomial in `M`: for `2 (1 + √discⁿ) ≤ 2^c`,
`∏_{p < N} Σ_k ‖A_{p^k}(M)‖ ≤ e² · (2 |M| |det|)^c`. -/
theorem prod_primesBelow_tsum_norm_gaussRamanujanCoefficient_le (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {c : ℕ}
    (hc : 2 * (1 + Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1)) ≤ 2 ^ c) (N : ℕ) :
    ∏ p ∈ N.primesBelow, ∑' k : ℕ, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ ≤
      Real.exp 2 * ((2 * M.natAbs * L.pairingMatrix.det.natAbs : ℕ) : ℝ) ^ c := by
  classical
  set X : ℕ := 2 * M.natAbs * L.pairingMatrix.det.natAbs with hXdef
  have hX : X ≠ 0 := by
    rw [hXdef]
    have := L.pairingMatrix_det_ne_zero
    positivity
  set S : ℕ → ℝ := fun p ↦ ∑' k : ℕ, ‖L.gaussRamanujanCoefficient (p ^ k) M‖ with hSdef
  have hS0 : ∀ p, 0 ≤ S p := fun p ↦ tsum_nonneg fun _ ↦ norm_nonneg _
  change ∏ p ∈ N.primesBelow, S p ≤ _
  rw [← Finset.prod_filter_mul_prod_filter_not N.primesBelow (· ∣ X), mul_comm (Real.exp 2)]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun p _ ↦ hS0 p) (by positivity)
  · -- the primes dividing `2 M det`
    have hle : ∀ p ∈ N.primesBelow.filter (· ∣ X), S p ≤ (p : ℝ) ^ c := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow (mem_filter.1 hp).1
      refine (L.tsum_norm_gaussRamanujanCoefficient_primePow_le hn hpp M).trans (hc.trans ?_)
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hpp.two_le) c
    refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
    rw [Finset.prod_pow]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _) ?_ c
    have hsub : N.primesBelow.filter (· ∣ X) ⊆ X.primeFactors := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primesBelow hp1, hp2, hX⟩
    have hprod : ∏ p ∈ N.primesBelow.filter (· ∣ X), p ≤ X :=
      (Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ ↦
        (Nat.prime_of_mem_primeFactors hp).one_lt.le).trans
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hX) (Nat.prod_primeFactors_dvd X))
    have hcast := (Nat.cast_le (α := ℝ)).2 hprod
    rwa [Nat.cast_prod] at hcast
  · -- the remaining primes: odd, prime to `M det`
    have hle : ∀ p ∈ N.primesBelow.filter (fun p ↦ ¬ p ∣ X),
        S p ≤ Real.exp (1 / (p : ℝ) ^ 2) := by
      intro p hp
      obtain ⟨hp1, hpX⟩ := mem_filter.1 hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp1
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hpX (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl 2) _) _)
      have hpM : ¬ (p : ℤ) ∣ M := fun h ↦ hpX
        (Dvd.dvd.mul_right (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _) _)
      have hpdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det := fun h ↦ hpX
        (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
      refine (L.tsum_norm_gaussRamanujanCoefficient_primePow_le_good hn hpp hp2 hpM hpdet).trans ?_
      have := Real.add_one_le_exp (1 / (p : ℝ) ^ 2)
      linarith
    refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.2 ?_
    have hsub : N.primesBelow.filter (fun p ↦ ¬ p ∣ X) ⊆ Ioo 0 N := by
      intro p hp
      have hp1 := (mem_filter.1 hp).1
      exact mem_Ioo.2 ⟨(Nat.prime_of_mem_primesBelow hp1).pos, Nat.lt_of_mem_primesBelow hp1⟩
    calc ∑ p ∈ N.primesBelow.filter (fun p ↦ ¬ p ∣ X), 1 / (p : ℝ) ^ 2
        ≤ ∑ i ∈ Ioo 0 N, ((i : ℝ) ^ 2)⁻¹ := by
          simp_rw [one_div]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 N
      _ = 2 := by norm_num

/-- The grouped Gauss--RAMANUJAN estimate in rank at least four: there are
constants `K > 0`, `c` (depending only on the lattice) with
`Σ_q ‖A_q(M)‖ < ∞` and `Σ_q ‖A_q(M)‖ ≤ K |M|^c` for every nonzero integer `M`. -/
theorem exists_summable_norm_gaussRamanujanCoefficient_le (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) :
    ∃ (K : ℝ) (c : ℕ), 0 < K ∧ ∀ M : ℤ, M ≠ 0 →
      Summable (fun q ↦ ‖L.gaussRamanujanCoefficient q M‖) ∧
        ∑' q, ‖L.gaussRamanujanCoefficient q M‖ ≤ K * (M.natAbs : ℝ) ^ c := by
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (2 * (1 + Real.sqrt (L.polarDeterminant.natAbs : ℝ) ^ (n + 1)))
    (by norm_num : (1 : ℝ) < 2)
  have hdet : L.pairingMatrix.det.natAbs ≠ 0 := Int.natAbs_ne_zero.2 L.pairingMatrix_det_ne_zero
  refine ⟨Real.exp 2 * ((2 * L.pairingMatrix.det.natAbs : ℕ) : ℝ) ^ c, c, by positivity,
    fun M hM ↦ ?_⟩
  have hbound : ∀ N, ∑ q ∈ range N, ‖L.gaussRamanujanCoefficient q M‖ ≤
      Real.exp 2 * ((2 * L.pairingMatrix.det.natAbs : ℕ) : ℝ) ^ c * (M.natAbs : ℝ) ^ c := by
    intro N
    refine (L.sum_range_norm_gaussRamanujanCoefficient_le_prod hn M N).trans
      ((L.prod_primesBelow_tsum_norm_gaussRamanujanCoefficient_le hn hM hc.le N).trans
        (le_of_eq ?_))
    push_cast
    ring
  exact ⟨summable_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound⟩

/-! ## The singular series as the sum of the grouped coefficients -/

/-- The singular series is the sum of the grouped coefficients: in rank at least four, for `M ≠ 0`,
`Σ_q A_q(M) = ∏'_p δ_p(M)` (absolutely convergent).  The divisor sums at `k!` are the residue
counts by (3.7), which converge to the singular series. -/
theorem hasSum_gaussRamanujanCoefficient_tprod_localResidueDensity (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) :
    HasSum (fun q ↦ L.gaussRamanujanCoefficient q M)
      ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ) := by
  obtain ⟨K, c, -, hK⟩ := L.exists_summable_norm_gaussRamanujanCoefficient_le hn
  have hS : Summable (fun q ↦ L.gaussRamanujanCoefficient q M) := (hK M hM).1.of_norm
  obtain ⟨-, hlim⟩ := L.tendsto_normalizedResidueCount_factorial_tprod_localResidueDensity hn hM
  have hfin : Tendsto (fun k : ℕ ↦ insert 0 (Nat.factorial k).divisors) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro a b hab
      exact Finset.insert_subset_insert _ (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero b)
        (Nat.factorial_dvd_factorial hab))
    · intro q
      rcases q.eq_zero_or_pos with rfl | hq
      · exact ⟨0, Finset.mem_insert_self _ _⟩
      · exact ⟨q, Finset.mem_insert_of_mem (Nat.mem_divisors.2
          ⟨Nat.dvd_factorial hq le_rfl, Nat.factorial_ne_zero q⟩)⟩
  have hA0 : L.gaussRamanujanCoefficient 0 M = 0 := by simp [gaussRamanujanCoefficient]
  have hpart : ∀ k, ∑ q ∈ insert 0 (Nat.factorial k).divisors, L.gaussRamanujanCoefficient q M =
      (L.normalizedResidueCount M (Nat.factorial k) : ℂ) := by
    intro k
    rw [Finset.sum_insert fun h ↦ Nat.factorial_ne_zero k (zero_dvd_iff.1 (Nat.mem_divisors.1 h).1),
      hA0, zero_add]
    exact L.sum_divisors_gaussRamanujanCoefficient (Nat.factorial_ne_zero k) M
  have h1 := (hS.hasSum.comp hfin).congr hpart
  have h2 : Tendsto (fun k ↦ (L.normalizedResidueCount M (Nat.factorial k) : ℂ)) atTop
      (𝓝 ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hlim
  rw [← tendsto_nhds_unique h1 h2]
  exact hS.hasSum

/-- The weighted form of (3.9): there is `c` such that any weight `w` on the positive integers with
`Σ_m ‖w m‖ m^c < ∞` has `Σ_m ‖w m‖ · Σ_q ‖A_q(m)‖ < ∞`.  (The real Gaussian coefficient
`m e^{-2π a m}` is such a weight for every `c`.) -/
theorem exists_summable_weight_mul_tsum_norm_gaussRamanujanCoefficient
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) :
    ∃ c : ℕ, ∀ w : ℕ → ℝ, Summable (fun m ↦ ‖w m‖ * ((m + 1 : ℕ) : ℝ) ^ c) →
      Summable (fun m ↦ ‖w m‖ * ∑' q, ‖L.gaussRamanujanCoefficient q ((m + 1 : ℕ) : ℤ)‖) := by
  obtain ⟨K, c, hK0, hK⟩ := L.exists_summable_norm_gaussRamanujanCoefficient_le hn
  refine ⟨c, fun w hw ↦ ?_⟩
  refine Summable.of_nonneg_of_le (fun m ↦ mul_nonneg (norm_nonneg _)
    (tsum_nonneg fun _ ↦ norm_nonneg _)) (fun m ↦ ?_) (hw.mul_left K)
  have hM : ((m + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hb := (hK _ hM).2
  rw [Int.natAbs_natCast] at hb
  calc ‖w m‖ * ∑' q, ‖L.gaussRamanujanCoefficient q ((m + 1 : ℕ) : ℤ)‖
      ≤ ‖w m‖ * (K * ((m + 1 : ℕ) : ℝ) ^ c) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = K * (‖w m‖ * ((m + 1 : ℕ) : ℝ) ^ c) := by ring

end PositiveDefiniteIntegralLattice
