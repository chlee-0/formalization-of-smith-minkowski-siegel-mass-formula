import SMSFormula.FiniteOrthogonalGroupGeneralOrder
import SMSFormula.Product

/-!
# Odd-rank good-prime orthogonal orders and density factors

This downstream module combines the completed arbitrary finite orthogonal-
group order with the good-prime normalized-cardinality theorem from
`Product.lean`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every good-prime reduced Gram form of dimension `2r+1` has the standard
closed odd orthogonal-group order.  The endpoint `r=0` is the actual
one-dimensional order theorem. -/
theorem natCard_goodPrimeFiniteGramOrthogonalGroup_odd_closedExpression
    (r : ℕ) (L : PositiveDefiniteIntegralLattice (2 * r + 1))
    (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) =
      oddIdentityOrthogonalOrderExpression p.1 r := by
  cases r with
  | zero =>
      simpa [oddIdentityOrthogonalOrderExpression,
        finiteOrthogonalOrderEulerProduct] using
        natCard_goodPrimeFiniteGramOrthogonalGroup_rank_one L p hp
  | succ m =>
      letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
      have hchar : ringChar (ZMod p.1) ≠ 2 := by
        rw [ZMod.ringChar_zmod_n]
        exact not_mem_massBadPrimeSet_ne_two L hp
      have hq : 2 ≤ Nat.card (ZMod p.1) := by
        rw [Nat.card_zmod]
        exact p.2.two_le
      change Nat.card (finiteGramOrthogonalGroup (goodPrimeGramMatrix L p)) = _
      simpa only [Nat.succ_eq_add_one, Nat.card_zmod] using
        natCard_oddFiniteGramOrthogonalGroup_eq_closedExpression
          hchar hq (m + 1) (by omega)
          (goodPrimeGramMatrix L p) (goodPrimeGramMatrix_isSymm L p)
          (goodPrimeGramMatrix_det_ne_zero L p hp)

/-! ### Closed-order normalization algebra -/

/-- One natural finite-orthogonal Euler factor, after extracting its power of
`p`, is the real Euler factor used by Schulze--Pillot. -/
lemma cast_finiteOrthogonalEulerFactor_div_pow_eq
    (p : {p : ℕ // Nat.Prime p}) (j : ℕ) :
    (((p.1 ^ (2 * j) - 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (2 * j)) =
      1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))) := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp_nonneg : (0 : ℝ) ≤ p.1 := by positivity
  have hp_pow_one : 1 ≤ p.1 ^ (2 * j) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero)
  have hrpow :
      (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))) =
        ((p.1 : ℝ) ^ (2 * j))⁻¹ := by
    rw [show (2 : ℝ) * (j : ℝ) = ((2 * j : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_neg hp_nonneg, Real.rpow_natCast]
  rw [hrpow, Nat.cast_sub hp_pow_one]
  norm_num [Nat.cast_pow]
  field_simp [hp0]

/-- The cast natural Euler product divided by its total extracted power of
`p` is exactly the real Schulze--Pillot Euler core. -/
theorem cast_finiteOrthogonalOrderEulerProduct_div_pow_eq_goodPrimeEulerCore
    (p : {p : ℕ // Nat.Prime p}) (r : ℕ) :
    (finiteOrthogonalOrderEulerProduct p.1 r : ℝ) /
        (p.1 : ℝ) ^ (r * (r + 1)) =
      goodPrimeEulerCore p (r + 1) := by
  induction r with
  | zero =>
      simp [finiteOrthogonalOrderEulerProduct,
        goodPrimeEulerCore]
  | succ r ih =>
      have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      have hp_pow_one : 1 ≤ p.1 ^ (2 * (r + 1)) :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero)
      have hcore :
          goodPrimeEulerCore p ((r + 1) + 1) =
            goodPrimeEulerCore p (r + 1) *
              (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * ((r + 1 : ℕ) : ℝ)))) := by
        unfold goodPrimeEulerCore
        change
          (Finset.Icc 1 (r + 1)).prod (fun j =>
              1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) =
            (Finset.Icc 1 r).prod (fun j =>
              1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))) *
                (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * ((r + 1 : ℕ) : ℝ))))
        exact Finset.prod_Icc_succ_top (by omega) _
      calc
        (finiteOrthogonalOrderEulerProduct p.1 (r + 1) : ℝ) /
            (p.1 : ℝ) ^ ((r + 1) * (r + 1 + 1)) =
          ((finiteOrthogonalOrderEulerProduct p.1 r : ℝ) *
              ((p.1 ^ (2 * (r + 1)) - 1 : ℕ) : ℝ)) /
            ((p.1 : ℝ) ^ (r * (r + 1)) *
              (p.1 : ℝ) ^ (2 * (r + 1))) := by
                rw [finiteOrthogonalOrderEulerProduct_succ,
                  Nat.cast_mul, Nat.cast_sub hp_pow_one, Nat.cast_pow]
                congr 2
                rw [← pow_add]
                congr 2
                ring
        _ =
          ((finiteOrthogonalOrderEulerProduct p.1 r : ℝ) /
              (p.1 : ℝ) ^ (r * (r + 1))) *
            (((p.1 ^ (2 * (r + 1)) - 1 : ℕ) : ℝ) /
              (p.1 : ℝ) ^ (2 * (r + 1))) := by
                field_simp [hp0]
        _ = goodPrimeEulerCore p (r + 1) *
            (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * ((r + 1 : ℕ) : ℝ)))) := by
              rw [ih, cast_finiteOrthogonalEulerFactor_div_pow_eq]
        _ = goodPrimeEulerCore p ((r + 1) + 1) := hcore.symm

/-- Substituting the closed odd orthogonal order into the normalized
good-prime density leaves exactly the real Euler core. -/
theorem cast_normalized_oddOrthogonalOrderExpression_eq_goodPrimeEulerCore
    (p : {p : ℕ // Nat.Prime p}) (r : ℕ) :
    (((1 / 2 : ℚ) *
        ((p.1 : ℚ) ^ ((2 * r + 1) * ((2 * r + 1) - 1) / 2))⁻¹ *
        (oddIdentityOrthogonalOrderExpression p.1 r : ℚ) : ℚ) : ℝ) =
      goodPrimeEulerCore p (r + 1) := by
  rw [← cast_finiteOrthogonalOrderEulerProduct_div_pow_eq_goodPrimeEulerCore]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hN :
      (2 * r + 1) * (2 * r) / 2 =
        r * r + r * (r + 1) := by
    calc
      (2 * r + 1) * (2 * r) / 2 =
          ((2 * r + 1) * r) * 2 / 2 := by
            congr 1
            ring
      _ = (2 * r + 1) * r := by
        rw [Nat.mul_comm ((2 * r + 1) * r) 2]
        exact Nat.mul_div_right ((2 * r + 1) * r) (by omega)
      _ = r * r + r * (r + 1) := by ring
  unfold oddIdentityOrthogonalOrderExpression
  norm_num [Nat.cast_mul, Nat.cast_pow]
  rw [hN, pow_add]
  field_simp [hp0]

/-! ### The odd good-prime factor -/

/-- In literal dimension `2r+1`, the normalized good-prime classical density
is the odd Euler factor with Schulze--Pillot parameter `r+1`. -/
theorem goodPrime_classicalSolutionCountLocalDensity_factor_odd_closed
    (r : ℕ) (L : PositiveDefiniteIntegralLattice (2 * r + 1))
    (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) =
      goodPrimeOddEulerFactor p (r + 1) := by
  rw [classicalSolutionCountLocalDensityAtPrime_eq_orthogonalGroup_normalizedCard_of_goodPrime
      L p hp,
    natCard_goodPrimeFiniteGramOrthogonalGroup_odd_closedExpression r L p hp]
  unfold goodPrimeOddEulerFactor
  convert
    cast_normalized_oddOrthogonalOrderExpression_eq_goodPrimeEulerCore p r using 1
  simp only [mul_assoc]

/-- The odd good-prime density factor in arbitrary rank, with a rank-equality
interface. -/
theorem goodPrime_classicalSolutionCountLocalDensity_factor_odd
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (s : ℕ) (hs : 0 < s)
    (hn : n = 2 * s - 1) :
    (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) =
      goodPrimeOddEulerFactor p s := by
  subst n
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one.mpr hs
  have hdim : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
  generalize hN : 2 * (r + 1) - 1 = N at L hp ⊢
  have hN_eq : N = 2 * r + 1 := hN.symm.trans hdim
  clear hN
  subst N
  exact
    goodPrime_classicalSolutionCountLocalDensity_factor_odd_closed
      r L p hp

end PositiveDefiniteIntegralLattice
