import SMSFormula.PadicQuadraticLocalDensityExplicit
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! The tail product of good-place local densities. If `|ε_p| ≤ p^{-k}` with
`k ≥ 2` then `∏_p (1 + ε_p)` converges (mathlib's real multipliability of
`1 + f` for summable `f`) to a positive real (exponential of a convergent sum of
logs).

For `W ⊕ ⟨a⟩` of rank `2m + 1` (resp. `2m + 2`) and a supplied finite set `S` of
primes, the explicit tail factor at a prime `p` is `1` for `p ∈ S` or `p`
exceptional, and otherwise the explicit good-place density
`1 + χ((-1)^m det F̄ ā)/p^m` (resp. `1 − χ((-1)^{m+1} det F̄)/p^{m+1}`), which
is `λ(X_a(ℤ_p))·ν(ℤ_p)` for every supplied atlas and Haar `ν` (with the
repository unit Haar). For rank `2m + 1 ≥ 5` (resp. `2m + 2 ≥ 4`) the tail
product converges to a positive real. -/
noncomputable section
open MeasureTheory Set Metric Matrix Finset
open scoped ENNReal

/-- Convergent positive Euler-type product: `|ε_p| ≤ p^{-k}`, `k ≥ 2`. -/
theorem Nat.Primes.multipliable_one_add_and_tprod_pos (ε : Nat.Primes → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hε : ∀ p, |ε p| ≤ 1 / ((p : ℕ) : ℝ) ^ k) :
    Multipliable (fun p ↦ 1 + ε p) ∧ 0 < ∏' p, (1 + ε p) := by
  have hsumk : Summable (fun p : Nat.Primes ↦ 1 / ((p : ℕ) : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow.mpr (by omega)).subtype {p | p.Prime}
  have hsum : Summable ε := hsumk.of_norm_bounded (fun p ↦ by rw [Real.norm_eq_abs]; exact hε p)
  have hpos : ∀ p : Nat.Primes, 0 < 1 + ε p := by
    intro p
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hlt : 1 / ((p : ℕ) : ℝ) ^ k < 1 := by
      rw [div_lt_one (by positivity)]
      calc (1 : ℝ) < 2 := by norm_num
        _ ≤ ((p : ℕ) : ℝ) := hp2
        _ = ((p : ℕ) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ ((p : ℕ) : ℝ) ^ k := pow_le_pow_right₀ (by linarith) (by omega)
    have := neg_abs_le (ε p)
    linarith [hε p]
  have hlog := Real.summable_log_one_add_of_summable hsum
  refine ⟨Real.multipliable_one_add_of_summable hsum, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

theorem abs_quadraticChar_le_one {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    |(quadraticChar F x : ℝ)| ≤ 1 := by
  rcases quadraticChar_isQuadratic F x with h | h | h <;> rw [h] <;> norm_num

namespace RationalQuadraticSpaceMatrix

local instance ldtPrimesFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance ldtFactPrimePowOne (p : ℕ) [Fact p.Prime] : Fact (p ^ 1).Prime :=
  ⟨by rw [pow_one]; exact Fact.out⟩
local instance ldtPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] :=
  borel _
local instance ldtPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Odd

variable {m : ℕ} (W : RationalQuadraticSpaceMatrix (2 * m)) (a : ℚ) (ha : a ≠ 0)
  (S : Finset ℕ)

/-- The deviation `χ((-1)^m det F̄ ā)/p^m` of the explicit tail factor, zero on `S`
and at exceptional primes. -/
def goodPlaceDensityDeviationOdd (p : Nat.Primes) : ℝ :=
  if h : (p : ℕ) ∉ S ∧ (p : ℕ) ∉ W.goodPlaceExceptionalPrimes a ha then
    (quadraticChar (ZMod ((p : ℕ) ^ 1)) ((-1) ^ m *
        PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha _ h.2).det *
        PadicInt.toZModPow 1 (W.goodPlaceIntegralValue a ha _ h.2)) : ℝ) / ((p : ℕ) : ℝ) ^ m
  else 0

theorem abs_goodPlaceDensityDeviationOdd_le (p : Nat.Primes) :
    |W.goodPlaceDensityDeviationOdd a ha S p| ≤ 1 / ((p : ℕ) : ℝ) ^ m := by
  unfold goodPlaceDensityDeviationOdd
  split_ifs
  · have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [abs_div, abs_of_pos (pow_pos hp0 _)]
    exact div_le_div_of_nonneg_right (abs_quadraticChar_le_one _) (pow_pos hp0 _).le
  · have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [abs_zero]; exact (one_div_pos.mpr (pow_pos hp0 _)).le

/-- The explicit tail factor is the good-place density for every supplied atlas and
Haar `ν`. -/
theorem one_add_goodPlaceDensityDeviationOdd_eq (p : Nat.Primes) (hpS : (p : ℕ) ∉ S)
    (hp : (p : ℕ) ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(p : ℕ)]) [ν.IsAddHaarMeasure] (point : ℕ → Fin (2 * m + 1) → ℚ_[(p : ℕ)])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(p : ℕ)] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(p : ℕ)]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(p : ℕ)] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(p : ℕ)]).padicSquareBranchAtlasRegion (p : ℕ) point hpoint i) :
    1 + W.goodPlaceDensityDeviationOdd a ha S p =
      (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
          ℚ_[(p : ℕ)]).padicSquareBranchAtlasGlue (p : ℕ) point hpoint tH ν
          (Padic.unitHaar (p : ℕ) (Fin (2 * m + 1))) (algebraMap ℚ ℚ_[(p : ℕ)] a)
          {y | ‖y.1‖ ≤ 1}).toReal * (ν (closedBall 0 1)).toReal := by
  rw [W.goodPlace_localDensity_toReal_odd a ha _ hp ν point hpoint tH hcover]
  unfold goodPlaceDensityDeviationOdd
  rw [dif_pos ⟨hpS, hp⟩]

/-- Convergent positive tail, rank `2m + 1 ≥ 5`. -/
theorem multipliable_goodPlaceDensityOdd_and_tprod_pos (hm : 2 ≤ m) :
    Multipliable (fun p ↦ 1 + W.goodPlaceDensityDeviationOdd a ha S p) ∧
      0 < ∏' p, (1 + W.goodPlaceDensityDeviationOdd a ha S p) :=
  Nat.Primes.multipliable_one_add_and_tprod_pos _ hm (W.abs_goodPlaceDensityDeviationOdd_le a ha S)

end Odd

section Even

variable {m : ℕ} (W : RationalQuadraticSpaceMatrix (2 * m + 1)) (a : ℚ) (ha : a ≠ 0)
  (S : Finset ℕ)

/-- The deviation `−χ((-1)^{m+1} det F̄)/p^{m+1}` of the explicit tail factor. -/
def goodPlaceDensityDeviationEven (p : Nat.Primes) : ℝ :=
  if h : (p : ℕ) ∉ S ∧ (p : ℕ) ∉ W.goodPlaceExceptionalPrimes a ha then
    -((quadraticChar (ZMod ((p : ℕ) ^ 1)) ((-1) ^ (m + 1) *
        PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha _ h.2).det) : ℝ) /
      ((p : ℕ) : ℝ) ^ (m + 1))
  else 0

theorem abs_goodPlaceDensityDeviationEven_le (p : Nat.Primes) :
    |W.goodPlaceDensityDeviationEven a ha S p| ≤ 1 / ((p : ℕ) : ℝ) ^ (m + 1) := by
  unfold goodPlaceDensityDeviationEven
  split_ifs
  · have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [abs_neg, abs_div, abs_of_pos (pow_pos hp0 _)]
    exact div_le_div_of_nonneg_right (abs_quadraticChar_le_one _) (pow_pos hp0 _).le
  · have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [abs_zero]; exact (one_div_pos.mpr (pow_pos hp0 _)).le

theorem one_add_goodPlaceDensityDeviationEven_eq (p : Nat.Primes) (hpS : (p : ℕ) ∉ S)
    (hp : (p : ℕ) ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(p : ℕ)]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (2 * m + 1 + 1) → ℚ_[(p : ℕ)])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(p : ℕ)] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(p : ℕ)]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(p : ℕ)] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(p : ℕ)]).padicSquareBranchAtlasRegion (p : ℕ) point hpoint i) :
    1 + W.goodPlaceDensityDeviationEven a ha S p =
      (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
          ℚ_[(p : ℕ)]).padicSquareBranchAtlasGlue (p : ℕ) point hpoint tH ν
          (Padic.unitHaar (p : ℕ) (Fin (2 * m + 1 + 1))) (algebraMap ℚ ℚ_[(p : ℕ)] a)
          {y | ‖y.1‖ ≤ 1}).toReal * (ν (closedBall 0 1)).toReal := by
  rw [W.goodPlace_localDensity_toReal_even a ha _ hp ν point hpoint tH hcover]
  unfold goodPlaceDensityDeviationEven
  rw [dif_pos ⟨hpS, hp⟩, ← sub_eq_add_neg]

/-- Convergent positive tail, rank `2m + 2 ≥ 4`. -/
theorem multipliable_goodPlaceDensityEven_and_tprod_pos (hm : 1 ≤ m) :
    Multipliable (fun p ↦ 1 + W.goodPlaceDensityDeviationEven a ha S p) ∧
      0 < ∏' p, (1 + W.goodPlaceDensityDeviationEven a ha S p) :=
  Nat.Primes.multipliable_one_add_and_tprod_pos _ (by omega)
    (W.abs_goodPlaceDensityDeviationEven_le a ha S)

end Even

end RationalQuadraticSpaceMatrix
