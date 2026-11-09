import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import SMSFormula.StandardAxiomsGuard

/-!
# Rank-uniform reduction of odd diagonal words

The four counts refer to coefficients 1, 3, 5, 7. `Reduces` is a proof-valued
word certificate generated only by the certified pair and quaternion moves.
It is not defined to mean isometry or equality of masses. Interpreting this
certificate as an actual matrix uses block embeddings and permutations; that
adapter is deliberately not represented by an unproved declaration here.

These proof scripts have not been compiler-run in the authoring environment.
-/

namespace UnimodularGenusClosure

/-- A finite sequence of explicitly allowed local reductions to an all-one word. -/
inductive Reduces : ℕ → ℕ → ℕ → ℕ → Prop
  | ones (a : ℕ) : Reduces a 0 0 0
  | fivePair {a b c d : ℕ} :
      Reduces (a + 2) b c d → Reduces a b (c + 2) d
  | sevenPair {a b c d : ℕ} :
      Reduces a (b + 2) c d → Reduces a b c (d + 2)
  | mixedPair {a b c d : ℕ} :
      Reduces (a + 1) (b + 1) c d → Reduces a b (c + 1) (d + 1)
  | fourThrees {a b c d : ℕ} :
      Reduces (a + 4) b c d → Reduces a (b + 4) c d

/-- A decreasing-measure algorithm, valid in every rank, not a bounded search. -/
theorem reduces_of_counts (a b c d : ℕ)
    (hhigh : (c + d) % 2 = 0) (hthree : (b + d) % 4 = 0) :
    Reduces a b c d := by
  by_cases hc : 2 ≤ c
  · have h := reduces_of_counts (a + 2) b (c - 2) d (by omega) hthree
    have hr := Reduces.fivePair h
    convert hr using 1; omega
  by_cases hd : 2 ≤ d
  · have h := reduces_of_counts a (b + 2) c (d - 2) (by omega) (by omega)
    have hr := Reduces.sevenPair h
    convert hr using 1; omega
  by_cases hm : c = 1
  · have hd1 : d = 1 := by omega
    subst c
    subst d
    have h := reduces_of_counts (a + 1) (b + 1) 0 0 (by omega) (by omega)
    simpa using Reduces.mixedPair h
  have hc0 : c = 0 := by omega
  have hd0 : d = 0 := by omega
  subst c
  subst d
  by_cases hb : b = 0
  · subst b
    exact Reduces.ones a
  have hb4 : 4 ≤ b := by omega
  have h := reduces_of_counts (a + 4) (b - 4) 0 0 (by omega) (by omega)
  have hr := Reduces.fourThrees h
  convert hr using 1; omega
termination_by 4 * (c + d) + b
decreasing_by all_goals omega

private theorem periodic_pow {R : Type*} [Monoid R] (z : R)
    (k n : ℕ) (hk : z ^ k = 1) : z ^ n = z ^ (n % k) := by
  calc
    z ^ n = z ^ (n % k + k * (n / k)) := by rw [Nat.mod_add_div]
    _ = z ^ (n % k) := by rw [pow_add, pow_mul, hk, one_pow, mul_one]

/-- The actual determinant of the diagonal word in the finite ring. -/
def wordDet (a b c d : ℕ) : ZMod 8 :=
  1 ^ a * 3 ^ b * 5 ^ c * 7 ^ d

/-- The actual binary Gauss product of the diagonal word. -/
def wordGauss (a b c d : ℕ) : ℂ :=
  (1 + Complex.I) ^ (a + c) * (1 - Complex.I) ^ (b + d)

theorem wordDet_factor (a b c d : ℕ) :
    wordDet a b c d = (3 : ZMod 8) ^ (b + d) * 5 ^ (c + d) := by
  have h7 : (7 : ZMod 8) = 3 * 5 := by decide
  simp only [wordDet, one_pow, one_mul, h7, mul_pow, pow_add]
  ring

/-- The Gauss identity forces the number of 3 mod 4 coefficients to be 0 mod 4. -/
theorem phase_four_of_gauss (u v : ℕ)
    (h : (1 + Complex.I) ^ u * (1 - Complex.I) ^ v =
      (1 + Complex.I) ^ (u + v)) : v % 4 = 0 := by
  have hfactor : (1 - Complex.I : ℂ) = (1 + Complex.I) * (-Complex.I) := by
    calc
      _ = 1 - Complex.I := rfl
      _ = (1 + Complex.I) * (-Complex.I) := by
        ring_nf
        simp [Complex.I_sq]
        ring
  have hnz : (1 + Complex.I : ℂ) ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    norm_num at hh'
  have hh : (1 + Complex.I) ^ (u + v) * (-Complex.I) ^ v =
      (1 + Complex.I) ^ (u + v) * 1 := by
    simpa only [hfactor, mul_pow, pow_add, mul_assoc, mul_one] using h
  have hphase : (-Complex.I) ^ v = (1 : ℂ) :=
    mul_left_cancel₀ (pow_ne_zero (u + v) hnz) hh
  have hperiod : (-Complex.I : ℂ) ^ 4 = 1 := by norm_num
  rw [periodic_pow (-Complex.I) 4 v hperiod] at hphase
  have hlt := Nat.mod_lt v (by decide : 0 < 4)
  have cases : v % 4 = 0 ∨ v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by omega
  rcases cases with h0 | h1 | h2 | h3
  · exact h0
  · have hr := congrArg Complex.re hphase
    norm_num [h1] at hr
  · have hr := congrArg Complex.re hphase
    norm_num [h2] at hr
  · have hr := congrArg Complex.re hphase
    norm_num [h3, pow_succ, Complex.mul_re, Complex.mul_im] at hr

theorem high_even_of_det_phase (a b c d : ℕ)
    (hdet : wordDet a b c d = 1) (hphase : (b + d) % 4 = 0) :
    (c + d) % 2 = 0 := by
  rw [wordDet_factor] at hdet
  have h3 : (3 : ZMod 8) ^ 2 = 1 := by decide
  have h5 : (5 : ZMod 8) ^ 2 = 1 := by decide
  rw [periodic_pow (3 : ZMod 8) 2 (b + d) h3,
    periodic_pow (5 : ZMod 8) 2 (c + d) h5] at hdet
  have hb : (b + d) % 2 = 0 := by omega
  simp only [hb, pow_zero, one_mul] at hdet
  by_cases hc : (c + d) % 2 = 0
  · exact hc
  have hc1 : (c + d) % 2 = 1 := by omega
  have hne : (5 : ZMod 8) ≠ 1 := by decide
  exact False.elim (hne (by simpa [hc1] using hdet))

/-- Complete word-level classification from concrete finite invariants. -/
theorem reduces_of_det_gauss (a b c d : ℕ)
    (hdet : wordDet a b c d = 1)
    (hgauss : wordGauss a b c d = (1 + Complex.I) ^ (a + b + c + d)) :
    Reduces a b c d := by
  have hphase : (b + d) % 4 = 0 := by
    apply phase_four_of_gauss (a + c) (b + d)
    simpa only [wordGauss, show a + c + (b + d) = a + b + c + d by omega] using hgauss
  exact reduces_of_counts a b c d (high_even_of_det_phase a b c d hdet hphase) hphase

#assert_standard_axioms reduces_of_counts
#assert_standard_axioms wordDet_factor
#assert_standard_axioms phase_four_of_gauss
#assert_standard_axioms high_even_of_det_phase
#assert_standard_axioms reduces_of_det_gauss

end UnimodularGenusClosure
