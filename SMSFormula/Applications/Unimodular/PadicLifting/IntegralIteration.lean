import Mathlib.Tactic
import SMSFormula.StandardAxiomsGuard

/-!
# An integral polynomial replacement for repeated inverse-Newton correction

For an arbitrary (possibly noncommutative) ring, put Y₀=0 and
Yₖ₊₁=E-p*Yₖ². Its fixed-point defect is divisible by p^k. In the matrix
application, Cₖ=1+2pYₖ corrects A toward H=A+4pAE. Only one initial inverse
is needed to obtain E; the iteration has no divisions or matrix inversions.
-/

namespace UnimodularPadicLift

variable {R : Type*} [Ring R]

/-- Do not commute arbitrary matrix factors. -/
lemma square_sub_factor (x y t z : R) (hxy : x - y = t * z)
    (hxt : x * t = t * x) :
    x * x - y * y = t * (x * z + z * y) := by
  calc
    _ = x * (x - y) + (x - y) * y := by noncomm_ring
    _ = x * (t * z) + (t * z) * y := by rw [hxy]
    _ = t * (x * z + z * y) := by
      rw [← mul_assoc x t z, hxt]
      noncomm_ring

def integralIterate (p : ℕ) (E : R) : ℕ → R
  | 0 => 0
  | k + 1 => E - (p : R) * (integralIterate p E k * integralIterate p E k)

lemma integralIterate_step_factor (p : ℕ) (E : R) (k : ℕ) :
    ∃ Z : R, integralIterate p E (k + 1) - integralIterate p E k =
      (p : R) ^ k * Z := by
  induction k with
  | zero => exact ⟨E, by simp [integralIterate]⟩
  | succ k ih =>
      obtain ⟨Z, hZ⟩ := ih
      let x := integralIterate p E (k + 1)
      let y := integralIterate p E k
      have hxy : x - y = (p : R) ^ k * Z := hZ
      have hxt : x * (p : R) ^ k = (p : R) ^ k * x :=
        ((Nat.cast_commute p x).pow_left k).eq.symm
      have hsq := square_sub_factor x y ((p : R) ^ k) Z hxy hxt
      refine ⟨-(x * Z + Z * y), ?_⟩
      change (E - (p : R) * (x * x)) - (E - (p : R) * (y * y)) = _
      calc
        _ = -(p : R) * (x * x - y * y) := by noncomm_ring
        _ = -(p : R) * ((p : R) ^ k * (x * Z + Z * y)) := by rw [hsq]
        _ = (p : R) ^ (k + 1) * -(x * Z + Z * y) := by
          rw [pow_succ']
          noncomm_ring

/-- This is a rank-independent polynomial certificate, not a bounded test. -/
theorem integralIterate_defect_factor (p : ℕ) (E : R) (k : ℕ) :
    ∃ Z : R, integralIterate p E k +
      (p : R) * (integralIterate p E k * integralIterate p E k) - E =
        (p : R) ^ k * Z := by
  obtain ⟨Z, hZ⟩ := integralIterate_step_factor p E k
  refine ⟨-Z, ?_⟩
  calc
    _ = -(integralIterate p E (k + 1) - integralIterate p E k) := by
      rw [integralIterate]
      noncomm_ring
    _ = -((p : R) ^ k * Z) := by rw [hZ]
    _ = (p : R) ^ k * -Z := by noncomm_ring

/-- Truncated geometric inverses give two-sided approximate inverses, without
using openness of GL or continuity of matrix inversion. -/
def geometricInverse (T : R) : ℕ → R
  | 0 => 0
  | k + 1 => geometricInverse T k + T ^ k

lemma geometricInverse_commutes (T : R) (k : ℕ) :
    T * geometricInverse T k = geometricInverse T k * T := by
  induction k with
  | zero => simp [geometricInverse]
  | succ k ih =>
      simp only [geometricInverse, mul_add, add_mul, ih]
      rw [← pow_succ', ← pow_succ]

lemma geometricInverse_left (T : R) (k : ℕ) :
    (1 - T) * geometricInverse T k = 1 - T ^ k := by
  induction k with
  | zero => simp [geometricInverse]
  | succ k ih =>
      rw [geometricInverse, mul_add, ih, pow_succ']
      noncomm_ring

lemma geometricInverse_right (T : R) (k : ℕ) :
    geometricInverse T k * (1 - T) = 1 - T ^ k := by
  calc
    _ = (1 - T) * geometricInverse T k := by
      rw [mul_sub, sub_mul, mul_one, one_mul, geometricInverse_commutes]
    _ = _ := geometricInverse_left T k

#assert_standard_axioms integralIterate_step_factor
#assert_standard_axioms integralIterate_defect_factor
#assert_standard_axioms geometricInverse_left
#assert_standard_axioms geometricInverse_right

end UnimodularPadicLift
