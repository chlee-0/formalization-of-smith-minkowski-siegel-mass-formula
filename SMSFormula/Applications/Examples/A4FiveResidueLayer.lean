import SMSFormula.Applications.Examples.A4FiveBlock
import SMSFormula.Applications.Examples.A4FiveDiagonal

/-! Exact scalar residue layers for the native A4 affine lift at five. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice Matrix

local instance a4FiveResiduePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4FiveReduction : ZMod 25 →+* ZMod 5 := ZMod.castHom (by decide) _

theorem a4FiveReduction_intCast (z : ℤ) :
    a4FiveReduction (z : ZMod 25) = (z : ZMod 5) := map_intCast _ _

def a4FiveLift (a : ZMod 5) : ZMod 25 := a.val

def a4FiveEmbed : ZMod 5 →+ ZMod 25 where
  toFun a := 5 * a4FiveLift a
  map_zero' := by decide
  map_add' := by
    have h : ∀ a b : ZMod 5,
        5 * a4FiveLift (a + b) =
          5 * a4FiveLift a + 5 * a4FiveLift b := by decide +kernel
    exact h

theorem a4FiveLift_reduces (a : ZMod 5) :
    a4FiveReduction (a4FiveLift a) = a := by
  have h : ∀ a : ZMod 5, a4FiveReduction (a4FiveLift a) = a := by decide
  exact h a

theorem a4FiveEmbed_reduces (a : ZMod 5) :
    a4FiveReduction (a4FiveEmbed a) = 0 := by
  change a4FiveReduction (5 * a4FiveLift a) = 0
  rw [map_mul]
  have h : a4FiveReduction 5 = 0 := by decide
  rw [h, zero_mul]

theorem a4FiveEmbed_injective : Function.Injective a4FiveEmbed := by
  have h : ∀ a b : ZMod 5, a4FiveEmbed a = a4FiveEmbed b → a = b := by
    decide +kernel
  exact h

theorem a4FiveEmbed_mul (a : ZMod 5) (b : ZMod 25) :
    a4FiveEmbed a * b = a4FiveEmbed (a * a4FiveReduction b) := by
  have h : ∀ a : ZMod 5, ∀ b : ZMod 25,
      a4FiveEmbed a * b = a4FiveEmbed (a * a4FiveReduction b) := by
    decide +kernel
  exact h a b

theorem a4Five_mul_Embed (a : ZMod 25) (b : ZMod 5) :
    a * a4FiveEmbed b = a4FiveEmbed (a4FiveReduction a * b) := by
  rw [mul_comm, a4FiveEmbed_mul]
  congr 1
  ring

theorem a4FiveEmbed_intCast (z : ℤ) :
    a4FiveEmbed (z : ZMod 5) = 5 * (z : ZMod 25) := by
  have h := map_zsmul a4FiveEmbed z (1 : ZMod 5)
  have h1 : a4FiveEmbed 1 = 5 := by decide
  simpa only [zsmul_eq_mul, mul_one, h1, mul_comm] using h

theorem a4Five_dvd_cast (z : ℤ) (hz : (5 : ℤ) ∣ z) :
    (z : ZMod 25) = a4FiveEmbed ((z / 5 : ℤ) : ZMod 5) := by
  rw [a4FiveEmbed_intCast]
  calc
    (z : ZMod 25) = ((5 * (z / 5) : ℤ) : ZMod 25) :=
      congrArg Int.cast (Int.mul_ediv_cancel' hz).symm
    _ = _ := by push_cast; rfl

def a4FiveDigit (a : ZMod 25) : ZMod 5 := ((a.val / 5 : ℕ) : ZMod 5)

theorem a4Five_split (a : ZMod 25) :
    a = a4FiveLift (a4FiveReduction a) +
      a4FiveEmbed (a4FiveDigit a) := by
  have h : ∀ a : ZMod 25,
      a = a4FiveLift (a4FiveReduction a) +
        a4FiveEmbed (a4FiveDigit a) := by decide +kernel
  exact h a

theorem a4Five_affine_mul (a b x y : ZMod 5) :
    (a4FiveLift a + a4FiveEmbed x) *
        (a4FiveLift b + a4FiveEmbed y) =
      a4FiveLift a * a4FiveLift b + a4FiveEmbed (a * y + x * b) := by
  rw [add_mul, mul_add, mul_add, a4Five_mul_Embed, a4FiveEmbed_mul,
    a4FiveEmbed_mul, a4FiveLift_reduces, a4FiveLift_reduces,
    a4FiveEmbed_reduces]
  simp only [mul_zero, map_zero, add_zero, map_add]
  ring



theorem a4Five_weighted_affine_pair (c : ℤ) (a b x y : ZMod 5) :
    (c : ZMod 25)*(a4FiveLift a+a4FiveEmbed x)*(a4FiveLift b+a4FiveEmbed y) =
      (c : ZMod 25)*a4FiveLift a*a4FiveLift b +
        a4FiveEmbed ((c : ZMod 5)*(a*y+x*b)) := by
  rw [mul_assoc (c : ZMod 25),a4Five_affine_mul,mul_add,
    a4Five_mul_Embed,a4FiveReduction_intCast]
  ring

theorem a4Five_scaled_pair (g w : ZMod 25) :
    (5 : ZMod 25)*g*w = a4FiveEmbed (a4FiveReduction g*a4FiveReduction w) := by
  have h : ∀ g w : ZMod 25,
      (5 : ZMod 25)*g*w = a4FiveEmbed (a4FiveReduction g*a4FiveReduction w) := by
    decide +kernel
  exact h g w

theorem a4Five_kernel_split (a : ZMod 25) (ha : a4FiveReduction a = 0) :
    a = a4FiveEmbed (a4FiveDigit a) := by
  have h := a4Five_split a
  rw [ha,show a4FiveLift 0 = 0 by decide,zero_add] at h
  exact h

end MassFormulaReleaseExamples
