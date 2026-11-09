import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Scalar factorization over the p-adics

Every nonzero p-adic scalar is canonically an integral unit times the signed
power of `p` given by its valuation. This is the scalar input needed for
eventual p-adic matrix elimination; no matrix decomposition is asserted here.
-/

noncomputable section

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- The integral unit obtained by removing the valuation power of `p` from a
nonzero p-adic scalar. -/
def integralUnitPart (x : ℚ_[p]) (hx : x ≠ 0) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (u := x * (p : ℚ_[p]) ^ (-x.valuation)) (by
    simp [hx, Padic.norm_eq_zpow_neg_valuation]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)))

@[simp]
theorem coe_integralUnitPart (x : ℚ_[p]) (hx : x ≠ 0) :
    ((integralUnitPart p x hx : ℤ_[p]) : ℚ_[p]) =
      x * (p : ℚ_[p]) ^ (-x.valuation) :=
  PadicInt.mkUnits_eq _

/-- The exact integral-unit-times-uniformizer-power factorization of a
nonzero p-adic scalar. -/
theorem integralUnitPart_mul_p_zpow (x : ℚ_[p]) (hx : x ≠ 0) :
    ((integralUnitPart p x hx : ℤ_[p]) : ℚ_[p]) *
        (p : ℚ_[p]) ^ x.valuation = x := by
  rw [coe_integralUnitPart]
  rw [mul_assoc, ← zpow_add₀]
  · simp
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

@[simp]
theorem norm_integralUnitPart (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖((integralUnitPart p x hx : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  rw [coe_integralUnitPart]
  simp [hx, Padic.norm_eq_zpow_neg_valuation]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero))

@[simp]
theorem valuation_integralUnitPart (x : ℚ_[p]) (hx : x ≠ 0) :
    valuation ((integralUnitPart p x hx : ℤ_[p]) : ℚ_[p]) = 0 := by
  rw [coe_integralUnitPart, Padic.valuation_mul hx]
  · rw [Padic.valuation_zpow, Padic.valuation_p]
    omega
  · exact zpow_ne_zero _ (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)

theorem norm_p_zpow_valuation_eq (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖(p : ℚ_[p]) ^ x.valuation‖ = ‖x‖ := by
  rw [Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx]

end Padic
