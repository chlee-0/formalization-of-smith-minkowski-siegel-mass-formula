import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Eliminating the orbit Riesz ratio between the two one-shell identities

The one-shell theta identity `r·Θ·(t_W b_W)·τ_V = (t_V b_V)·τ_W·d` and the Euler-cancelled Riesz ratio
`r·F = c_G·(d_∞·((t_V/t_W)·G₁·G₂)·X/Y)` share the orbit Riesz ratio `r`.  Multiplying crosswise
eliminates `r` without assuming `r ≠ 0`; then `t_W·(t_V/t_W) = t_V` and the common finite nonzero
`t_V` cancels:

`Θ · (b_W·τ_V·c_G·d_∞·G₁·G₂·X/Y) = b_V·τ_W·d·F`.

So the theta shell weight against `d` is `b_V τ_W F / (b_W τ_V c_G d_∞ G₁ G₂ X / Y)`: no finite
stabilizer volume `t` and no orbit Riesz ratio remains.  Pure algebra; nothing is chosen.
-/

open scoped ENNReal

namespace ENNReal

/-- Elimination of the Riesz ratio and of the finite stabilizer volumes. -/
theorem thetaShellWeight_eq_of_riesz {r Θ tW bW τV tV bV τW d F cG dR G₁ G₂ X Y : ℝ≥0∞}
    (h₁ : r * Θ * (tW * bW) * τV = (tV * bV) * τW * d)
    (h₂ : r * F = cG * (dR * (tV / tW * G₁ * G₂) * X / Y))
    (htW0 : tW ≠ 0) (htWt : tW ≠ ⊤) (htV0 : tV ≠ 0) (htVt : tV ≠ ⊤) :
    Θ * (bW * τV * cG * dR * G₁ * G₂ * X / Y) = bV * τW * d * F := by
  have e : tV * (bV * τW * d * F) = tV * (Θ * (bW * τV * cG * dR * G₁ * G₂ * X / Y)) := by
    calc tV * (bV * τW * d * F) = (tV * bV) * τW * d * F := by ring
      _ = r * Θ * (tW * bW) * τV * F := by rw [h₁]
      _ = (r * F) * Θ * tW * bW * τV := by ring
      _ = cG * (dR * (tV / tW * G₁ * G₂) * X / Y) * Θ * tW * bW * τV := by rw [h₂]
      _ = tV * (Θ * (bW * τV * cG * dR * G₁ * G₂ * X / Y)) * (tW⁻¹ * tW) := by
        simp only [div_eq_mul_inv]; ring
      _ = _ := by rw [ENNReal.inv_mul_cancel htW0 htWt, mul_one]
  exact ((ENNReal.mul_right_inj htV0 htVt).mp e).symm

end ENNReal
