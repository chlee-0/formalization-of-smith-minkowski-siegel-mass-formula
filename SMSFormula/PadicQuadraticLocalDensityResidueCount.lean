import SMSFormula.PadicQuadraticLocalDensityLevelOne
import SMSFormula.FiniteFieldQuadraticFormCount

/-! The explicit level-one residue count. For a symmetric Gram matrix `F` over
`ℤ_p` with unit determinant and `p` odd, the level-one residue set
`R_1 = {r ∈ F_p^N : r ⬝ F̄ r = ā}` has, with `χ` the quadratic character of `F_p`,

* `N = 2m + 1`: `#R_1 = p^{2m} + p^m · χ((-1)^m · det F̄ · ā)`;
* `N = 2m + 2`, `a` a unit: `#R_1 = p^{2m+1} − p^m · χ((-1)^{m+1} · det F̄)`.

With the level-one identity `p^{N−1} · λ(X_a(ℤ_p)) · ν(ℤ_p) = #R_1 · ν_vec(ℤ_p^N)`
this is the explicit good-place local density. The diagonal case is recorded
separately. The Gram matrix is supplied; no basis or diagonalization enters the
statements. -/
noncomputable section
open Finset Matrix

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

/-- `ZMod (p ^ 1)` is the prime field. -/
local instance factPrimePowOne : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩

theorem ringChar_zmodPowOne_ne_two (hp : p ≠ 2) : ringChar (ZMod (p ^ 1)) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n, pow_one]; exact hp

theorem card_zmodPowOne : (Fintype.card (ZMod (p ^ 1)) : ℤ) = p := by
  rw [ZMod.card, pow_one]

theorem toZModPow_one_ne_zero {z : ℤ_[p]} (hz : ‖(z : ℚ_[p])‖ = 1) : toZModPow 1 z ≠ 0 := by
  intro h
  have := (toZModPow_eq_zero_iff z 1).mp h
  rw [PadicInt.padic_norm_e_of_padicInt] at hz
  rw [hz] at this
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := zpow_lt_one_of_neg₀ hp1 (by simp)
  linarith

/-- The level-one residue set of a diagonal Gram matrix is a diagonal count. -/
theorem card_levelOne_diagonal (d : Fin N → ℤ_[p]) (a : ℤ_[p]) :
    (univ.filter (fun r : Fin N → ZMod (p ^ 1) ↦
        r ⬝ᵥ ((Matrix.diagonal d).map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card =
      FiniteField.diagonalQuadraticCount (fun i ↦ toZModPow 1 (d i)) (toZModPow 1 a) := by
  unfold FiniteField.diagonalQuadraticCount
  congr 1
  refine Finset.filter_congr fun r _ ↦ ?_
  rw [Matrix.diagonal_map (map_zero _)]
  simp only [dotProduct, mulVec_diagonal]
  constructor <;> intro h <;> (rw [← h]; refine sum_congr rfl fun i _ ↦ by ring)

/-- Odd rank `N = 2m + 1`: `#R_1 = p^{2m} + p^m χ((-1)^m ∏ d̄ᵢ ā)`. -/
theorem card_levelOne_diagonal_odd (hp : p ≠ 2) (m : ℕ) (d : Fin (2 * m + 1) → ℤ_[p])
    (hd : ∀ i, ‖(d i : ℚ_[p])‖ = 1) (a : ℤ_[p]) :
    ((univ.filter (fun r : Fin (2 * m + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ ((Matrix.diagonal d).map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) =
      (p : ℤ) ^ (2 * m) + (p : ℤ) ^ m *
        quadraticChar (ZMod (p ^ 1)) ((-1) ^ m * (∏ i, toZModPow 1 (d i)) * toZModPow 1 a) := by
  rw [card_levelOne_diagonal, FiniteField.diagonalQuadraticCount_odd
    (ringChar_zmodPowOne_ne_two hp) m _ (fun i ↦ toZModPow_one_ne_zero (hd i)), card_zmodPowOne]

/-- Even rank `N = 2m + 2`, `a` a unit: `#R_1 = p^{2m+1} − p^m χ((-1)^{m+1} ∏ d̄ᵢ)`. -/
theorem card_levelOne_diagonal_even (hp : p ≠ 2) (m : ℕ) (d : Fin (2 * m + 2) → ℤ_[p])
    (hd : ∀ i, ‖(d i : ℚ_[p])‖ = 1) (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) :
    ((univ.filter (fun r : Fin (2 * m + 2) → ZMod (p ^ 1) ↦
        r ⬝ᵥ ((Matrix.diagonal d).map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) =
      (p : ℤ) ^ (2 * m + 1) - (p : ℤ) ^ m *
        quadraticChar (ZMod (p ^ 1)) ((-1) ^ (m + 1) * ∏ i, toZModPow 1 (d i)) := by
  rw [card_levelOne_diagonal, FiniteField.diagonalQuadraticCount_even
    (ringChar_zmodPowOne_ne_two hp) m _ (fun i ↦ toZModPow_one_ne_zero (hd i)), card_zmodPowOne,
    if_neg (toZModPow_one_ne_zero ha)]
  ring

theorem det_map_toZModPow (k : ℕ) (F : Matrix (Fin N) (Fin N) ℤ_[p]) :
    (F.map (toZModPow k)).det = toZModPow k F.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

theorem isUnit_toZModPow_one_det {F : Matrix (Fin N) (Fin N) ℤ_[p]}
    (hdet : ‖((F.det : ℤ_[p]) : ℚ_[p])‖ = 1) : (F.map (toZModPow 1)).det ≠ 0 := by
  rw [det_map_toZModPow]
  exact toZModPow_one_ne_zero hdet

/-- The level-one residue set of a Gram matrix is the matrix count of its reduction. -/
theorem card_levelOne_eq_matrixQuadraticCount (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p]) :
    (univ.filter (fun r : Fin N → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card =
      FiniteField.matrixQuadraticCount (F.map (toZModPow 1)) (toZModPow 1 a) := rfl

/-- Odd rank `N = 2m + 1`, symmetric unimodular `F`:
`#R_1 = p^{2m} + p^m χ((-1)^m det F̄ · ā)`. -/
theorem card_levelOne_odd (hp : p ≠ 2) (m : ℕ) (F : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ_[p])
    (hF : F.IsSymm) (hdet : ‖((F.det : ℤ_[p]) : ℚ_[p])‖ = 1) (a : ℤ_[p]) :
    ((univ.filter (fun r : Fin (2 * m + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) =
      (p : ℤ) ^ (2 * m) + (p : ℤ) ^ m *
        quadraticChar (ZMod (p ^ 1)) ((-1) ^ m * toZModPow 1 F.det * toZModPow 1 a) := by
  rw [card_levelOne_eq_matrixQuadraticCount, FiniteField.matrixQuadraticCount_odd
    (ringChar_zmodPowOne_ne_two hp) m _ (hF.map _) (isUnit_toZModPow_one_det hdet),
    card_zmodPowOne, det_map_toZModPow]

/-- Even rank `N = 2m + 2`, symmetric unimodular `F`, `a` a unit:
`#R_1 = p^{2m+1} − p^m χ((-1)^{m+1} det F̄)`. -/
theorem card_levelOne_even (hp : p ≠ 2) (m : ℕ) (F : Matrix (Fin (2 * m + 2)) (Fin (2 * m + 2)) ℤ_[p])
    (hF : F.IsSymm) (hdet : ‖((F.det : ℤ_[p]) : ℚ_[p])‖ = 1) (a : ℤ_[p])
    (ha : ‖(a : ℚ_[p])‖ = 1) :
    ((univ.filter (fun r : Fin (2 * m + 2) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) =
      (p : ℤ) ^ (2 * m + 1) - (p : ℤ) ^ m *
        quadraticChar (ZMod (p ^ 1)) ((-1) ^ (m + 1) * toZModPow 1 F.det) := by
  rw [card_levelOne_eq_matrixQuadraticCount, FiniteField.matrixQuadraticCount_even
    (ringChar_zmodPowOne_ne_two hp) m _ (hF.map _) (isUnit_toZModPow_one_det hdet),
    card_zmodPowOne, det_map_toZModPow, if_neg (toZModPow_one_ne_zero ha)]
  ring

end PadicInt
