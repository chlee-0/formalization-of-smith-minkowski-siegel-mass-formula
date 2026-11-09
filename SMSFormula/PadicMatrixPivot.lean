import SMSFormula.PadicScalarFactorization
import Mathlib.Data.Matrix.Basic

/-!
# Minimum-valuation pivots for p-adic matrices

A nonzero finite p-adic matrix has a nonzero entry of minimum valuation.
Dividing every entry by such a pivot gives an integral p-adic scalar. This is
the finite pivot certificate needed before p-adic matrix elimination; no row
or column operation and no matrix decomposition is constructed here.
-/

noncomputable section

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A nonzero entry of a finite p-adic matrix whose valuation is minimal among
all nonzero entries. -/
structure PadicPivot (p : ℕ) [Fact p.Prime] (A : Matrix ι κ ℚ_[p]) where
  row : ι
  col : κ
  ne_zero : A row col ≠ 0
  valuation_le : ∀ i j, A i j ≠ 0 → (A row col).valuation ≤ (A i j).valuation

/-- A nonzero finite p-adic matrix has a minimum-valuation nonzero entry. -/
theorem padicPivot_nonempty (p : ℕ) [Fact p.Prime]
    (A : Matrix ι κ ℚ_[p]) (hA : A ≠ 0) :
    Nonempty (PadicPivot p A) := by
  classical
  let s : Finset (ι × κ) :=
    Finset.univ.filter fun ij => A ij.1 ij.2 ≠ 0
  have hs : s.Nonempty := by
    by_contra hs'
    simp only [Finset.not_nonempty_iff_eq_empty] at hs'
    apply hA
    ext i j
    have hij : (i, j) ∉ s := by simp [hs']
    simpa [s] using hij
  obtain ⟨ij, hij_mem, hij_min⟩ :=
    Finset.exists_min_image (s := s)
      (f := fun ij : ι × κ => (A ij.1 ij.2).valuation) hs
  exact ⟨
    { row := ij.1
      col := ij.2
      ne_zero := by simpa [s] using hij_mem
      valuation_le := by
        intro i j hij
        exact hij_min (i, j) (by simp [s, hij]) }⟩

/-- Choose a minimum-valuation nonzero entry of a nonzero finite p-adic
matrix. -/
def padicPivot (p : ℕ) [Fact p.Prime] (A : Matrix ι κ ℚ_[p])
    (hA : A ≠ 0) : PadicPivot p A :=
  Classical.choice (padicPivot_nonempty p A hA)

end Matrix

namespace Matrix.PadicPivot

variable {ι κ : Type*} {p : ℕ} [Fact p.Prime] {A : Matrix ι κ ℚ_[p]}

theorem norm_div_pivot_le_one (P : PadicPivot p A) (i : ι) (j : κ) :
    ‖A i j / A P.row P.col‖ ≤ 1 := by
  rw [Padic.norm_le_one_iff_val_nonneg]
  by_cases hij : A i j = 0
  · simp [hij]
  rw [div_eq_mul_inv, Padic.valuation_mul hij]
  · rw [Padic.valuation_inv]
    exact sub_nonneg.mpr (P.valuation_le i j hij)
  · exact inv_ne_zero P.ne_zero

/-- The integral matrix obtained by dividing every entry by a
minimum-valuation pivot. -/
def integralRatioMatrix (P : PadicPivot p A) : Matrix ι κ ℤ_[p] :=
  fun i j => ⟨A i j / A P.row P.col, P.norm_div_pivot_le_one i j⟩

@[simp]
theorem coe_integralRatioMatrix (P : PadicPivot p A) (i : ι) (j : κ) :
    ((P.integralRatioMatrix i j : ℤ_[p]) : ℚ_[p]) =
      A i j / A P.row P.col :=
  rfl

theorem coe_integralRatioMatrix_mul_pivot
    (P : PadicPivot p A) (i : ι) (j : κ) :
    ((P.integralRatioMatrix i j : ℤ_[p]) : ℚ_[p]) *
        A P.row P.col = A i j := by
  rw [coe_integralRatioMatrix, div_mul_cancel₀ _ P.ne_zero]

@[simp]
theorem integralRatioMatrix_pivot (P : PadicPivot p A) :
    P.integralRatioMatrix P.row P.col = 1 := by
  apply Subtype.ext
  simp [P.ne_zero]

end Matrix.PadicPivot
