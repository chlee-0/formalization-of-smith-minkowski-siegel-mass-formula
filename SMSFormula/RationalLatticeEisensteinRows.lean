import SMSFormula.RationalLatticeRegularizedEisenstein

/-!
# The regularized series as a sum of rows

The signed-pair series `E_s = ½ Σ_{(c,d) primitive} (Im γz)^s (cz+d)⁻² F(c,d)` equals

`E_s(z) = y^s e₀ + Σ_{c ≥ 1} Row_c(s, z)`,   `Row_c = Σ_{d ∈ ℤ} (Im γz)^s (cz+d)⁻² F(c,d) [(c,d) = 1]`

(`regEisenstein_eq_rows`).  The pairs `(0, ±1)` give `y^s e₀` each, and `(c,d) ↦ (-c,-d)` identifies the rows
`c` and `-c` (`regEisSummand_neg_neg`, by the `gaussColumn_neg_neg`).  All sums are absolute.  Nothing is
chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm

namespace PositiveDefiniteIntegralLattice

variable (L : PositiveDefiniteIntegralLattice 4)

/-- The `c`-th row `Row_c(s, z) = Σ_d (Im γz)^s (cz+d)⁻² F(c,d) [(c,d) = 1]`. -/
def regEisRow (s : ℝ) (z : ℂ) (c : ℤ) : L.PolarDiscriminantGroup → ℂ :=
  ∑' d : ℤ, L.regEisSummand s z ![c, d]

theorem regEisSummand_neg_neg (s : ℝ) (z : ℂ) (c d : ℤ) :
    L.regEisSummand s z ![-c, -d] = L.regEisSummand s z ![c, d] := by
  unfold regEisSummand eisRegularizer
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hcop : IsCoprime (-c) (-d) ↔ IsCoprime c d := IsCoprime.neg_neg_iff c d
  by_cases h : IsCoprime c d
  · rw [if_pos (hcop.2 h), if_pos h, L.gaussColumn_neg_neg]
    have hw : ((-c : ℤ) : ℂ) * z + ((-d : ℤ) : ℂ) = -((c : ℂ) * z + d) := by push_cast; ring
    rw [hw, normSq_neg, neg_sq]
  · rw [if_neg (mt hcop.1 h), if_neg h]

theorem regEisSummand_zero_one (s : ℝ) (z : ℂ) :
    L.regEisSummand s z ![0, 1] = ((z.im ^ s : ℝ) : ℂ) • L.gaussE0 := by
  unfold regEisSummand eisRegularizer
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [if_pos isCoprime_one_right, L.gaussColumn_zero]
  simp

theorem regEisSummand_zero_neg_one (s : ℝ) (z : ℂ) :
    L.regEisSummand s z ![0, -1] = ((z.im ^ s : ℝ) : ℂ) • L.gaussE0 := by
  unfold regEisSummand eisRegularizer
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [if_pos (isCoprime_one_right.neg_right), L.gaussColumn_zero]
  simp

theorem regEisSummand_zero_of_ne (s : ℝ) (z : ℂ) {d : ℤ} (h1 : d ≠ 1) (h2 : d ≠ -1) :
    L.regEisSummand s z ![0, d] = 0 := by
  unfold regEisSummand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [if_neg]
  rw [isCoprime_zero_left, Int.isUnit_iff]
  tauto

/-- The row at `c = 0` is `2 y^s e₀`. -/
theorem regEisRow_zero (s : ℝ) (z : ℂ) :
    L.regEisRow s z 0 = (2 : ℂ) • (((z.im ^ s : ℝ) : ℂ) • L.gaussE0) := by
  unfold regEisRow
  rw [tsum_eq_sum (s := {1, -1}) (fun d hd ↦ by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact L.regEisSummand_zero_of_ne s z hd.1 hd.2)]
  rw [Finset.sum_pair (by norm_num), L.regEisSummand_zero_one, L.regEisSummand_zero_neg_one, two_smul]

/-- The summand as a function on `ℤ × ℤ`. -/
theorem summable_regEisSummand_prod {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    Summable fun q : ℤ × ℤ ↦ L.regEisSummand s z ![q.1, q.2] := by
  exact (L.summable_regEisSummand hs hz).comp_injective (finTwoArrowEquiv ℤ).symm.injective

theorem regEisRow_neg (s : ℝ) (z : ℂ) (c : ℤ) : L.regEisRow s z (-c) = L.regEisRow s z c := by
  unfold regEisRow
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d ↦ ?_
  exact L.regEisSummand_neg_neg s z c d

/-- The row decomposition: `E_s(z) = y^s e₀ + Σ_{c ≥ 1} Row_c(s, z)`. -/
theorem regEisenstein_eq_rows {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    L.regEisenstein s z =
      ((z.im ^ s : ℝ) : ℂ) • L.gaussE0 + ∑' n : ℕ, L.regEisRow s z ((n : ℤ) + 1) := by
  have hP := L.summable_regEisSummand_prod hs hz
  have hrow : Summable fun c : ℤ ↦ L.regEisRow s z c := hP.prod
  have h1 : Summable fun n : ℕ ↦ L.regEisRow s z ((n : ℤ) + 1) :=
    hrow.comp_injective fun a b h ↦ by simpa using h
  have h2 : Summable fun n : ℕ ↦ L.regEisRow s z (-((n : ℤ) + 1)) :=
    hrow.comp_injective fun a b h ↦ by simpa using h
  have hsum : ∑' p : Fin 2 → ℤ, L.regEisSummand s z p = ∑' c : ℤ, L.regEisRow s z c := by
    rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
    exact hP.tsum_prod
  unfold regEisenstein
  rw [hsum, tsum_of_add_one_of_neg_add_one h1 h2, L.regEisRow_zero]
  simp_rw [L.regEisRow_neg]
  set S := ∑' n : ℕ, L.regEisRow s z ((n : ℤ) + 1)
  set a := ((z.im ^ s : ℝ) : ℂ) • L.gaussE0
  rw [show S + (2 : ℂ) • a + S = (2 : ℂ) • (a + S) by rw [smul_add, two_smul ℂ S]; abel, smul_smul]
  norm_num

end PositiveDefiniteIntegralLattice
