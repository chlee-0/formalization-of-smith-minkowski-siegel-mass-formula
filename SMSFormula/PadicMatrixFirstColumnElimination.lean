import SMSFormula.PadicMatrixSingleElimination

/-!
# Integral p-adic first-column elimination

The one-entry integral transvections are composed in the fixed order
`Fin.succ 0, ..., Fin.succ (d - 1)`. Their product clears every nonzero-index
entry of the normalized first column and preserves the normalized pivot.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The integral first-column transvections, in increasing target-row order. -/
def firstColumnEliminationTransvections
    (P : PadicPivot p A) : List (GL (Fin (d + 1)) ℤ_[p]) :=
  List.ofFn fun i : Fin d =>
    P.firstColumnEliminationTransvection i.succ i.succ_ne_zero

/-- The integral general-linear factor clearing the normalized first column. -/
def firstColumnEliminationFactor
    (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.firstColumnEliminationTransvections.prod

/-- The corresponding list of transvection matrices over `Q_p`. -/
def firstColumnEliminationMatrices
    (P : PadicPivot p A) :
    List (Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) :=
  List.ofFn fun i : Fin d =>
    Matrix.transvection i.succ 0
      (P.firstColumnEliminationCoefficient i.succ : ℚ_[p])

@[simp]
theorem length_firstColumnEliminationMatrices
    (P : PadicPivot p A) :
    P.firstColumnEliminationMatrices.length = d := by
  simp [firstColumnEliminationMatrices]

theorem firstColumnEliminationMatrices_getElem
    (P : PadicPivot p A) {i : ℕ}
    (hi : i < P.firstColumnEliminationMatrices.length) :
    P.firstColumnEliminationMatrices[i] =
      let i' : Fin d :=
        ⟨i, P.length_firstColumnEliminationMatrices ▸ hi⟩
      Matrix.transvection i'.succ 0
        (P.firstColumnEliminationCoefficient i'.succ : ℚ_[p]) := by
  simp [firstColumnEliminationMatrices]

/-- Mapping the integral factor to `Q_p` gives the concrete transvection
matrix product used below. -/
theorem coe_map_firstColumnEliminationFactor
    (P : PadicPivot p A) :
    ((Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom
        P.firstColumnEliminationFactor :
          GL (Fin (d + 1)) ℚ_[p]) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
      P.firstColumnEliminationMatrices.prod := by
  unfold firstColumnEliminationFactor
  rw [map_list_prod]
  change
    (Units.coeHom
        (Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]))
        (List.map (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom)
          P.firstColumnEliminationTransvections).prod =
      P.firstColumnEliminationMatrices.prod
  rw [map_list_prod]
  apply congrArg List.prod
  rw [firstColumnEliminationTransvections,
    firstColumnEliminationMatrices]
  rw [List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [firstColumnEliminationTransvection,
    TransvectionStruct.toGeneralLinearGroup,
    TransvectionStruct.toMatrix]

/-- Apply the integral transvection product to the normalized matrix. -/
def firstColumnEliminatedMatrix
    (P : PadicPivot p A) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom
      P.firstColumnEliminationFactor :
        GL (Fin (d + 1)) ℚ_[p]) *
    P.normalizedMatrix

theorem firstColumnEliminatedMatrix_eq
    (P : PadicPivot p A) :
    P.firstColumnEliminatedMatrix =
      P.firstColumnEliminationMatrices.prod * P.normalizedMatrix := by
  rw [firstColumnEliminatedMatrix, P.coe_map_firstColumnEliminationFactor]

/-- A suffix of the elimination list leaves the normalized pivot row fixed. -/
theorem firstColumnEliminationMatrices_mul_zero_row_drop
    (P : PadicPivot p A) (j : Fin (d + 1)) {k : ℕ} (hk : k ≤ d) :
    (((P.firstColumnEliminationMatrices.drop k).prod *
        P.normalizedMatrix) 0 j) =
      P.normalizedMatrix 0 j := by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn ih =>
    have hn' : n < P.firstColumnEliminationMatrices.length := by
      simpa using hn
    rw [List.drop_eq_getElem_cons hn']
    let n' : Fin d := ⟨n, hn⟩
    have hmatrix :
        P.firstColumnEliminationMatrices[n] =
          Matrix.transvection n'.succ 0
            (P.firstColumnEliminationCoefficient n'.succ : ℚ_[p]) := by
      simpa [n'] using P.firstColumnEliminationMatrices_getElem hn'
    simp only [List.prod_cons, Matrix.mul_assoc, hmatrix]
    rw [Matrix.transvection_mul_apply_of_ne n'.succ 0 0 j]
    · exact ih
    · exact Ne.symm n'.succ_ne_zero
  | self =>
    simp only [length_firstColumnEliminationMatrices, le_refl,
      List.drop_eq_nil_of_le, List.prod_nil, Matrix.one_mul]

/-- The fixed-order product clears every nonzero-index first-column entry. -/
theorem firstColumnEliminationMatrices_mul_firstColumn
    (P : PadicPivot p A) (i : Fin d) :
    (P.firstColumnEliminationMatrices.prod *
        P.normalizedMatrix) i.succ 0 = 0 := by
  suffices h :
      ∀ k : ℕ, k ≤ d →
        (((P.firstColumnEliminationMatrices.drop k).prod *
            P.normalizedMatrix) i.succ 0) =
          if k ≤ i then 0 else P.normalizedMatrix i.succ 0 by
    simpa using h 0 (Nat.zero_le d)
  intro k hk
  induction hk using Nat.decreasingInduction with
  | of_succ n hn ih =>
    have hn' : n < P.firstColumnEliminationMatrices.length := by
      simpa using hn
    rw [List.drop_eq_getElem_cons hn']
    let n' : Fin d := ⟨n, hn⟩
    have hmatrix :
        P.firstColumnEliminationMatrices[n] =
          Matrix.transvection n'.succ 0
            (P.firstColumnEliminationCoefficient n'.succ : ℚ_[p]) := by
      simpa [n'] using P.firstColumnEliminationMatrices_getElem hn'
    simp only [List.prod_cons, Matrix.mul_assoc, hmatrix]
    by_cases hni : n' = i
    · subst i
      rw [Matrix.transvection_mul_apply_same]
      rw [ih]
      simp [n']
      rw [P.firstColumnEliminationMatrices_mul_zero_row_drop 0 hn]
      exact P.normalizedMatrix_add_coefficient_mul_pivot
        n'.succ n'.succ_ne_zero
    · rw [Matrix.transvection_mul_apply_of_ne n'.succ 0 i.succ 0]
      · rw [ih]
        rcases le_or_gt (n + 1) i with hi | hi
        · simp only [hi, Nat.le_trans (Nat.le_succ n) hi, if_true]
        · have hne : n ≠ i := by
            intro h
            apply hni
            exact Fin.ext h
          rw [if_neg (by omega), if_neg (by omega)]
      · intro h
        apply hni
        exact (Fin.succ_inj.mp h).symm
  | self =>
    simp only [length_firstColumnEliminationMatrices, le_refl,
      List.drop_eq_nil_of_le, List.prod_nil, Matrix.one_mul]
    rw [if_neg]
    exact Nat.not_le_of_lt i.isLt

@[simp]
theorem firstColumnEliminatedMatrix_apply_succ_zero
    (P : PadicPivot p A) (i : Fin d) :
    P.firstColumnEliminatedMatrix i.succ 0 = 0 := by
  rw [P.firstColumnEliminatedMatrix_eq]
  exact P.firstColumnEliminationMatrices_mul_firstColumn i

theorem firstColumnEliminatedMatrix_apply_zero_of_ne
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.firstColumnEliminatedMatrix i 0 = 0 := by
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  exact P.firstColumnEliminatedMatrix_apply_succ_zero j

@[simp]
theorem firstColumnEliminatedMatrix_zero_zero
    (P : PadicPivot p A) :
    P.firstColumnEliminatedMatrix 0 0 =
      (p : ℚ_[p]) ^ (A P.row P.col).valuation := by
  rw [P.firstColumnEliminatedMatrix_eq]
  have hzero :=
    P.firstColumnEliminationMatrices_mul_zero_row_drop
      (j := (0 : Fin (d + 1))) (k := 0) (Nat.zero_le d)
  rw [show
      (P.firstColumnEliminationMatrices.prod *
          P.normalizedMatrix) 0 0 =
        P.normalizedMatrix 0 0 by simpa using hzero]
  exact P.normalizedMatrix_zero_zero

end Matrix.PadicPivot
