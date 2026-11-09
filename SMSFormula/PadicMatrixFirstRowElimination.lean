import SMSFormula.PadicMatrixSingleRowElimination

/-!
# Integral p-adic first-row elimination

The one-entry integral right transvections are composed in the fixed
order `Fin.succ 0, ..., Fin.succ (d - 1)`. Their product clears every
nonzero-index entry of the first row while preserving the already-cleared
first column and its normalized pivot.

No block extraction, dimension induction, or matrix decomposition is
constructed here.
-/

noncomputable section

open Matrix

namespace Matrix.PadicPivot

variable {d p : ℕ} [Fact p.Prime]
  {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]}

/-- The integral first-row transvections, in increasing target-column order. -/
def firstRowEliminationTransvections
    (P : PadicPivot p A) : List (GL (Fin (d + 1)) ℤ_[p]) :=
  List.ofFn fun j : Fin d =>
    P.firstRowEliminationTransvection j.succ j.succ_ne_zero

/-- The integral general-linear factor clearing the first row. -/
def firstRowEliminationFactor
    (P : PadicPivot p A) : GL (Fin (d + 1)) ℤ_[p] :=
  P.firstRowEliminationTransvections.prod

/-- The corresponding list of right transvection matrices over `Q_p`. -/
def firstRowEliminationMatrices
    (P : PadicPivot p A) :
    List (Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) :=
  List.ofFn fun j : Fin d =>
    Matrix.transvection 0 j.succ
      (P.firstRowEliminationCoefficient j.succ : ℚ_[p])

@[simp]
theorem length_firstRowEliminationMatrices
    (P : PadicPivot p A) :
    P.firstRowEliminationMatrices.length = d := by
  simp [firstRowEliminationMatrices]

/-- Mapping the integral factor to `Q_p` gives the concrete transvection
matrix product used below. -/
theorem coe_map_firstRowEliminationFactor
    (P : PadicPivot p A) :
    ((Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom
        P.firstRowEliminationFactor :
          GL (Fin (d + 1)) ℚ_[p]) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]) =
      P.firstRowEliminationMatrices.prod := by
  unfold firstRowEliminationFactor
  rw [map_list_prod]
  change
    (Units.coeHom
        (Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p]))
        (List.map (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom)
          P.firstRowEliminationTransvections).prod =
      P.firstRowEliminationMatrices.prod
  rw [map_list_prod]
  apply congrArg List.prod
  rw [firstRowEliminationTransvections, firstRowEliminationMatrices]
  rw [List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp [firstRowEliminationTransvection,
    TransvectionStruct.toGeneralLinearGroup,
    TransvectionStruct.toMatrix]

/-- Apply the integral right-transvection product after first-column
elimination. -/
def firstRowEliminatedMatrix
    (P : PadicPivot p A) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ_[p] :=
  P.firstColumnEliminatedMatrix *
    (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom
      P.firstRowEliminationFactor :
        GL (Fin (d + 1)) ℚ_[p])

theorem firstRowEliminatedMatrix_eq
    (P : PadicPivot p A) :
    P.firstRowEliminatedMatrix =
      P.firstColumnEliminatedMatrix *
        P.firstRowEliminationMatrices.prod := by
  rw [firstRowEliminatedMatrix, P.coe_map_firstRowEliminationFactor]

/-- Every prefix of the right-transvection list preserves the cleared first
column. -/
theorem firstColumnEliminatedMatrix_mul_firstRowEliminationMatrices_apply_zero_take
    (P : PadicPivot p A) (i : Fin (d + 1)) {k : ℕ} (hk : k ≤ d) :
    (P.firstColumnEliminatedMatrix *
        (P.firstRowEliminationMatrices.take k).prod) i 0 =
      P.firstColumnEliminatedMatrix i 0 := by
  induction k with
  | zero =>
    simp
  | succ n ih =>
    have hnd : n < d := hk
    let n' : Fin d := ⟨n, hnd⟩
    have hmatrix :
        P.firstRowEliminationMatrices[n]? =
          some (Matrix.transvection 0 n'.succ
            (P.firstRowEliminationCoefficient n'.succ : ℚ_[p])) := by
      simp [firstRowEliminationMatrices, n', hnd]
    simp only [List.take_add_one, ← Matrix.mul_assoc, hmatrix,
      List.prod_append, Matrix.mul_one, List.prod_cons, List.prod_nil,
      Option.toList_some]
    rw [Matrix.mul_transvection_apply_of_ne 0 n'.succ i 0]
    · exact ih hnd.le
    · exact Ne.symm n'.succ_ne_zero

/-- The fixed-order right-transvection product clears every nonzero-index
first-row entry. -/
theorem firstColumnEliminatedMatrix_mul_firstRowEliminationMatrices_zero_apply
    (P : PadicPivot p A) (j : Fin d) :
    (P.firstColumnEliminatedMatrix *
        P.firstRowEliminationMatrices.prod) 0 j.succ = 0 := by
  suffices h :
      ∀ k : ℕ, k ≤ d →
        (P.firstColumnEliminatedMatrix *
            (P.firstRowEliminationMatrices.take k).prod) 0 j.succ =
          if k ≤ j then P.firstColumnEliminatedMatrix 0 j.succ else 0 by
    have hlength : P.firstRowEliminationMatrices.length = d := by simp
    rw [← List.take_length (l := P.firstRowEliminationMatrices), hlength]
    have hnot : ¬d ≤ j := Nat.not_le_of_lt j.isLt
    simpa [hnot] using h d (Nat.le_refl d)
  intro k hk
  induction k with
  | zero =>
    simp
  | succ n ih =>
    have hnd : n < d := hk
    let n' : Fin d := ⟨n, hnd⟩
    have hmatrix :
        P.firstRowEliminationMatrices[n]? =
          some (Matrix.transvection 0 n'.succ
            (P.firstRowEliminationCoefficient n'.succ : ℚ_[p])) := by
      simp [firstRowEliminationMatrices, n', hnd]
    simp only [List.take_add_one, ← Matrix.mul_assoc, hmatrix,
      List.prod_append, Matrix.mul_one, List.prod_cons, List.prod_nil,
      Option.toList_some]
    by_cases hnj : n' = j
    · subst j
      rw [Matrix.mul_transvection_apply_same]
      rw [ih hnd.le]
      rw [
        P.firstColumnEliminatedMatrix_mul_firstRowEliminationMatrices_apply_zero_take
          0 hnd.le]
      simp [n']
      simpa using
        P.firstColumnEliminatedMatrix_add_firstRowCoefficient_mul_pivot
          n'.succ
    · rw [Matrix.mul_transvection_apply_of_ne 0 n'.succ 0 j.succ]
      · rw [ih hnd.le]
        rcases le_or_gt (n + 1) j with hj | hj
        · simp only [hj, Nat.le_trans (Nat.le_succ n) hj, if_true]
        · have hne : n ≠ j := by
            intro h
            apply hnj
            exact Fin.ext h
          rw [if_neg (by omega), if_neg (by omega)]
      · intro h
        apply hnj
        exact (Fin.succ_inj.mp h).symm

@[simp]
theorem firstRowEliminatedMatrix_zero_apply_succ
    (P : PadicPivot p A) (j : Fin d) :
    P.firstRowEliminatedMatrix 0 j.succ = 0 := by
  rw [P.firstRowEliminatedMatrix_eq]
  exact
    P.firstColumnEliminatedMatrix_mul_firstRowEliminationMatrices_zero_apply j

theorem firstRowEliminatedMatrix_zero_apply_of_ne
    (P : PadicPivot p A) (j : Fin (d + 1)) (hj : j ≠ 0) :
    P.firstRowEliminatedMatrix 0 j = 0 := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj
  exact P.firstRowEliminatedMatrix_zero_apply_succ i

theorem firstRowEliminatedMatrix_apply_zero
    (P : PadicPivot p A) (i : Fin (d + 1)) :
    P.firstRowEliminatedMatrix i 0 =
      P.firstColumnEliminatedMatrix i 0 := by
  rw [P.firstRowEliminatedMatrix_eq]
  have hzero :=
    P.firstColumnEliminatedMatrix_mul_firstRowEliminationMatrices_apply_zero_take
      i (k := d) (Nat.le_refl d)
  have htake :
      P.firstRowEliminationMatrices.take d =
        P.firstRowEliminationMatrices := by
    exact (List.take_eq_self_iff _).2 (by simp)
  rw [htake] at hzero
  exact hzero

theorem firstRowEliminatedMatrix_apply_zero_of_ne
    (P : PadicPivot p A) (i : Fin (d + 1)) (hi : i ≠ 0) :
    P.firstRowEliminatedMatrix i 0 = 0 := by
  rw [P.firstRowEliminatedMatrix_apply_zero]
  exact P.firstColumnEliminatedMatrix_apply_zero_of_ne i hi

@[simp]
theorem firstRowEliminatedMatrix_zero_zero
    (P : PadicPivot p A) :
    P.firstRowEliminatedMatrix 0 0 =
      (p : ℚ_[p]) ^ (A P.row P.col).valuation := by
  rw [P.firstRowEliminatedMatrix_apply_zero]
  exact P.firstColumnEliminatedMatrix_zero_zero

end Matrix.PadicPivot
