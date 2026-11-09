import SMSFormula.Applications.Unimodular.DirectPeeling.PeelingCore
import SMSFormula.Applications.Unimodular.ModEightTransport.FiniteCertificates

/-!
# Direct Type II hyperbolic peeling: packaged split step

This module packages the explicit split-pair square congruence from
`PeelingCore.lean` as the finite `GramCongruenceCertificate` interface used by
the native-count transport layer. It is still a one-step constructor,
not the all-rank recursive normal-form theorem.
-/

noncomputable section

namespace TypeIIDirectPeeling
open TypeIIModEightCertificates

/-- The explicit hyperbolic-pair split gives a packaged finite mod-eight
Gram-congruence certificate after reindexing the source matrix to the split
coordinate type. -/
def splitPairStepCertificate {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r) :
    GramCongruenceCertificate
      (G.submatrix (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj))
      (splitPairTargetMatrix G x y r j) where
  changeMatrix := splitPairSquareChangeMatrix G x y hrj
  inverseMatrix := splitPairSquareInverseMatrix G x y hrj
  congruence := splitPairSquareChangeMatrix_congruence hrj hsymm hp
  mul_inverse := splitPairSquareChangeMatrix_mul_inverse hrj hsymm hp hxr hy
  inverse_mul := splitPairSquareInverseMatrix_mul_change hrj hsymm hp hxr hy


/-- The residual block remaining after one hyperbolic-pair split. -/
def splitPairResidualMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    (r j : Fin n) : Matrix (RemainingIndex n r j) (RemainingIndex n r j) R :=
  (splitPairTargetMatrix G x y r j).submatrix Sum.inr Sum.inr

/-- The split-pair target is literally one hyperbolic plane plus the residual block. -/
theorem splitPairTargetMatrix_eq_sumBlockMatrix {n : ℕ}
    (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (r j : Fin n) :
    splitPairTargetMatrix G x y r j =
      sumBlockMatrix H (splitPairResidualMatrix G x y r j) := by
  ext a b
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          fin_cases a <;> fin_cases b <;> simp [splitPairTargetMatrix, H, sumBlockMatrix]
      | inr b =>
          fin_cases a <;> simp [splitPairTargetMatrix, sumBlockMatrix]
  | inr a =>
      cases b with
      | inl b =>
          fin_cases b <;> simp [splitPairTargetMatrix, sumBlockMatrix]
      | inr b =>
          rfl

/-- Reflexive finite Gram-congruence certificate used for block composition. -/
def reflGramCongruenceCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : GramCongruenceCertificate A A where
  changeMatrix := 1
  inverseMatrix := 1
  congruence := by simp
  mul_inverse := by simp
  inverse_mul := by simp

/-- The one-step split certificate with the target written as an explicit block sum. -/
def splitPairBlockStepCertificate {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r) :
    GramCongruenceCertificate
      (G.submatrix (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj))
      (sumBlockMatrix H (splitPairResidualMatrix G x y r j)) := by
  rw [← splitPairTargetMatrix_eq_sumBlockMatrix G x y r j]
  exact splitPairStepCertificate hrj hsymm hp hxr hy

/-- Compose one split step with a certificate for the residual block. This is the
certificate-level recursion interface for the direct hyperbolic-peeling route. -/
def splitPairStepThenResidualCertificate {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r)
    {T : Matrix (RemainingIndex n r j) (RemainingIndex n r j) R}
    (Cres : GramCongruenceCertificate (splitPairResidualMatrix G x y r j) T) :
    GramCongruenceCertificate
      (G.submatrix (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj))
      (sumBlockMatrix H T) :=
  (splitPairBlockStepCertificate hrj hsymm hp hxr hy).trans
    (sumBlockCertificate (reflGramCongruenceCertificate H) Cres)


/-- The residual index type has cardinality `n - 2`.  This is the bookkeeping fact
needed to feed the residual block back into the `Fin`-indexed split constructor. -/
theorem remainingIndex_card {n : ℕ} {r j : Fin n} (hrj : r ≠ j) :
    Fintype.card (RemainingIndex n r j) = n - 2 := by
  have hcard := Fintype.card_congr (splitPairIndexEquiv (n := n) hrj)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hcard
  omega

/-- A finite coordinate model for the residual block after deleting the two split pivots. -/
def remainingIndexFinEquiv {n : ℕ} {r j : Fin n} (hrj : r ≠ j) :
    RemainingIndex n r j ≃ Fin (n - 2) :=
  Fintype.equivFinOfCardEq (remainingIndex_card hrj)

/-- The residual block transported to the `Fin (n - 2)` index type used by recursive
split steps. -/
def splitPairResidualFinMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    {r j : Fin n} (hrj : r ≠ j) : Matrix (Fin (n - 2)) (Fin (n - 2)) R :=
  Matrix.reindex (remainingIndexFinEquiv hrj) (remainingIndexFinEquiv hrj)
    (splitPairResidualMatrix G x y r j)

/-- The residual block remains symmetric. -/
theorem splitPairResidualMatrix_isSymm {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) :
    (splitPairResidualMatrix G x y r j).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro a b
  exact Matrix.IsSymm.ext_iff.mp (splitPairTargetMatrix_isSymm hsymm) (Sum.inr a) (Sum.inr b)

/-- The residual block keeps even diagonal entries. -/
theorem splitPairResidualMatrix_diag_even {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hp : HyperbolicPair (matrixBilinear G) x y)
    (l : RemainingIndex n r j) :
    Even8 (splitPairResidualMatrix G x y r j l l) := by
  simpa [splitPairResidualMatrix] using
    (splitPairTargetMatrix_residual_diag_even hsymm hdiag hp l)

/-- The `Fin (n - 2)` residual model remains symmetric. -/
theorem splitPairResidualFinMatrix_isSymm {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) :
    (splitPairResidualFinMatrix G x y hrj).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro a b
  let e := remainingIndexFinEquiv hrj
  exact Matrix.IsSymm.ext_iff.mp (splitPairResidualMatrix_isSymm hsymm) (e.symm a) (e.symm b)

/-- The `Fin (n - 2)` residual model keeps even diagonal entries. -/
theorem splitPairResidualFinMatrix_diag_even {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hp : HyperbolicPair (matrixBilinear G) x y)
    (i : Fin (n - 2)) :
    Even8 (splitPairResidualFinMatrix G x y hrj i i) := by
  let e := remainingIndexFinEquiv hrj
  exact splitPairResidualMatrix_diag_even hsymm hdiag hp (e.symm i)

/-- The determinant of a generic block-sum matrix is the product of block determinants. -/
theorem sumBlockMatrix_det {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α α R) (B : Matrix β β R) :
    (sumBlockMatrix A B).det = A.det * B.det := by
  rw [sumBlockMatrix_eq_fromBlocks, Matrix.det_fromBlocks_zero₁₂]

/-- One hyperbolic split flips the determinant-sign invariant for the residual block. -/
theorem splitPairResidualMatrix_det_sign {n m : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r)
    (hdet : G.det = (-1 : R) ^ (m + 1)) :
    (splitPairResidualMatrix G x y r j).det = (-1 : R) ^ m := by
  let e := splitPairIndexEquiv hrj
  let Resid := splitPairResidualMatrix G x y r j
  let C := splitPairBlockStepCertificate hrj hsymm hp hxr hy
  have hstep : (-1 : R) * Resid.det = (-1 : R) ^ (m + 1) := by
    calc
      (-1 : R) * Resid.det = H.det * Resid.det := by rw [H_det]
      _ = (sumBlockMatrix H Resid).det := by rw [sumBlockMatrix_det]
      _ = (G.submatrix e e).det := C.det_eq
      _ = G.det := by rw [Matrix.det_submatrix_equiv_self]
      _ = (-1 : R) ^ (m + 1) := hdet
  calc
    Resid.det = (-1 : R) * ((-1 : R) * Resid.det) := by ring
    _ = (-1 : R) * (-1 : R) ^ (m + 1) := by rw [hstep]
    _ = (-1 : R) ^ m := by rw [pow_succ]; ring

/-- The `Fin (n - 2)` residual model satisfies the same determinant-sign invariant. -/
theorem splitPairResidualFinMatrix_det_sign {n m : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r)
    (hdet : G.det = (-1 : R) ^ (m + 1)) :
    (splitPairResidualFinMatrix G x y hrj).det = (-1 : R) ^ m := by
  rw [splitPairResidualFinMatrix, Matrix.det_reindex_self]
  exact splitPairResidualMatrix_det_sign hrj hsymm hp hxr hy hdet

/-- A determinant equal to one of the alternating signs is a unit, hence the matrix has
a right inverse. This converts the determinant-sign invariant into the input expected
by the next hyperbolic-pair selection step. -/
theorem exists_right_inverse_of_det_sign {n m : ℕ}
    (G : Matrix (Fin n) (Fin n) R) (hdet : G.det = (-1 : R) ^ m) :
    ∃ V : Matrix (Fin n) (Fin n) R, G * V = 1 := by
  have hdet_unit : IsUnit G.det := by
    rw [hdet]
    exact IsUnit.pow m (IsUnit.neg isUnit_one)
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact hdet_unit
  rcases hGunit with ⟨U, hU⟩
  refine ⟨↑U⁻¹, ?_⟩
  rw [← hU]
  simp

/-- Reindexing a matrix restricted along an equivalence returns the original matrix. -/
theorem reindex_submatrix_equiv_self {ι κ : Type*} (e : ι ≃ κ) (A : Matrix κ κ R) :
    Matrix.reindex e e (A.submatrix e e) = A := by
  ext i j
  simp [Matrix.reindex_apply]

/-- Reindexing a matrix along an equivalence and then back along the inverse returns the
original matrix. -/
theorem reindex_symm_reindex_self {ι κ : Type*} (e : ι ≃ κ) (A : Matrix ι ι R) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

/-- Compose one split step with a residual certificate and return to the original
coordinate index.  The target is the same split block target transported back along the
selected split-coordinate equivalence. -/
def splitPairStepThenResidualCertificate_originalIndex {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r)
    {T : Matrix (RemainingIndex n r j) (RemainingIndex n r j) R}
    (Cres : GramCongruenceCertificate (splitPairResidualMatrix G x y r j) T) :
    GramCongruenceCertificate G
      (Matrix.reindex (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj) (sumBlockMatrix H T)) := by
  let e := splitPairIndexEquiv hrj
  let C := splitPairStepThenResidualCertificate hrj hsymm hp hxr hy Cres
  have hsource : Matrix.reindex e e (G.submatrix e e) = G :=
    reindex_submatrix_equiv_self e G
  simpa [e, C, hsource] using (reindexCertificate e C)

/-- Recursive-facing version of `splitPairStepThenResidualCertificate_originalIndex`: the
residual certificate may be proved on the standard `Fin (n - 2)` coordinate model, then
this definition transports it back to the residual subtype and composes the split step. -/
def splitPairStepThenResidualFinCertificate_originalIndex {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r)
    {T : Matrix (Fin (n - 2)) (Fin (n - 2)) R}
    (Cres : GramCongruenceCertificate (splitPairResidualFinMatrix G x y hrj) T) :
    GramCongruenceCertificate G
      (Matrix.reindex (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj)
        (sumBlockMatrix H
          (Matrix.reindex (remainingIndexFinEquiv hrj).symm
            (remainingIndexFinEquiv hrj).symm T))) := by
  let e := remainingIndexFinEquiv hrj
  let CresBack := reindexCertificate e.symm Cres
  have hsource :
      Matrix.reindex e.symm e.symm (splitPairResidualFinMatrix G x y hrj) =
        splitPairResidualMatrix G x y r j := by
    simp [splitPairResidualFinMatrix, e]
  exact splitPairStepThenResidualCertificate_originalIndex hrj hsymm hp hxr hy
    (by simpa [e, hsource] using CresBack)

/-- Data produced by one recursive direct-H split step.  It records the selected
hyperbolic pair, the residual matrix invariants needed for the next step, and the
right inverse obtained from the determinant-sign invariant. -/
structure RecursiveSplitStepData {n m : ℕ} (G : Matrix (Fin n) (Fin n) R) where
  x : Fin n → R
  y : Fin n → R
  r : Fin n
  s : Fin n
  hrj : r ≠ s
  sourceSymm : G.IsSymm
  pair : HyperbolicPair (matrixBilinear G) x y
  pivot : x r = 1
  residualRows : ∀ l : RemainingIndex n r s, y l.1 = x l.1 * y r
  residualSymm : (splitPairResidualFinMatrix G x y hrj).IsSymm
  residualDiagEven : ∀ a, Even8 (splitPairResidualFinMatrix G x y hrj a a)
  residualDetSign : (splitPairResidualFinMatrix G x y hrj).det = (-1 : R) ^ m
  residualRightInverse : ∃ Vres : Matrix (Fin (n - 2)) (Fin (n - 2)) R,
    splitPairResidualFinMatrix G x y hrj * Vres = 1

/-- A selected recursive split step composes any future residual certificate back to a
certificate for the original matrix. -/
def RecursiveSplitStepData.certificate {n m : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (D : RecursiveSplitStepData (n := n) (m := m) G)
    {T : Matrix (Fin (n - 2)) (Fin (n - 2)) R}
    (Cres : GramCongruenceCertificate (splitPairResidualFinMatrix G D.x D.y D.hrj) T) :
    GramCongruenceCertificate G
      (Matrix.reindex (splitPairIndexEquiv D.hrj) (splitPairIndexEquiv D.hrj)
        (sumBlockMatrix H
          (Matrix.reindex (remainingIndexFinEquiv D.hrj).symm
            (remainingIndexFinEquiv D.hrj).symm T))) :=
  splitPairStepThenResidualFinCertificate_originalIndex D.hrj
    D.sourceSymm D.pair D.pivot D.residualRows Cres

/-- One actual recursive split step exists from three distinct coordinates.  The
determinant sign is turned into a right inverse for the residual, so the returned
residual block is ready for the same selector at the next recursive call. -/
theorem exists_recursiveSplitStepDataFromThreeCoordinates {n m : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hdet : G.det = (-1 : R) ^ (m + 1))
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nonempty (RecursiveSplitStepData (n := n) (m := m) G) := by
  obtain ⟨x, y, r, s, hrj, hp, hxr, hy⟩ :=
    exists_split_pair_from_three_coordinates_of_right_inverse_mod8
      G V hGV hsymm hdiag i j k hij hik hjk
  refine ⟨
    { x := x
      y := y
      r := r
      s := s
      hrj := hrj
      sourceSymm := hsymm
      pair := hp
      pivot := hxr
      residualRows := hy
      residualSymm := splitPairResidualFinMatrix_isSymm hrj hsymm
      residualDiagEven := splitPairResidualFinMatrix_diag_even hrj hsymm hdiag hp
      residualDetSign := splitPairResidualFinMatrix_det_sign hrj hsymm hp hxr hy hdet
      residualRightInverse := ?_ }⟩
  exact exists_right_inverse_of_det_sign _
    (splitPairResidualFinMatrix_det_sign hrj hsymm hp hxr hy hdet)

/-- A chosen recursive split step from three distinct coordinates. -/
def recursiveSplitStepDataFromThreeCoordinates {n m : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hdet : G.det = (-1 : R) ^ (m + 1))
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    RecursiveSplitStepData (n := n) (m := m) G :=
  Classical.choice
    (exists_recursiveSplitStepDataFromThreeCoordinates
      G V hGV hsymm hdiag hdet i j k hij hik hjk)

/-- A `Fin n` coordinate type has three distinct coordinates as soon as `3 ≤ n`. -/
theorem exists_three_distinct_fin {n : ℕ} (hn : 3 ≤ n) :
    ∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp at this
  · intro h
    have := congrArg Fin.val h
    simp at this
  · intro h
    have := congrArg Fin.val h
    simp at this

/-- Recursive split-step data exists without supplying coordinate names once the current
residual rank is at least three. -/
theorem exists_recursiveSplitStepData_of_three_le {n m : ℕ}
    (hn : 3 ≤ n)
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hdet : G.det = (-1 : R) ^ (m + 1)) :
    Nonempty (RecursiveSplitStepData (n := n) (m := m) G) := by
  obtain ⟨i, j, k, hij, hik, hjk⟩ := exists_three_distinct_fin hn
  exact exists_recursiveSplitStepDataFromThreeCoordinates
    G V hGV hsymm hdiag hdet i j k hij hik hjk

/-- A chosen recursive split step in rank at least three. -/
def recursiveSplitStepDataOfThreeLe {n m : ℕ}
    (hn : 3 ≤ n)
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hdet : G.det = (-1 : R) ^ (m + 1)) :
    RecursiveSplitStepData (n := n) (m := m) G :=
  Classical.choice
    (exists_recursiveSplitStepData_of_three_le hn G V hGV hsymm hdiag hdet)

#assert_standard_axioms splitPairStepCertificate
#assert_standard_axioms remainingIndex_card
#assert_standard_axioms remainingIndexFinEquiv
#assert_standard_axioms splitPairResidualFinMatrix
#assert_standard_axioms splitPairResidualMatrix_isSymm
#assert_standard_axioms splitPairResidualMatrix_diag_even
#assert_standard_axioms splitPairResidualFinMatrix_isSymm
#assert_standard_axioms splitPairResidualFinMatrix_diag_even
#assert_standard_axioms sumBlockMatrix_det
#assert_standard_axioms splitPairResidualMatrix_det_sign
#assert_standard_axioms splitPairResidualFinMatrix_det_sign
#assert_standard_axioms exists_right_inverse_of_det_sign
#assert_standard_axioms reindex_submatrix_equiv_self
#assert_standard_axioms reindex_symm_reindex_self
#assert_standard_axioms splitPairStepThenResidualFinCertificate_originalIndex
#assert_standard_axioms splitPairStepThenResidualCertificate_originalIndex
#assert_standard_axioms RecursiveSplitStepData
#assert_standard_axioms RecursiveSplitStepData.certificate
#assert_standard_axioms exists_recursiveSplitStepDataFromThreeCoordinates
#assert_standard_axioms recursiveSplitStepDataFromThreeCoordinates
#assert_standard_axioms exists_three_distinct_fin
#assert_standard_axioms exists_recursiveSplitStepData_of_three_le
#assert_standard_axioms recursiveSplitStepDataOfThreeLe
#assert_standard_axioms splitPairResidualMatrix
#assert_standard_axioms splitPairTargetMatrix_eq_sumBlockMatrix
#assert_standard_axioms reflGramCongruenceCertificate
#assert_standard_axioms splitPairBlockStepCertificate
#assert_standard_axioms splitPairStepThenResidualCertificate

end TypeIIDirectPeeling
