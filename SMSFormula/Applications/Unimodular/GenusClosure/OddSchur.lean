import SMSFormula.Applications.Unimodular.GenusClosure.DiagonalClassification
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section

namespace UnimodularGenusClosure
open TypeIIModEightCertificates
open scoped BigOperators

def schurChange {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (inverse : Matrix α α R8) (cross : Matrix α β R8) :
    Matrix (α ⊕ β) (α ⊕ β) R8 :=
  Matrix.fromBlocks 1 (-(inverse * cross)) 0 1

def schurInverse {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (inverse : Matrix α α R8) (cross : Matrix α β R8) :
    Matrix (α ⊕ β) (α ⊕ β) R8 :=
  Matrix.fromBlocks 1 (inverse * cross) 0 1

def schurResidual {α β : Type*} [Fintype α]
    (inverse : Matrix α α R8) (cross : Matrix α β R8)
    (tail : Matrix β β R8) : Matrix β β R8 :=
  tail - cross.transpose * inverse * cross

def schurCertificate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (head inverse : Matrix α α R8) (cross : Matrix α β R8)
    (tail : Matrix β β R8) (hsymm : inverse.IsSymm)
    (hleft : inverse * head = 1) (hright : head * inverse = 1) :
    GramCongruenceCertificate (Matrix.fromBlocks head cross cross.transpose tail)
      (sumBlockMatrix head (schurResidual inverse cross tail)) where
  changeMatrix := schurChange inverse cross
  inverseMatrix := schurInverse inverse cross
  congruence := by
    have hcross : head * (inverse * cross) = cross := by
      rw [← Matrix.mul_assoc, hright, Matrix.one_mul]
    rw [sumBlockMatrix_eq_fromBlocks]
    simp [schurChange, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_neg, Matrix.transpose_zero, Matrix.transpose_mul, hsymm.eq,
      Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, hleft, hcross, schurResidual, sub_eq_add_neg, add_comm]
  mul_inverse := by
    simp [schurChange, schurInverse, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  inverse_mul := by
    simp [schurChange, schurInverse, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem schurResidual_isSymm {α β : Type*} [Fintype α]
    (inverse : Matrix α α R8) (cross : Matrix α β R8)
    (tail : Matrix β β R8) (hinverse : inverse.IsSymm) (htail : tail.IsSymm) :
    (schurResidual inverse cross tail).IsSymm := by
  change (tail - cross.transpose * inverse * cross).transpose = _
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    hinverse.eq, htail.eq, schurResidual, Matrix.mul_assoc]

theorem schurResidual_det_isUnit {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (head inverse : Matrix α α R8) (cross : Matrix α β R8)
    (tail : Matrix β β R8) (hsymm : inverse.IsSymm)
    (hleft : inverse * head = 1) (hright : head * inverse = 1)
    (hdet : IsUnit (Matrix.fromBlocks head cross cross.transpose tail).det) :
    IsUnit (schurResidual inverse cross tail).det := by
  have hcert := (schurCertificate head inverse cross tail hsymm hleft hright).det_eq
  rw [sumBlockMatrix_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁] at hcert
  exact isUnit_of_mul_isUnit_right (hcert.symm ▸ hdet)

def splitIndexEquiv {α ι : Type*} (chosen : α ↪ ι) :
    α ⊕ {index : ι // index ∉ Set.range chosen} ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective chosen chosen.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun index => index ∈ Set.range chosen))

@[simp] theorem splitIndexEquiv_inl {α ι : Type*} (chosen : α ↪ ι) (index : α) :
    splitIndexEquiv chosen (Sum.inl index) = chosen index := rfl

@[simp] theorem splitIndexEquiv_inr {α ι : Type*} (chosen : α ↪ ι)
    (index : {index : ι // index ∉ Set.range chosen}) :
    splitIndexEquiv chosen (Sum.inr index) = index.val := rfl

def splitCross {α ι : Type*} (gram : Matrix ι ι R8) (chosen : α ↪ ι) :
    Matrix α {index : ι // index ∉ Set.range chosen} R8 :=
  gram.submatrix chosen Subtype.val

def splitTail {α ι : Type*} (gram : Matrix ι ι R8) (chosen : α ↪ ι) :
    Matrix {index : ι // index ∉ Set.range chosen}
      {index : ι // index ∉ Set.range chosen} R8 :=
  gram.submatrix Subtype.val Subtype.val

theorem splitSource_eq {α ι : Type*} (gram : Matrix ι ι R8)
    (chosen : α ↪ ι) (hsymm : gram.IsSymm) :
    Matrix.reindex (splitIndexEquiv chosen).symm (splitIndexEquiv chosen).symm gram =
      Matrix.fromBlocks (gram.submatrix chosen chosen) (splitCross gram chosen)
        (splitCross gram chosen).transpose (splitTail gram chosen) := by
  ext row col
  cases row <;> cases col <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, splitCross, splitTail,
      hsymm.apply]

def splitSchurCertificate {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (gram : Matrix ι ι R8) (chosen : α ↪ ι) (hsymm : gram.IsSymm)
    (inverse : Matrix α α R8) (hinverse : inverse.IsSymm)
    (hleft : inverse * gram.submatrix chosen chosen = 1)
    (hright : gram.submatrix chosen chosen * inverse = 1) :
    GramCongruenceCertificate
      (Matrix.reindex (splitIndexEquiv chosen).symm (splitIndexEquiv chosen).symm gram)
      (sumBlockMatrix (gram.submatrix chosen chosen)
        (schurResidual inverse (splitCross gram chosen) (splitTail gram chosen))) := by
  classical
  rw [splitSource_eq gram chosen hsymm]
  exact schurCertificate _ _ _ _ hinverse hleft hright

def OddDiagonalizes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) : Prop :=
  ∃ coefficients : ι → R8, (∀ index, IsUnit (coefficients index)) ∧
    Nonempty (GramCongruenceCertificate gram (Matrix.diagonal coefficients))

theorem oddDiagonalizes_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficients : ι → R8) (hunit : ∀ index, IsUnit (coefficients index)) :
    OddDiagonalizes (Matrix.diagonal coefficients) :=
  ⟨coefficients, hunit, ⟨⟨1, 1, by simp, by simp, by simp⟩⟩⟩

theorem oddDiagonalizes_of_certificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source target : Matrix ι ι R8} (cert : GramCongruenceCertificate source target)
    (htarget : OddDiagonalizes target) : OddDiagonalizes source := by
  obtain ⟨coefficients, hunits, ⟨last⟩⟩ := htarget
  exact ⟨coefficients, hunits, ⟨cert.trans last⟩⟩

theorem oddDiagonalizes_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (equiv : ι ≃ κ)
    {gram : Matrix ι ι R8} (hgram : OddDiagonalizes gram) :
    OddDiagonalizes (Matrix.reindex equiv equiv gram) := by
  obtain ⟨coefficients, hunits, ⟨cert⟩⟩ := hgram
  refine ⟨coefficients ∘ equiv.symm, fun index => hunits _, ⟨?_⟩⟩
  convert reindexCertificate equiv cert using 1
  ext row col
  simp [Matrix.reindex_apply, Matrix.diagonal_apply]

theorem oddDiagonalizes_reindex_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (equiv : ι ≃ κ) (gram : Matrix ι ι R8) :
    OddDiagonalizes (Matrix.reindex equiv equiv gram) ↔ OddDiagonalizes gram := by
  constructor
  · intro hgram
    have hback := oddDiagonalizes_reindex equiv.symm hgram
    simpa [Matrix.reindex_apply] using hback
  · exact oddDiagonalizes_reindex equiv

theorem oddDiagonalizes_sumBlock {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {left : Matrix α α R8} {right : Matrix β β R8}
    (hleft : OddDiagonalizes left) (hright : OddDiagonalizes right) :
    OddDiagonalizes (sumBlockMatrix left right) := by
  obtain ⟨leftCoefficients, hleftUnits, ⟨leftCert⟩⟩ := hleft
  obtain ⟨rightCoefficients, hrightUnits, ⟨rightCert⟩⟩ := hright
  refine ⟨Sum.elim leftCoefficients rightCoefficients, ?_, ⟨?_⟩⟩
  · intro index
    cases index with
    | inl index => exact hleftUnits index
    | inr index => exact hrightUnits index
  · convert sumBlockCertificate leftCert rightCert using 1
    ext row col
    cases row <;> cases col <;> simp [Matrix.diagonal_apply]

def unitLine (value : R8) : Matrix (Fin 1) (Fin 1) R8 := Matrix.diagonal (fun _ => value)

theorem unitLine_self_inverse (value : R8) (hunit : IsUnit value) :
    unitLine value * unitLine value = 1 := by
  obtain ⟨unit, rfl⟩ := hunit
  have hsquare := unit_square_certificate (unit : R8) (↑unit⁻¹) (by simp)
  ext row col
  fin_cases row
  fin_cases col
  simpa [unitLine, Matrix.mul_apply, pow_two] using hsquare

theorem oddDiagonalizes_unitLine (value : R8) (hunit : IsUnit value) :
    OddDiagonalizes (unitLine value) :=
  oddDiagonalizes_diagonal _ (fun _ => hunit)

def splitResidual {α ι : Type*} [Fintype α] [DecidableEq α]
    (gram : Matrix ι ι R8) (chosen : α ↪ ι) :
    Matrix {index : ι // index ∉ Set.range chosen}
      {index : ι // index ∉ Set.range chosen} R8 :=
  schurResidual (gram.submatrix chosen chosen)⁻¹ (splitCross gram chosen)
    (splitTail gram chosen)

def invertibleHeadSplitCertificate {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (gram : Matrix ι ι R8) (chosen : α ↪ ι) (hsymm : gram.IsSymm)
    (hhead : IsUnit (gram.submatrix chosen chosen).det) :
    GramCongruenceCertificate
      (Matrix.reindex (splitIndexEquiv chosen).symm (splitIndexEquiv chosen).symm gram)
      (sumBlockMatrix (gram.submatrix chosen chosen) (splitResidual gram chosen)) := by
  classical
  have hheadSymm := hsymm.submatrix chosen
  apply splitSchurCertificate gram chosen hsymm _ _
    (Matrix.nonsing_inv_mul _ hhead) (Matrix.mul_nonsing_inv _ hhead)
  change ((gram.submatrix chosen chosen)⁻¹).transpose = _
  rw [Matrix.transpose_nonsing_inv, hheadSymm.eq]

theorem splitResidual_isSymm {α ι : Type*} [Fintype α] [DecidableEq α]
    (gram : Matrix ι ι R8) (chosen : α ↪ ι) (hsymm : gram.IsSymm) :
    (splitResidual gram chosen).IsSymm := by
  apply schurResidual_isSymm
  · change ((gram.submatrix chosen chosen)⁻¹).transpose = _
    rw [Matrix.transpose_nonsing_inv, (hsymm.submatrix chosen).eq]
  · exact hsymm.submatrix Subtype.val

theorem splitResidual_det_isUnit {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (gram : Matrix ι ι R8) (chosen : α ↪ ι) (hsymm : gram.IsSymm)
    (hhead : IsUnit (gram.submatrix chosen chosen).det) (hdet : IsUnit gram.det) :
    IsUnit (splitResidual gram chosen).det := by
  classical
  have hcert := (invertibleHeadSplitCertificate gram chosen hsymm hhead).det_eq
  rw [sumBlockMatrix_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_reindex_self] at hcert
  exact isUnit_of_mul_isUnit_right (hcert.symm ▸ hdet)

theorem splitRemainder_card_lt {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    [Nonempty α]
    (chosen : α ↪ ι) :
    Fintype.card {index : ι // index ∉ Set.range chosen} < Fintype.card ι := by
  classical
  have hcard := Fintype.card_congr (splitIndexEquiv chosen)
  rw [Fintype.card_sum] at hcard
  have hpos := Fintype.card_pos (α := α)
  omega

def lineEmbedding {ι : Type*} (pivot : ι) : Fin 1 ↪ ι where
  toFun _ := pivot
  inj' _ _ _ := Subsingleton.elim _ _

theorem lineEmbedding_head {ι : Type*} (gram : Matrix ι ι R8) (pivot : ι) :
    gram.submatrix (lineEmbedding pivot) (lineEmbedding pivot) =
      Matrix.diagonal (fun _ : Fin 1 => gram pivot pivot) := by
  ext row col
  fin_cases row
  fin_cases col
  rfl

def pairEmbedding {ι : Type*} (left right : ι) (hdistinct : left ≠ right) : Fin 2 ↪ ι where
  toFun index := if index = 0 then left else right
  inj' := by
    intro first second heq
    fin_cases first <;> fin_cases second <;> simp_all

theorem pairEmbedding_head {ι : Type*} (gram : Matrix ι ι R8) (hsymm : gram.IsSymm)
    (left right : ι) (hdistinct : left ≠ right) :
    gram.submatrix (pairEmbedding left right hdistinct) (pairEmbedding left right hdistinct) =
      !![gram left left, gram left right; gram left right, gram right right] := by
  ext row col
  fin_cases row <;> fin_cases col <;> simp [pairEmbedding, hsymm.apply]

theorem evenBinary_det_isUnit (left cross right : R8)
    (hleft : ¬ IsUnit left) (hright : ¬ IsUnit right) (hcross : IsUnit cross) :
    IsUnit (!![left, cross; cross, right] : M2).det := by
  have hfinite : ∀ left cross right : R8,
      ¬ IsUnit left → ¬ IsUnit right → IsUnit cross →
      IsUnit (!![left, cross; cross, right] : M2).det := by decide
  exact hfinite left cross right hleft hright hcross

theorem exists_unit_offdiag_of_det_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) (hdet : IsUnit gram.det)
    (hdiag : ∀ index, ¬ IsUnit (gram index index)) (pivot : ι) :
    ∃ partner, partner ≠ pivot ∧ IsUnit (gram pivot partner) := by
  have heven : ∀ value : R8, ¬ IsUnit value → zmod8Even value := by
    unfold zmod8Even
    decide
  classical
  by_contra hnone
  have hrow : ∀ index, zmod8Even (gram pivot index) := by
    intro index
    apply heven
    by_cases heq : index = pivot
    · simpa [heq] using hdiag pivot
    · exact fun hunit => hnone ⟨index, heq, hunit⟩
  have hinverse := Matrix.mul_nonsing_inv gram hdet
  have hentry := congrFun (congrFun hinverse pivot) pivot
  have hevenSum : zmod8Even (∑ index, gram pivot index * gram⁻¹ index pivot) :=
    zmod8Even_sum _ _ (fun index _ => zmod8Even_mul_left (hrow index))
  rw [Matrix.mul_apply] at hentry
  have hone : zmod8Even (1 : R8) := by
    simpa only [hentry, Matrix.one_apply_eq] using hevenSum
  exact zmod8_one_not_even hone

theorem oddDiagonalizes_tripleInput (first second third cross : Fin 4) :
    OddDiagonalizes (tripleInput first second third cross) := by
  let gram := tripleInput first second third cross
  let change := tripleMove gram
  let inverse := tripleMoveInverse gram
  let target := change.transpose * gram * change
  obtain ⟨hoffdiag, hunits, hright, hleft⟩ :=
    tripleMove_certificate first second third cross
  refine ⟨fun index => target index index, ?_, ⟨⟨change, inverse, ?_, hright, hleft⟩⟩⟩
  · intro index
    exact IsUnit.of_mul_eq_one _ (hunits index)
  · change target = Matrix.diagonal (fun index => target index index)
    ext row col
    by_cases heq : row = col
    · subst col
      simp
    · simpa [Matrix.diagonal_apply, heq] using hoffdiag row col heq

theorem oddDiagonalizes_line_evenBinary (value left cross right : R8)
    (hvalue : IsUnit value) (hleft : ¬ IsUnit left) (hright : ¬ IsUnit right)
    (hcross : IsUnit cross) :
    OddDiagonalizes (sumBlockMatrix (unitLine value)
      (!![left, cross; cross, right] : M2)) := by
  have hodd : ∀ value : R8, IsUnit value → ∃ index : Fin 4, value = oddUnit index := by
    decide
  have heven : ∀ value : R8, ¬ IsUnit value →
      ∃ index : Fin 4, value = 2 * (index.val : R8) := by decide
  obtain ⟨first, rfl⟩ := hodd value hvalue
  obtain ⟨second, rfl⟩ := heven left hleft
  obtain ⟨third, rfl⟩ := heven right hright
  obtain ⟨middle, rfl⟩ := hodd cross hcross
  apply (oddDiagonalizes_reindex_iff finSumFinEquiv _).mp
  convert oddDiagonalizes_tripleInput first second third middle using 1
  ext row col
  fin_cases row <;> fin_cases col <;> rfl

theorem sumBlock_reindex_right {α β γ : Type*} (equiv : β ≃ γ)
    (left : Matrix α α R8) (right : Matrix β β R8) :
    Matrix.reindex (Equiv.sumCongr (Equiv.refl α) equiv)
        (Equiv.sumCongr (Equiv.refl α) equiv) (sumBlockMatrix left right) =
      sumBlockMatrix left (Matrix.reindex equiv equiv right) := by
  ext row col
  cases row <;> cases col <;> rfl

theorem oddDiagonalizes_sumBlock_assoc {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (left : Matrix α α R8) (middle : Matrix β β R8) (right : Matrix γ γ R8) :
    OddDiagonalizes (sumBlockMatrix left (sumBlockMatrix middle right)) ↔
      OddDiagonalizes (sumBlockMatrix (sumBlockMatrix left middle) right) := by
  have heq : Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
      (sumBlockMatrix (sumBlockMatrix left middle) right) =
      sumBlockMatrix left (sumBlockMatrix middle right) := by
    ext row col
    rcases row with row | (row | row) <;> rcases col with col | (col | col) <;> rfl
  rw [← heq, oddDiagonalizes_reindex_iff]

theorem oddDiagonalizes_three_lines_tail {β : Type*} [Fintype β] [DecidableEq β]
    (coefficients : Fin 1 ⊕ Fin 2 → R8) (tail : Matrix β β R8)
    (hunit : ∀ index, IsUnit (coefficients index))
    (hrest : OddDiagonalizes (sumBlockMatrix (unitLine (coefficients (Sum.inl 0))) tail)) :
    OddDiagonalizes (sumBlockMatrix (Matrix.diagonal coefficients) tail) := by
  let equiv : (Fin 1 ⊕ Fin 2) ⊕ β ≃ Fin 2 ⊕ (Fin 1 ⊕ β) :=
    (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl β)).trans (Equiv.sumAssoc _ _ _)
  apply (oddDiagonalizes_reindex_iff equiv _).mp
  have heq : Matrix.reindex equiv equiv (sumBlockMatrix (Matrix.diagonal coefficients) tail) =
      sumBlockMatrix (Matrix.diagonal (fun index : Fin 2 => coefficients (Sum.inr index)))
        (sumBlockMatrix (unitLine (coefficients (Sum.inl 0))) tail) := by
    ext row col
    rcases row with row | (row | row) <;> rcases col with col | (col | col) <;>
      simp [equiv, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.diagonal_apply, unitLine]
    fin_cases row
    fin_cases col
    rfl
  rw [heq]
  exact oddDiagonalizes_sumBlock
    (oddDiagonalizes_diagonal _ (fun index => hunit (Sum.inr index))) hrest

#assert_standard_axioms schurCertificate
#assert_standard_axioms schurResidual_isSymm
#assert_standard_axioms schurResidual_det_isUnit
#assert_standard_axioms splitSchurCertificate
#assert_standard_axioms oddDiagonalizes_sumBlock
#assert_standard_axioms oddDiagonalizes_reindex_iff

end UnimodularGenusClosure
