import SMSFormula.Applications.Unimodular.GenusClosure.BinaryGauss

noncomputable section

namespace UnimodularGenusClosure
open scoped BigOperators

theorem oddResidue_cases_of_isUnit (value : R8) (hunit : IsUnit value) :
    value = 1 ∨ value = 3 ∨ value = 5 ∨ value = 7 := by
  obtain ⟨unit, rfl⟩ := hunit
  have hfinite : ∀ left right : R8, left * right = 1 →
      left = 1 ∨ left = 3 ∨ left = 5 ∨ left = 7 := by decide
  exact hfinite unit (↑unit⁻¹) (by simp)

theorem word_perm_countWord (word : List R8)
    (hodd : ∀ value ∈ word, value = 1 ∨ value = 3 ∨ value = 5 ∨ value = 7) :
    word.Perm (countWord (word.count 1) (word.count 3) (word.count 5) (word.count 7)) := by
  have h13 : (1 : R8) ≠ 3 := by decide
  have h15 : (1 : R8) ≠ 5 := by decide
  have h17 : (1 : R8) ≠ 7 := by decide
  have h35 : (3 : R8) ≠ 5 := by decide
  have h37 : (3 : R8) ≠ 7 := by decide
  have h57 : (5 : R8) ≠ 7 := by decide
  apply List.perm_iff_count.mpr
  intro value
  by_cases hone : value = 1
  · subst value
    simp [countWord, List.count_replicate, Ne.symm h13,
      Ne.symm h15, Ne.symm h17]
  by_cases hthree : value = 3
  · subst value
    simp [countWord, List.count_replicate, h13, Ne.symm h35, Ne.symm h37]
  by_cases hfive : value = 5
  · subst value
    simp [countWord, List.count_replicate, h15, h35, Ne.symm h57]
  by_cases hseven : value = 7
  · subst value
    simp [countWord, List.count_replicate, h17, h37, h57]
  have hnot : value ∉ word := by
    intro hmem
    rcases hodd value hmem with hvalue | hvalue | hvalue | hvalue
    · exact hone hvalue
    · exact hthree hvalue
    · exact hfive hvalue
    · exact hseven hvalue
  simp [countWord, List.count_replicate,
    Ne.symm hone, Ne.symm hthree, Ne.symm hfive, Ne.symm hseven]
  exact List.count_eq_zero.mpr hnot

theorem wordMatrix_det (word : List R8) : (wordMatrix word).det = word.prod := by
  rw [wordMatrix, Matrix.det_diagonal, ← Fin.prod_ofFn, List.ofFn_get]

theorem binaryWordGauss_eq_list_prod (word : List R8) :
    binaryWordGauss word = (word.map (fun value => 1 + Complex.I ^ value.val)).prod := by
  rw [binaryWordGauss_eq_prod, ← Fin.prod_ofFn]
  congr 1
  calc
    _ = (List.ofFn word.get).map (fun value : R8 => 1 + Complex.I ^ value.val) :=
      List.map_ofFn.symm
    _ = _ := by rw [List.ofFn_get]

theorem binaryWordGauss_eq_of_perm {left right : List R8} (perm : left.Perm right) :
    binaryWordGauss left = binaryWordGauss right := by
  rw [binaryWordGauss_eq_list_prod, binaryWordGauss_eq_list_prod]
  exact (perm.map (fun value => 1 + Complex.I ^ value.val)).prod_eq

theorem normalizes_word_of_det_binaryGauss (word : List R8)
    (hodd : ∀ value ∈ word, value = 1 ∨ value = 3 ∨ value = 5 ∨ value = 7)
    (hdet : (wordMatrix word).det = 1)
    (hgauss : binaryWordGauss word = (1 + Complex.I) ^ word.length) :
    Normalizes (wordMatrix word) := by
  have perm := word_perm_countWord word hodd
  apply normalizes_word_of_perm perm
  apply normalizes_countWord_of_det_binaryGauss
  · rw [wordMatrix_det, ← perm.prod_eq, ← wordMatrix_det]
    exact hdet
  · rw [← binaryWordGauss_eq_of_perm perm, ← perm.length_eq]
    exact hgauss

theorem normalizes_word_of_units_det_binaryGauss (word : List R8)
    (hunits : ∀ value ∈ word, IsUnit value)
    (hdet : (wordMatrix word).det = 1)
    (hgauss : binaryWordGauss word = (1 + Complex.I) ^ word.length) :
    Normalizes (wordMatrix word) :=
  normalizes_word_of_det_binaryGauss word
    (fun value hmem => oddResidue_cases_of_isUnit value (hunits value hmem)) hdet hgauss

#assert_standard_axioms word_perm_countWord
#assert_standard_axioms binaryWordGauss_eq_of_perm
#assert_standard_axioms normalizes_word_of_det_binaryGauss
#assert_standard_axioms normalizes_word_of_units_det_binaryGauss

end UnimodularGenusClosure
