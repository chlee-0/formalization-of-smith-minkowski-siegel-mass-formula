import SMSFormula.Applications.Unimodular.GenusClosure.FiniteMoves
import SMSFormula.Applications.Unimodular.GenusClosure.WordReduction
import SMSFormula.Applications.Unimodular.ModEightTransport.FiniteCertificates

noncomputable section

namespace UnimodularGenusClosure
open TypeIIModEightCertificates
open scoped BigOperators

def wordMatrix (word : List R8) : Matrix (Fin word.length) (Fin word.length) R8 :=
  Matrix.diagonal word.get

def Normalizes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) : Prop := Nonempty (GramCongruenceCertificate gram 1)

theorem normalizes_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Normalizes (1 : Matrix ι ι R8) :=
  ⟨⟨1, 1, by simp, by simp, by simp⟩⟩

theorem normalizes_of_certificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {source target : Matrix ι ι R8} (cert : GramCongruenceCertificate source target)
    (htarget : Normalizes target) : Normalizes source := by
  obtain ⟨last⟩ := htarget
  exact ⟨cert.trans last⟩

theorem normalizes_reindex_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (gram : Matrix ι ι R8) :
    Normalizes (Matrix.reindex equiv equiv gram) ↔ Normalizes gram := by
  constructor
  · rintro ⟨cert⟩
    have transported := reindexCertificate equiv.symm cert
    have hgram : Matrix.reindex equiv.symm equiv.symm
        (Matrix.reindex equiv equiv gram) = gram := by
      ext row col
      simp [Matrix.reindex_apply]
    exact ⟨by simpa only [hgram, reindexMatrix_one] using transported⟩
  · rintro ⟨cert⟩
    exact ⟨by simpa only [reindexMatrix_one] using reindexCertificate equiv cert⟩

theorem normalizes_word_of_perm {left right : List R8} (perm : left.Perm right)
    (hright : Normalizes (wordMatrix right)) : Normalizes (wordMatrix left) := by
  let equiv : Fin left.length ≃ Fin right.length :=
    ⟨perm.idxBij, perm.symm.idxBij, perm.idxBij_rightInverse_idxBij_symm,
      perm.idxBij_leftInverse_idxBij_symm⟩
  have hgram : Matrix.reindex equiv equiv (wordMatrix left) = wordMatrix right := by
    ext row col
    obtain ⟨row, rfl⟩ := equiv.surjective row
    obtain ⟨col, rfl⟩ := equiv.surjective col
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, wordMatrix,
      Matrix.diagonal_apply, equiv.injective.eq_iff]
    have hget := perm.getElem_idxBij_eq_getElem row
    simpa only [List.get_eq_getElem] using congrArg (fun value : R8 =>
      if row = col then value else 0) hget.symm
  apply (normalizes_reindex_iff equiv (wordMatrix left)).mp
  rw [hgram]
  exact hright

def appendIndexEquiv (left right : List R8) :
    Fin left.length ⊕ Fin right.length ≃ Fin (left ++ right).length :=
  finSumFinEquiv.trans (finCongr (by simp))

theorem wordMatrix_append (left right : List R8) :
    wordMatrix (left ++ right) =
      Matrix.reindex (appendIndexEquiv left right) (appendIndexEquiv left right)
        (sumBlockMatrix (wordMatrix left) (wordMatrix right)) := by
  ext row col
  obtain ⟨row, rfl⟩ := (appendIndexEquiv left right).surjective row
  obtain ⟨col, rfl⟩ := (appendIndexEquiv left right).surjective col
  cases row <;> cases col <;>
    simp [Matrix.reindex_apply, appendIndexEquiv, wordMatrix, Matrix.diagonal_apply,
      sumBlockMatrix, List.get_eq_getElem, Fin.ext_iff] <;> omega

theorem normalizes_word_prefix {left right : List R8}
    (equiv : Fin left.length ≃ Fin right.length)
    (cert : GramCongruenceCertificate
      (Matrix.reindex equiv equiv (wordMatrix left)) (wordMatrix right))
    (rest : List R8) (htarget : Normalizes (wordMatrix (right ++ rest))) :
    Normalizes (wordMatrix (left ++ rest)) := by
  rw [wordMatrix_append] at htarget ⊢
  have hright := (normalizes_reindex_iff _ _).mp htarget
  let unchanged : GramCongruenceCertificate (wordMatrix rest) (wordMatrix rest) :=
    ⟨1, 1, by simp, by simp, by simp⟩
  have hleft := normalizes_of_certificate (sumBlockCertificate cert unchanged) hright
  have hblock : sumBlockMatrix (Matrix.reindex equiv equiv (wordMatrix left))
        (wordMatrix rest) =
      Matrix.reindex (Equiv.sumCongr equiv (Equiv.refl (Fin rest.length)))
        (Equiv.sumCongr equiv (Equiv.refl (Fin rest.length)))
        (sumBlockMatrix (wordMatrix left) (wordMatrix rest)) := by
    ext row col
    cases row <;> cases col <;> rfl
  rw [hblock] at hleft
  exact (normalizes_reindex_iff _ _).mpr ((normalizes_reindex_iff _ _).mp hleft)

def pairWordCertificate (left right : Fin 4) :
    GramCongruenceCertificate (wordMatrix [oddUnit left, oddUnit right])
      (wordMatrix [oddUnit left + 4, oddUnit right + 4]) where
  changeMatrix := pairMove (oddUnit left) (oddUnit right)
  inverseMatrix := pairMoveInverse (oddUnit left) (oddUnit right)
  congruence := by
    have hpair (first second : R8) : wordMatrix [first, second] =
        diagonalPair first second := by
      ext row col
      fin_cases row <;> fin_cases col <;> simp [wordMatrix, diagonalPair]
    simpa only [hpair] using (pairMove_certificate left right).1
  mul_inverse := (pairMove_certificate left right).2.1
  inverse_mul := (pairMove_certificate left right).2.2

def quaternionWordCertificate :
    GramCongruenceCertificate (wordMatrix [3, 3, 3, 3]) (wordMatrix [1, 1, 1, 1]) where
  changeMatrix := quaternionMatrix
  inverseMatrix := quaternionInverse
  congruence := by
    have hthree : wordMatrix [3, 3, 3, 3] = (3 : R8) • (1 : M4) := by decide
    have hone : wordMatrix [1, 1, 1, 1] = (1 : M4) := by decide
    rw [hthree, hone]
    exact quaternion_certificate.1
  mul_inverse := quaternion_certificate.2.1
  inverse_mul := quaternion_certificate.2.2

def countWord (ones threes fives sevens : ℕ) : List R8 :=
  List.replicate ones 1 ++ List.replicate threes 3 ++
    List.replicate fives 5 ++ List.replicate sevens 7

theorem wordMatrix_countWord_det (ones threes fives sevens : ℕ) :
    (wordMatrix (countWord ones threes fives sevens)).det =
      wordDet ones threes fives sevens := by
  rw [wordMatrix, Matrix.det_diagonal, ← Fin.prod_ofFn, List.ofFn_get]
  simp [countWord, wordDet, mul_assoc]

def binaryWordGauss (word : List R8) : ℂ :=
  ∑ vector : Fin word.length → Fin 2,
    Complex.I ^ (∑ index, (word.get index).val * (vector index).val ^ 2)

theorem binaryWordGauss_eq_prod (word : List R8) :
    binaryWordGauss word = ∏ index : Fin word.length,
      (1 + Complex.I ^ (word.get index).val) := by
  unfold binaryWordGauss
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (index : Fin word.length) (entry : Fin 2) =>
    Complex.I ^ ((word.get index).val * entry.val ^ 2))]
  simp [Fin.sum_univ_two]

theorem binaryWordGauss_countWord (ones threes fives sevens : ℕ) :
    binaryWordGauss (countWord ones threes fives sevens) =
      wordGauss ones threes fives sevens := by
  rw [binaryWordGauss_eq_prod, ← Fin.prod_ofFn]
  have hmap (word : List R8) :
      List.ofFn (fun index : Fin word.length => 1 + Complex.I ^ (word.get index).val) =
        word.map (fun value => 1 + Complex.I ^ value.val) := by
    calc
      _ = List.ofFn ((fun value : R8 => 1 + Complex.I ^ value.val) ∘ word.get) := rfl
      _ = (List.ofFn word.get).map (fun value => 1 + Complex.I ^ value.val) :=
        List.map_ofFn.symm
      _ = _ := by rw [List.ofFn_get]
  rw [hmap]
  simp only [countWord, List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate, wordGauss, pow_add]
  rw [show (1 : R8).val = 1 by decide, show (3 : R8).val = 3 by decide,
    show (5 : R8).val = 5 by decide, show (7 : R8).val = 7 by decide]
  norm_num [pow_succ, Complex.I_sq]
  ring

theorem countWord_add_perm (ones threes fives sevens extraOnes extraThrees extraFives
    extraSevens : ℕ) :
    (countWord (ones + extraOnes) (threes + extraThrees) (fives + extraFives)
      (sevens + extraSevens)).Perm
      (countWord ones threes fives sevens ++
        countWord extraOnes extraThrees extraFives extraSevens) := by
  apply List.perm_iff_count.mpr
  intro value
  simp only [countWord, List.count_append, List.count_replicate]
  split_ifs <;> omega

theorem normalizes_countWord_of_reduces {ones threes fives sevens : ℕ}
    (reduction : Reduces ones threes fives sevens) :
    Normalizes (wordMatrix (countWord ones threes fives sevens)) := by
  induction reduction with
  | ones ones =>
      have hgram : wordMatrix (countWord ones 0 0 0) = 1 := by
        ext row col
        simp [wordMatrix, countWord, Matrix.one_apply, Matrix.diagonal_apply,
          List.get_eq_getElem]
      rw [hgram]
      exact normalizes_one
  | @fivePair ones threes fives sevens reduction ih =>
      have hsource := countWord_add_perm 0 0 2 0 ones threes fives sevens
      have htarget := countWord_add_perm 2 0 0 0 ones threes fives sevens
      simp only [zero_add, add_comm 2] at hsource htarget
      apply normalizes_word_of_perm hsource
      apply normalizes_word_prefix (left := [5, 5]) (right := [1, 1])
        (Equiv.refl (Fin 2)) (pairWordCertificate 2 2)
      exact normalizes_word_of_perm htarget.symm ih
  | @sevenPair ones threes fives sevens reduction ih =>
      have hsource := countWord_add_perm 0 0 0 2 ones threes fives sevens
      have htarget := countWord_add_perm 0 2 0 0 ones threes fives sevens
      simp only [zero_add, add_comm 2] at hsource htarget
      apply normalizes_word_of_perm hsource
      apply normalizes_word_prefix (left := [7, 7]) (right := [3, 3])
        (Equiv.refl (Fin 2)) (pairWordCertificate 3 3)
      exact normalizes_word_of_perm htarget.symm ih
  | @mixedPair ones threes fives sevens reduction ih =>
      have hsource := countWord_add_perm 0 0 1 1 ones threes fives sevens
      have htarget := countWord_add_perm 1 1 0 0 ones threes fives sevens
      simp only [zero_add, add_comm 1] at hsource htarget
      apply normalizes_word_of_perm hsource
      apply normalizes_word_prefix (left := [5, 7]) (right := [1, 3])
        (Equiv.refl (Fin 2)) (pairWordCertificate 2 3)
      exact normalizes_word_of_perm htarget.symm ih
  | @fourThrees ones threes fives sevens reduction ih =>
      have hsource := countWord_add_perm 0 4 0 0 ones threes fives sevens
      have htarget := countWord_add_perm 4 0 0 0 ones threes fives sevens
      simp only [zero_add, add_comm 4] at hsource htarget
      apply normalizes_word_of_perm hsource
      apply normalizes_word_prefix (left := [3, 3, 3, 3]) (right := [1, 1, 1, 1])
        (Equiv.refl (Fin 4)) quaternionWordCertificate
      exact normalizes_word_of_perm htarget.symm ih

theorem normalizes_countWord_of_det_gauss (ones threes fives sevens : ℕ)
    (hdet : wordDet ones threes fives sevens = 1)
    (hgauss : wordGauss ones threes fives sevens =
      (1 + Complex.I) ^ (ones + threes + fives + sevens)) :
    Normalizes (wordMatrix (countWord ones threes fives sevens)) :=
  normalizes_countWord_of_reduces (reduces_of_det_gauss ones threes fives sevens hdet hgauss)

theorem normalizes_countWord_of_det_binaryGauss (ones threes fives sevens : ℕ)
    (hdet : (wordMatrix (countWord ones threes fives sevens)).det = 1)
    (hgauss : binaryWordGauss (countWord ones threes fives sevens) =
      (1 + Complex.I) ^ (countWord ones threes fives sevens).length) :
    Normalizes (wordMatrix (countWord ones threes fives sevens)) := by
  rw [wordMatrix_countWord_det] at hdet
  rw [binaryWordGauss_countWord] at hgauss
  have hlength : (countWord ones threes fives sevens).length =
      ones + threes + fives + sevens := by simp [countWord, Nat.add_assoc]
  rw [hlength] at hgauss
  exact normalizes_countWord_of_det_gauss ones threes fives sevens hdet hgauss

#assert_standard_axioms normalizes_word_of_perm
#assert_standard_axioms normalizes_word_prefix
#assert_standard_axioms pairWordCertificate
#assert_standard_axioms quaternionWordCertificate
#assert_standard_axioms wordMatrix_countWord_det
#assert_standard_axioms binaryWordGauss_countWord
#assert_standard_axioms normalizes_countWord_of_reduces
#assert_standard_axioms normalizes_countWord_of_det_gauss
#assert_standard_axioms normalizes_countWord_of_det_binaryGauss

end UnimodularGenusClosure
