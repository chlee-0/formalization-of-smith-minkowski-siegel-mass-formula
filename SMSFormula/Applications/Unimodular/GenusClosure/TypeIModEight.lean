import SMSFormula.Applications.Unimodular.GenusClosure.OddDiagonalization
import SMSFormula.Applications.Unimodular.GenusClosure.UnimodularBinaryGauss

noncomputable section

namespace UnimodularGenusClosure
open TypeIIModEightCertificates
open scoped BigOperators

theorem matrixNorm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equiv : ι ≃ κ) (gram : Matrix ι ι R4) (vector : ι → R4) :
    matrixNorm (Matrix.reindex equiv equiv gram) (vector ∘ equiv.symm) =
      matrixNorm gram vector := by
  simp only [matrixNorm, dotProduct, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.submatrix_apply, Function.comp_apply]
  rw [← equiv.sum_comp]
  apply Finset.sum_congr rfl
  intro row _
  simp only [Equiv.symm_apply_apply]
  rw [← equiv.sum_comp]
  simp

theorem binaryMatrixGauss_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (equiv : ι ≃ κ) (gram : Matrix ι ι R8) :
    binaryMatrixGauss (Matrix.reindex equiv equiv gram) = binaryMatrixGauss gram := by
  unfold binaryMatrixGauss
  rw [← (Equiv.arrowCongr equiv (Equiv.refl R2)).sum_comp]
  apply Finset.sum_congr rfl
  intro vector _
  have hmap : (Matrix.reindex equiv equiv gram).map modFour =
      Matrix.reindex equiv equiv (gram.map modFour) := rfl
  rw [hmap]
  exact congrArg quarticPhase (matrixNorm_reindex equiv (gram.map modFour)
    (fun index => bitLift (vector index)))

theorem normalizes_of_oddDiagonalizes {n : ℕ} (gram : Matrix (Fin n) (Fin n) R8)
    (hsymm : gram.IsSymm) (hdet : gram.det = 1)
    (hphase : binaryMatrixGauss gram = (1 + Complex.I) ^ n)
    (hdiag : OddDiagonalizes gram) : Normalizes gram := by
  obtain ⟨coefficients, hunits, ⟨certificate⟩⟩ := hdiag
  let word := List.ofFn coefficients
  let equiv : Fin word.length ≃ Fin n := finCongr (by simp [word])
  have hword : Matrix.reindex equiv equiv (wordMatrix word) =
      Matrix.diagonal coefficients := by
    ext row col
    simp [wordMatrix, Matrix.reindex_apply, Matrix.diagonal_apply, word, equiv,
      List.get_eq_getElem]
  have hwordUnits : ∀ value ∈ word, IsUnit value := by
    intro value hmem
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hmem
    exact hunits index
  have hwordDet : (wordMatrix word).det = 1 := by
    rw [← Matrix.det_reindex_self equiv, hword]
    exact certificate.det_eq.trans hdet
  have hwordGauss : binaryWordGauss word = (1 + Complex.I) ^ word.length := by
    rw [← binaryMatrixGauss_wordMatrix, ← binaryMatrixGauss_reindex equiv, hword,
      ← binaryMatrixGauss_eq_of_certificate hsymm certificate, hphase]
    simp [word]
  have hnormal := (normalizes_reindex_iff equiv (wordMatrix word)).mpr
    (normalizes_word_of_units_det_binaryGauss word hwordUnits hwordDet hwordGauss)
  rw [hword] at hnormal
  exact normalizes_of_certificate certificate hnormal

theorem normalizes_typeI_unimodular {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (htypeI : lattice.HasOddNorm) :
    Normalizes (lattice.pairingMatrix.map (Int.cast : ℤ → R8)) := by
  have hoddUnit : ∀ value : R8, IsUnit (2 * value + 1) := by decide
  have hsymm := lattice.form_symm.map (Int.cast : ℤ → R8)
  have hdet : (lattice.pairingMatrix.map (Int.cast : ℤ → R8)).det = 1 := by
    calc
      _ = (lattice.pairingMatrix.det : R8) := (Int.cast_det lattice.pairingMatrix).symm
      _ = 1 := by rw [show lattice.pairingMatrix.det = 1 from hunimodular]; rfl
  apply normalizes_of_oddDiagonalizes _ hsymm hdet (unimodular_binaryGauss lattice hunimodular)
  apply oddDiagonalizes_of_unit_diag _ hsymm (hdet ▸ isUnit_one)
  obtain ⟨pivot, hpivot⟩ := lattice.hasOddNorm_iff_exists_diag_odd.mp htypeI
  refine ⟨pivot, ?_⟩
  obtain ⟨integer, hinteger⟩ := hpivot
  change IsUnit (Int.cast (lattice.pairingMatrix pivot pivot) : R8)
  rw [hinteger]
  convert hoddUnit (integer : R8) using 1
  push_cast
  ring

#assert_standard_axioms binaryMatrixGauss_reindex
#assert_standard_axioms normalizes_of_oddDiagonalizes
#assert_standard_axioms normalizes_typeI_unimodular

end UnimodularGenusClosure
