import SMSFormula.Applications.Unimodular.GenusClosure.OddSchur

noncomputable section

namespace UnimodularGenusClosure
open TypeIIModEightCertificates
open scoped BigOperators

def identityGramCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) : GramCongruenceCertificate gram gram :=
  ⟨1, 1, by simp, by simp, by simp⟩

theorem oddDiagonalizes_line_sum_by_card : ∀ rank : ℕ,
    ∀ (β : Type) [Fintype β] [DecidableEq β], Fintype.card β = rank →
    ∀ (tail : Matrix β β R8), tail.IsSymm → IsUnit tail.det →
    ∀ value : R8, IsUnit value → OddDiagonalizes (sumBlockMatrix (unitLine value) tail) := by
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
    intro β _ _ hcard tail hsymm hdet value hvalue
    classical
    by_cases hodd : ∃ pivot, IsUnit (tail pivot pivot)
    · obtain ⟨pivot, hpivot⟩ := hodd
      let chosen := lineEmbedding pivot
      let residual := splitResidual tail chosen
      have hhead : IsUnit (tail.submatrix chosen chosen).det := by
        simpa [chosen, lineEmbedding_head, Matrix.det_diagonal] using hpivot
      have cert := invertibleHeadSplitCertificate tail chosen hsymm hhead
      apply (oddDiagonalizes_reindex_iff
        (Equiv.sumCongr (Equiv.refl (Fin 1)) (splitIndexEquiv chosen).symm) _).mp
      rw [sumBlock_reindex_right]
      apply oddDiagonalizes_of_certificate
        (sumBlockCertificate (identityGramCertificate (unitLine value)) cert)
      rw [show tail.submatrix chosen chosen = unitLine (tail pivot pivot) from
        lineEmbedding_head tail pivot]
      apply oddDiagonalizes_sumBlock (oddDiagonalizes_unitLine value hvalue)
      exact ih _ (hcard ▸ splitRemainder_card_lt chosen) _ rfl residual
        (splitResidual_isSymm tail chosen hsymm)
        (splitResidual_det_isUnit tail chosen hsymm hhead hdet) _ hpivot
    · have heven : ∀ index, ¬ IsUnit (tail index index) := by
        simpa only [not_exists] using hodd
      cases isEmpty_or_nonempty β with
      | inl hempty =>
        letI := hempty
        have heq : sumBlockMatrix (unitLine value) tail =
            Matrix.diagonal (Sum.elim (fun _ : Fin 1 => value) (fun index : β => isEmptyElim index)) := by
          ext row col
          rcases row with row | row
          · rcases col with col | col
            · simp [unitLine, Matrix.diagonal_apply]
            · exact isEmptyElim col
          · exact isEmptyElim row
        rw [heq]
        apply oddDiagonalizes_diagonal
        intro index
        rcases index with index | index
        · exact hvalue
        · exact isEmptyElim index
      | inr hnonempty =>
        letI := hnonempty
        obtain ⟨pivot⟩ := hnonempty
        obtain ⟨partner, hpartner, hcross⟩ :=
          exists_unit_offdiag_of_det_isUnit tail hdet heven pivot
        let chosen := pairEmbedding pivot partner hpartner.symm
        let residual := splitResidual tail chosen
        have hhead : IsUnit (tail.submatrix chosen chosen).det := by
          rw [show tail.submatrix chosen chosen =
            !![tail pivot pivot, tail pivot partner; tail pivot partner, tail partner partner] from
            pairEmbedding_head tail hsymm pivot partner hpartner.symm]
          exact evenBinary_det_isUnit _ _ _ (heven pivot) (heven partner) hcross
        have cert := invertibleHeadSplitCertificate tail chosen hsymm hhead
        apply (oddDiagonalizes_reindex_iff
          (Equiv.sumCongr (Equiv.refl (Fin 1)) (splitIndexEquiv chosen).symm) _).mp
        rw [sumBlock_reindex_right]
        apply oddDiagonalizes_of_certificate
          (sumBlockCertificate (identityGramCertificate (unitLine value)) cert)
        apply (oddDiagonalizes_sumBlock_assoc _ _ _).mpr
        have htriple : OddDiagonalizes
            (sumBlockMatrix (unitLine value) (tail.submatrix chosen chosen)) := by
          rw [show tail.submatrix chosen chosen =
            !![tail pivot pivot, tail pivot partner; tail pivot partner, tail partner partner] from
            pairEmbedding_head tail hsymm pivot partner hpartner.symm]
          exact oddDiagonalizes_line_evenBinary _ _ _ _ hvalue (heven pivot) (heven partner) hcross
        obtain ⟨coefficients, hunits, ⟨tripleCert⟩⟩ := htriple
        apply oddDiagonalizes_of_certificate
          (sumBlockCertificate tripleCert (identityGramCertificate residual))
        apply oddDiagonalizes_three_lines_tail coefficients residual hunits
        exact ih _ (hcard ▸ splitRemainder_card_lt chosen) _ rfl residual
          (splitResidual_isSymm tail chosen hsymm)
          (splitResidual_det_isUnit tail chosen hsymm hhead hdet) _ (hunits (Sum.inl 0))

theorem oddDiagonalizes_of_unit_diag {ι : Type} [Fintype ι] [DecidableEq ι]
    (gram : Matrix ι ι R8) (hsymm : gram.IsSymm) (hdet : IsUnit gram.det)
    (hodd : ∃ pivot, IsUnit (gram pivot pivot)) : OddDiagonalizes gram := by
  classical
  obtain ⟨pivot, hpivot⟩ := hodd
  let chosen := lineEmbedding pivot
  have hhead : IsUnit (gram.submatrix chosen chosen).det := by
    simpa [chosen, lineEmbedding_head, Matrix.det_diagonal] using hpivot
  apply (oddDiagonalizes_reindex_iff (splitIndexEquiv chosen).symm _).mp
  apply oddDiagonalizes_of_certificate
    (invertibleHeadSplitCertificate gram chosen hsymm hhead)
  rw [show gram.submatrix chosen chosen = unitLine (gram pivot pivot) from
    lineEmbedding_head gram pivot]
  exact oddDiagonalizes_line_sum_by_card _ _ rfl _
    (splitResidual_isSymm gram chosen hsymm)
    (splitResidual_det_isUnit gram chosen hsymm hhead hdet) _ hpivot

#assert_standard_axioms oddDiagonalizes_line_sum_by_card
#assert_standard_axioms oddDiagonalizes_of_unit_diag

end UnimodularGenusClosure
