import SMSFormula.RationalCliffordGeneralSpinLatticeRealSimilitude
import SMSFormula.RationalCliffordGeneralSpinSimilitudeDifferenceIsotropy
import SMSFormula.RationalDyadicHighRankIsotropy
import SMSFormula.RationalPadicHighRankIsotropy
import SMSFormula.RationalWeakApproximation

/-!
# Rational lattice general-Spin similitudes from local difference isotropy

For the positive-definite rational lattice form, the real localization of
`Q ⊕ -aQ` is isotropic whenever `a > 0`, because `a` becomes a real square.
Hasse--Minkowski therefore reduces realization of a positive rational
similitude to the corresponding p-adic isotropy statements.  This file makes
that reduction literal and leaves the p-adic `u`-invariant input exposed.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

namespace CliffordGeneralSpinIntrinsicPoint

/-- At every odd prime, the doubled form `Q ⊕ -aQ` attached to a rank at
least three rational lattice is isotropic.  Its dimension is at least six,
so the odd-prime high-rank isotropy theorem applies. -/
theorem differenceGramBlock_smul_gramIsotropic_padic_of_ne_two
    (hn : 3 ≤ n) (a : ℚˣ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    GramIsotropic
      ((differenceGramBlock
        (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)
        ((a : ℚ) •
          L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)).map
        (algebraMap ℚ ℚ_[p])) := by
  let A := L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ
  let M := differenceGramBlock A ((a : ℚ) • A)
  have hA_symm : A.IsSymm := by
    exact L.rationalQuadraticSpaceMatrix.form_symm.map (algebraMap ℚ ℚ)
  have hA_det : A.det ≠ 0 := by
    exact
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix_det_isUnit ℚ).ne_zero
  have hM_symm : M.IsSymm := by
    dsimp [M, differenceGramBlock]
    apply Matrix.IsSymm.submatrix
    exact hA_symm.fromBlocks (by simp) ((hA_symm.smul (a : ℚ)).neg)
  have hM_det : M.det ≠ 0 := by
    simp only [M, differenceGramBlock, Matrix.det_reindex_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_neg]
    exact mul_ne_zero hA_det
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (pow_ne_zero _ a.ne_zero) hA_det))
  exact gramIsotropic_padic_of_rat_of_five_le hp (by omega) M hM_symm hM_det

/-- At the dyadic prime, the same doubled lattice form is isotropic in every
rank at least three.  Its dimension is at least six, and the
modulo-eight high-rank theorem includes all bad integral coefficients. -/
theorem differenceGramBlock_smul_gramIsotropic_dyadic
    (hn : 3 ≤ n) (a : ℚˣ) :
    GramIsotropic
      ((differenceGramBlock
        (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)
        ((a : ℚ) •
          L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)).map
        (algebraMap ℚ ℚ_[2])) := by
  let A := L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ
  let M := differenceGramBlock A ((a : ℚ) • A)
  have hA_symm : A.IsSymm := by
    exact L.rationalQuadraticSpaceMatrix.form_symm.map (algebraMap ℚ ℚ)
  have hA_det : A.det ≠ 0 := by
    exact
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix_det_isUnit ℚ).ne_zero
  have hM_symm : M.IsSymm := by
    dsimp [M, differenceGramBlock]
    apply Matrix.IsSymm.submatrix
    exact hA_symm.fromBlocks (by simp) ((hA_symm.smul (a : ℚ)).neg)
  have hM_det : M.det ≠ 0 := by
    simp only [M, differenceGramBlock, Matrix.det_reindex_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_neg]
    exact mul_ne_zero hA_det
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (pow_ne_zero _ a.ne_zero) hA_det))
  exact gramIsotropic_dyadic_of_rat_of_five_le (by omega) M hM_symm hM_det

/-- A positive rational unit is a literal intrinsic general-Spin similitude
once all p-adic scalar extensions of `Q ⊕ -aQ` are isotropic. -/
theorem exists_rationalCliffordGeneralSpin_similitude_eq_of_pos_of_padic_isotropic
    (hn : 3 ≤ n) (a : ℚˣ) (ha : 0 < (a : ℚ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      GramIsotropic
        ((differenceGramBlock
          (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)
          ((a : ℚ) •
            L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)).map
          (algebraMap ℚ ℚ_[p]))) :
    ∃ x : L.rationalQuadraticSpaceMatrix.RationalCliffordGeneralSpinGroup,
      similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ x = a := by
  letI : NeZero n := ⟨by omega⟩
  let A := L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ
  let M := differenceGramBlock A ((a : ℚ) • A)
  have hA_symm : A.IsSymm := by
    exact L.rationalQuadraticSpaceMatrix.form_symm.map (algebraMap ℚ ℚ)
  have hA_det : A.det ≠ 0 := by
    exact (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix_det_isUnit ℚ).ne_zero
  have hM_symm : M.IsSymm := by
    dsimp [M, differenceGramBlock]
    apply Matrix.IsSymm.submatrix
    exact hA_symm.fromBlocks (by simp) ((hA_symm.smul (a : ℚ)).neg)
  have hM_det : M.det ≠ 0 := by
    simp only [M, differenceGramBlock, Matrix.det_reindex_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_neg]
    exact mul_ne_zero hA_det
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (pow_ne_zero _ a.ne_zero) hA_det))
  have ha_real : IsSquare ((a : ℚ) : ℝ) := by
    refine ⟨Real.sqrt (a : ℚ), ?_⟩
    simpa [pow_two] using (Real.sq_sqrt
      (show (0 : ℝ) ≤ (a : ℚ) by exact_mod_cast le_of_lt ha)).symm
  have hreal : GramIsotropic (M.map (algebraMap ℚ ℝ)) := by
    have h := gramIsotropic_differenceGramBlock_smul_of_isSquare
      (A.map (algebraMap ℚ ℝ))
      (hA_symm.map (algebraMap ℚ ℝ))
      (by
        rw [show (A.map (algebraMap ℚ ℝ)).det =
          algebraMap ℚ ℝ A.det by
            simpa using (RingHom.map_det (algebraMap ℚ ℝ) A).symm]
        exact Rat.cast_ne_zero.mpr hA_det)
      (by norm_num) ((a : ℚ) : ℝ) (by exact_mod_cast a.ne_zero) ha_real
    change GramIsotropic
      ((differenceGramBlock A ((a : ℚ) • A)).map (algebraMap ℚ ℝ))
    rw [differenceGramBlock_map]
    rw [show (((a : ℚ) • A).map (algebraMap ℚ ℝ)) =
      ((a : ℚ) : ℝ) • A.map (algebraMap ℚ ℝ) by
        ext i j
        simp]
    exact h
  have hM : GramIsotropic M :=
    Rat.gramIsotropic_rat_of_real_and_padic (by omega) M hM_symm hM_det hreal
      (by simpa [M] using hpadic)
  exact exists_similitude_eq_of_differenceGramBlock_smul_isotropic
    L.rationalQuadraticSpaceMatrix ℚ a hM

/-- For a positive rational unit, the only local hypothesis still needed to
realize it as an intrinsic general-Spin similitude is isotropy of the doubled
form over `ℚ₂`.  Every odd-prime localization is discharged by the
preceding theorem. -/
theorem exists_rationalCliffordGeneralSpin_similitude_eq_of_pos_of_dyadic_isotropic
    (hn : 3 ≤ n) (a : ℚˣ) (ha : 0 < (a : ℚ))
    (hdyadic :
      GramIsotropic
        ((differenceGramBlock
          (L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)
          ((a : ℚ) •
            L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℚ)).map
          (algebraMap ℚ ℚ_[2]))) :
    ∃ x : L.rationalQuadraticSpaceMatrix.RationalCliffordGeneralSpinGroup,
      similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ x = a := by
  apply exists_rationalCliffordGeneralSpin_similitude_eq_of_pos_of_padic_isotropic
    L hn a ha
  intro p hpprime
  by_cases hp : p = 2
  · subst p
    simpa using hdyadic
  · exact differenceGramBlock_smul_gramIsotropic_padic_of_ne_two
      L hn a p hp

/-- Every positive rational unit is the similitude of a literal rational
intrinsic general-Spin point for the positive-definite lattice form. -/
theorem exists_rationalCliffordGeneralSpin_similitude_eq_of_pos
    (hn : 3 ≤ n) (a : ℚˣ) (ha : 0 < (a : ℚ)) :
    ∃ x : L.rationalQuadraticSpaceMatrix.RationalCliffordGeneralSpinGroup,
      similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ x = a := by
  apply exists_rationalCliffordGeneralSpin_similitude_eq_of_pos_of_dyadic_isotropic
    L hn a ha
  exact differenceGramBlock_smul_gramIsotropic_dyadic L hn a

/-- The rational similitude image of the positive-definite lattice intrinsic
general-Spin group is exactly the positive rational units. -/
theorem range_rationalCliffordGeneralSpinSimilitudeHom_eq_positive
    (hn : 3 ≤ n) :
    (similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ).range =
      positiveRationalUnitsSubgroup := by
  apply le_antisymm
  · exact range_rationalCliffordGeneralSpinSimilitudeHom_le_positive L
  · intro a ha
    exact exists_rationalCliffordGeneralSpin_similitude_eq_of_pos L hn a ha

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
