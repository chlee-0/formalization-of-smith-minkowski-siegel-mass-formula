import SMSFormula.RationalCliffordSpinCandidateIntegralReflectionWordLift

/-!
# Integral Cartan--Dieudonne generation over odd p-adic integers

The recursive complement word lift closes the rank induction: every
isometry of a symmetric unimodular form over `Z_p`, for odd `p`, is a word in
unit-norm integral reflections.  The construction records the sufficient
length bound `2 * rank`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- Every integral isometry of an odd-prime symmetric unimodular form is an
evaluated word of unit-norm reflections, of length at most twice the rank. -/
theorem LocalPadicIntegralUnimodularForm.exists_unitReflectionWord_eval_eq
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm) :
    ∃ xs : U.UnitReflectionWord,
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U xs = g ∧
        xs.length ≤ 2 * U.rank := by
  by_cases hzero : U.rank = 0
  · refine ⟨[], ?_, by simp [hzero]⟩
    apply DFunLike.coe_injective
    funext z
    haveI : Subsingleton (Fin U.rank → ℤ_[p]) := by
      rw [hzero]
      infer_instance
    exact Subsingleton.elim _ _
  · letI : NeZero U.rank := ⟨hzero⟩
    obtain ⟨x⟩ := U.unitVector_nonempty hpodd
    let a := U.reflectionAlignmentAt hpodd g x
    let corrected := U.reflectionCorrectionAt hpodd g x
    have hfix : corrected x = x :=
      U.reflectionCorrectionAt_apply_self hpodd g x
    let U' := U.orthogonalUnimodularForm x x.property
    let restricted :=
      U.orthogonalCoordinateRestriction hpodd x x.property corrected hfix
    obtain ⟨ys, hys, hlen⟩ :=
      LocalPadicIntegralUnimodularForm.exists_unitReflectionWord_eval_eq
        U' hpodd restricted
    let lifted :=
      LocalPadicIntegralUnimodularForm.UnitReflectionWord.liftOrthogonal
        U x x.property ys
    let tail := a.inverseWord
    refine ⟨lifted ++ tail, ?_, ?_⟩
    · rw [LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_append,
        show LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
            lifted = corrected by
          exact
            LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_liftOrthogonal_eq_of_fixed
              U hpodd x x.property corrected hfix ys hys,
        show LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U
            tail = a.correction.symm by
          exact a.eval_inverseWord]
      apply DFunLike.coe_injective
      funext z
      exact a.correction.toLinearEquiv.symm_apply_apply (g z)
    · have hdim := U.orthogonalUnimodularForm_rank_add_one x x.property
      have halen : tail.length ≤ 2 := by
        change a.inverseWord.length ≤ 2
        rw [a.length_inverseWord]
        exact a.length_le_two
      rw [List.length_append]
      change lifted.length + tail.length ≤ 2 * U.rank
      rw [LocalPadicIntegralUnimodularForm.UnitReflectionWord.length_liftOrthogonal]
      calc
        ys.length + tail.length ≤ 2 * U'.rank + 2 :=
          Nat.add_le_add hlen halen
        _ = 2 * U.rank := by
          dsimp only [U']
          omega
termination_by U.rank
decreasing_by
  have hdim := U.orthogonalUnimodularForm_rank_add_one x x.property
  omega

/-- Unbounded reflection-generation endpoint used by later spinor-norm
bookkeeping. -/
theorem LocalPadicIntegralUnimodularForm.isGeneratedByUnitReflections
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm) :
    U.IsGeneratedByUnitReflections g := by
  obtain ⟨xs, hxs, _hlen⟩ := U.exists_unitReflectionWord_eval_eq hpodd g
  exact ⟨xs, hxs⟩

end PositiveDefiniteIntegralLattice
