import SMSFormula.QuadraticComplement
import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalarCancellation

/-!
# Positive-definite rational reduction of the real differential mass

A positive-definite rational symmetric form admits a rational congruence to a
positive diagonal form.  The completed real congruence comparison then
transports total differential mass with the explicit determinant comparing
the independently fixed rational tangent bases.

The subsequent diagonal-to-identity change of variables is generally real,
not rational, and is deliberately not asserted here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Positive definiteness after scalar extension forces a rational matrix to
be nonsingular. -/
theorem rational_det_ne_zero_of_posDef_map_real
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hpos : (F.map (algebraMap ℚ ℝ)).PosDef) :
    F.det ≠ 0 := by
  intro hdet
  have hreal : (F.map (algebraMap ℚ ℝ)).det ≠ 0 :=
    hpos.det_pos.ne'
  apply hreal
  calc
    (F.map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) F.det :=
      (RingHom.map_det (algebraMap ℚ ℝ) F).symm
    _ = 0 := by rw [hdet, map_zero]

/-- A positive-definite rational symmetric matrix is rationally congruent to
a diagonal matrix whose entries are all positive. -/
theorem exists_positive_gramMatrix_congr_diagonal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hpos : (F.map (algebraMap ℚ ℝ)).PosDef) :
    ∃ (d : Fin n → ℚ) (W : GL (Fin n) ℚ),
      (∀ i, 0 < d i) ∧
        Matrix.skewAdjointCongruenceForm F W = Matrix.diagonal d := by
  obtain ⟨d, W, _hd_ne, hdiag⟩ :=
    exists_gramMatrix_congr_diagonal F hF
      (rational_det_ne_zero_of_posDef_map_real F hpos) (by norm_num)
  refine ⟨d, W, ?_, hdiag⟩
  let Wℝ := rationalMatrixUnitReal W
  have hWinj : Function.Injective
      (Wℝ : Matrix (Fin n) (Fin n) ℝ).mulVec :=
    Matrix.mulVec_injective_of_isUnit Wℝ.isUnit
  have hcongrPos :
      ((Wℝ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        F.map (algebraMap ℚ ℝ) *
        (Wℝ : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    by
      simpa [Matrix.conjTranspose_apply] using
        hpos.conjTranspose_mul_mul_same hWinj
  have hdiagReal :
      (Matrix.diagonal d).map (algebraMap ℚ ℝ) =
        (Wℝ : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          F.map (algebraMap ℚ ℝ) *
          (Wℝ : Matrix (Fin n) (Fin n) ℝ) := by
    calc
      _ = ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
          (W : Matrix (Fin n) (Fin n) ℚ)).map
            (algebraMap ℚ ℝ) :=
        congrArg
          (fun A : Matrix (Fin n) (Fin n) ℚ =>
            A.map (algebraMap ℚ ℝ)) hdiag.symm
      _ = _ := map_skewAdjointCongruenceForm_real F W
  have hdiagPos :
      (Matrix.diagonal (fun i => (d i : ℝ))).PosDef := by
    have hdiagMapPos :
        ((Matrix.diagonal d).map (algebraMap ℚ ℝ)).PosDef := by
      rw [hdiagReal]
      exact hcongrPos
    simpa only [Matrix.diagonal_map
      (show (algebraMap ℚ ℝ) 0 = 0 by simp)] using hdiagMapPos
  intro i
  exact_mod_cast (Matrix.posDef_diagonal_iff.mp hdiagPos i)

/-- Positive rational diagonalization together with the exact total-mass
transport.  The congruent target is retained in rational form and is proved
equal to the displayed positive diagonal matrix. -/
theorem exists_positive_diagonal_realDifferentialMeasure_mass
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hpos : (F.map (algebraMap ℚ ℝ)).PosDef) :
    ∃ (d : Fin n → ℚ) (W : GL (Fin n) ℚ),
      (∀ i, 0 < d i) ∧
      Matrix.skewAdjointCongruenceForm F W = Matrix.diagonal d ∧
      specialFormPreservingSmoothRealDifferentialMeasure F hF
          (rational_det_ne_zero_of_posDef_map_real F hpos) Set.univ =
        (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingSmoothRealDifferentialMeasure
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F
              (rational_det_ne_zero_of_posDef_map_real F hpos) W)
            Set.univ := by
  obtain ⟨d, W, hd, hdiag⟩ :=
    exists_positive_gramMatrix_congr_diagonal F hF hpos
  refine ⟨d, W, hd, hdiag, ?_⟩
  rw [specialFormPreservingSmoothRealDifferentialMeasure_congruence_univ,
    specialFormPreservingRealCongruenceHaarScalar_eq]

end PositiveDefiniteIntegralLattice
