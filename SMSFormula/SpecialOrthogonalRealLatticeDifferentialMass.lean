import SMSFormula.SpecialOrthogonalRealPositiveDiagonalDifferentialMass
import SMSFormula.SpecialOrthogonalRealPositiveDefiniteReduction
import SMSFormula.SpecialOrthogonalRealLatticeReference

/-!
# Lattice real differential mass

The positive-diagonal Gamma formula is first restated in the actual matrix
rank.  Positive rational diagonalization of the lattice form then combines
the rational congruence determinant, the positive-diagonal-to-identity
determinant, and the arbitrary fixed-to-elementary identity determinant.

The diagonalization witnesses and all three determinant factors remain
literal.  No canonical diagonalization, reference-Haar comparison, or
Tamagawa specialization occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- Equality of rational forms transports the total mass, independently of
the proof terms certifying symmetry and nonsingularity. -/
private theorem specialFormPreservingSmoothRealDifferentialMeasure_univ_congr
    {n : ℕ} (F F' : Matrix (Fin n) (Fin n) ℚ) (hFF' : F = F')
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0) :
    specialFormPreservingSmoothRealDifferentialMeasure
        F hF hdet Set.univ =
      specialFormPreservingSmoothRealDifferentialMeasure
        F' hF' hdet' Set.univ := by
  subst F'
  rfl

/-- Rank-normalized positive-diagonal differential mass. -/
theorem positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma_rank
    (n : ℕ) [NeZero n] (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.diagonal d)
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) Set.univ =
      (↑((Real.toNNReal
        |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
        ((Real.toNNReal
          |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| :
            ℝ≥0∞) *
          ENNReal.ofReal
            ((2 : ℝ) ^ (n - 1) *
                Real.pi ^
                  (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + 3) / 4) /
              (∏ k ∈ Finset.range (n - 1),
                Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))) := by
  cases n with
  | zero =>
      exact (NeZero.ne 0 rfl).elim
  | succ m =>
      simpa using
        positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma
          m d hd

/-- A positive rational diagonalization evaluates the lattice real
differential mass with all three tangent determinant factors exposed. -/
theorem exists_concreteRealSpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
    {n : ℕ} [NeZero n] (L : PositiveDefiniteIntegralLattice n) :
    ∃ (d : Fin n → ℚ) (W : GL (Fin n) ℚ)
        (hd : ∀ i, 0 < d i),
      Matrix.skewAdjointCongruenceForm L.rationalFormMatrix W =
        Matrix.diagonal d ∧
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ =
        (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar
          L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) *
          ((↑((Real.toNNReal
            |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
            ((Real.toNNReal
              |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| :
                ℝ≥0∞) *
              ENNReal.ofReal
                ((2 : ℝ) ^ (n - 1) *
                    Real.pi ^
                      (((n - 1 : ℕ) : ℝ) *
                        (((n - 1 : ℕ) : ℝ) + 3) / 4) /
                  (∏ k ∈ Finset.range (n - 1),
                    Real.Gamma (((k + 2 : ℕ) : ℝ) / 2))))) := by
  have hpos :
      (L.rationalFormMatrix.map (algebraMap ℚ ℝ)).PosDef := by
    rw [L.rationalFormMatrix_map_real]
    exact L.form_posDef
  obtain ⟨d, W, hd, hdiag, hmass⟩ :=
    exists_positive_diagonal_realDifferentialMeasure_mass
      L.rationalFormMatrix (L.form_symm.map _) hpos
  refine ⟨d, W, hd, hdiag, ?_⟩
  have hmass' :
      specialFormPreservingSmoothRealDifferentialMeasure
          L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero Set.univ =
        (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar
            L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) *
          specialFormPreservingSmoothRealDifferentialMeasure
            (Matrix.diagonal d)
            (positiveDiagonalForm_isSymm d)
            (positiveDiagonalForm_det_ne_zero d hd)
            Set.univ := by
    calc
      _ =
          (↑((Real.toNNReal
            |Matrix.skewAdjointRealCongruenceDetScalar
              L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) *
            specialFormPreservingSmoothRealDifferentialMeasure
              (Matrix.skewAdjointCongruenceForm L.rationalFormMatrix W)
              (skewAdjointCongruenceForm_isSymm
                L.rationalFormMatrix (L.form_symm.map _) W)
              (skewAdjointCongruenceForm_det_ne_zero
                L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero W)
              Set.univ := hmass
      _ = _ := congrArg
        (fun x : ℝ≥0∞ =>
          (↑((Real.toNNReal
            |Matrix.skewAdjointRealCongruenceDetScalar
              L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) * x)
        (specialFormPreservingSmoothRealDifferentialMeasure_univ_congr
          (Matrix.skewAdjointCongruenceForm L.rationalFormMatrix W)
          (Matrix.diagonal d) hdiag
          (skewAdjointCongruenceForm_isSymm
            L.rationalFormMatrix (L.form_symm.map _) W)
          (skewAdjointCongruenceForm_det_ne_zero
            L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero W)
          (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd))
  rw [L.concreteRealSpecialOrthogonalDifferentialMeasure_univ]
  rw [
    hmass',
    positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma_rank
      n d hd
  ]

end PositiveDefiniteIntegralLattice
