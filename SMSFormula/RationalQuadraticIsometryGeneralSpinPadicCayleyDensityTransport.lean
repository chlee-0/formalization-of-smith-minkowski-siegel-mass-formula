import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTransport
import SMSFormula.PadicCayleyTranslatedChartDifferentialMeasure

/-!
# P-adic Cayley density transport across anisotropic presentations

Presentation conjugation preserves the exact Cayley denominator determinant
and therefore the reciprocal Cayley differential density.  No measure or
independently selected Spin chart is transported here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Presentation conjugation preserves the determinant of the Cayley
denominator. -/
theorem det_one_sub_blockToAmbientPadicSkewAdjointLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource
      (P.blockSpace hx).pairingMatrix p) :
    Matrix.det
        (1 - (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X.1 :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])) =
      Matrix.det (1 - (X.1 :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])) := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  rw [P.coe_blockToAmbientPadicSkewAdjointLinearEquiv_apply hx p]
  let Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] := X.1
  change Matrix.det (1 - M * Y * N) = Matrix.det (1 - Y)
  have hmat : 1 - M * Y * N = M * (1 - Y) * N := by
    calc
      1 - M * Y * N = M * N - M * Y * N := by rw [hMN]
      _ = M * (1 - Y) * N := by noncomm_ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul]
  have hdetMN := congrArg Matrix.det hMN
  simp only [Matrix.det_mul, Matrix.det_one] at hdetMN
  calc
    M.det * Matrix.det (1 - Y) * N.det =
        (M.det * N.det) * Matrix.det (1 - Y) := by ring
    _ = Matrix.det (1 - Y) := by rw [hdetMN, one_mul]

/-- Presentation conjugation preserves the reciprocal Cayley differential
density pointwise on the exact source. -/
theorem blockToAmbientPadicCayleySourceDifferentialDensityENNReal
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource
      (P.blockSpace hx).pairingMatrix p) :
    Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p (m + 1) V.pairingMatrix
        (P.blockToAmbientPadicCayleySourceHomeomorph hx p X) =
      Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p (m + 1) (P.blockSpace hx).pairingMatrix X := by
  unfold Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
  unfold Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
  unfold Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
  rw [P.blockToAmbientPadicCayleySourceHomeomorph_apply hx p,
    P.det_one_sub_blockToAmbientPadicSkewAdjointLinearEquiv hx p X]
  have hrank := LinearEquiv.finrank_eq
    (P.blockToAmbientSkewAdjointLinearEquiv hx)
  rw [hrank]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
