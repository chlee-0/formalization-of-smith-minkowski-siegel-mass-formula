import SMSFormula.SkewAdjointPadicSpecialOrthogonalAdjointDeterminant
import SMSFormula.PadicCayleyTranslatedChartDifferentialMeasure

/-!
# Special-orthogonal adjoint symmetry of p-adic Cayley coordinates

Conjugation by a p-adic special-orthogonal point preserves the exact Cayley
source and its determinant density.  The ambient adjoint equivalence therefore
restricts to a homeomorphism of the source subtype.  The Cayley transform is
equivariant for this action.

This file contains only algebra, topology, and pointwise density identities.
Measure preservation and right translation of target charts are treated in
subsequent modules.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

open PositiveDefiniteIntegralLattice

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The Cayley denominator transforms by literal matrix conjugation under the
p-adic special-orthogonal adjoint action. -/
theorem one_sub_skewAdjointPadicSpecialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    1 -
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g X : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹ *
        (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) *
          (g.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  let W : GL (Fin n) ℚ_[p] := g.1.1
  have hWunit : IsUnit (W : Matrix (Fin n) (Fin n) ℚ_[p]) :=
    Units.isUnit W
  have hWdet : IsUnit (W : Matrix (Fin n) (Fin n) ℚ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hWunit
  have hWinv :
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (W : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 :=
    Matrix.nonsing_inv_mul _ hWdet
  rw [coe_skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv_apply]
  change
    1 - (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) * W =
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) * W
  calc
    1 - (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) * W =
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * W -
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) * W := by
            rw [hWinv]
    _ = _ := by noncomm_ring

/-- The determinant of the Cayley denominator is invariant under the p-adic
special-orthogonal adjoint action. -/
theorem det_one_sub_skewAdjointPadicSpecialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Matrix.det
        (1 -
          (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
            p n F hF hdet g X : Matrix (Fin n) (Fin n) ℚ_[p])) =
      Matrix.det (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])) := by
  rw [one_sub_skewAdjointPadicSpecialOrthogonalAdjoint p n F hF hdet g X]
  exact Matrix.det_conj' (Units.isUnit g.1.1) _

/-- Special-orthogonal adjoint conjugation preserves the exact inverse-Cayley
source, in both directions. -/
theorem skewAdjointPadicSpecialOrthogonalAdjoint_mem_cayleySource_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g X ∈ skewAdjointPadicCayleySource F p ↔
      X ∈ skewAdjointPadicCayleySource F p := by
  change
    IsUnit
        (1 -
          (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
            p n F hF hdet g X : Matrix (Fin n) (Fin n) ℚ_[p])) ↔
      IsUnit (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    det_one_sub_skewAdjointPadicSpecialOrthogonalAdjoint
      p n F hF hdet g X]

/-- The ambient adjoint equivalence restricted to the exact p-adic Cayley
source. -/
def skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleySource F p ≃ₜ
      skewAdjointPadicCayleySource F p where
  toFun X :=
    ⟨skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g X.1,
      (skewAdjointPadicSpecialOrthogonalAdjoint_mem_cayleySource_iff
        p n F hF hdet g X.1).2 X.2⟩
  invFun Y :=
    ⟨(skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g).symm Y.1, by
      apply
        (skewAdjointPadicSpecialOrthogonalAdjoint_mem_cayleySource_iff
          p n F hF hdet g
          ((skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
            p n F hF hdet g).symm Y.1)).1
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact Y.2⟩
  left_inv X := by simp
  right_inv X := by simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g).symm.continuous.comp continuous_subtype_val

@[simp]
theorem coe_skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
      p n F hF hdet g X).1 =
      skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g X.1 :=
  rfl

/-- The full Cayley-coordinate Jacobian density is invariant under the p-adic
special-orthogonal adjoint action. -/
theorem skewAdjointPadicCayleyCoordinateJacobianDensityENNReal_adjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g X) =
      skewAdjointPadicCayleyCoordinateJacobianDensityENNReal p n F X := by
  simp only [skewAdjointPadicCayleyCoordinateJacobianDensityENNReal,
    skewAdjointPadicCayleyCoordinateJacobianDensity]
  rw [det_one_sub_skewAdjointPadicSpecialOrthogonalAdjoint
    p n F hF hdet g X]

/-- The reciprocal differential density on the exact source is invariant
under the restricted adjoint homeomorphism. -/
theorem skewAdjointPadicCayleySourceDifferentialDensityENNReal_adjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
        (skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hF hdet g X) =
      skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F X := by
  simp only [skewAdjointPadicCayleySourceDifferentialDensityENNReal,
    coe_skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph_apply]
  rw [skewAdjointPadicCayleyCoordinateJacobianDensityENNReal_adjoint
    p n F hF hdet g X.1]

/-- The p-adic Cayley transform intertwines special-orthogonal adjoint
conjugation on its source with group conjugation on its target. -/
theorem padicCayleyForwardMatrix_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleySource F p) :
    padicCayleyForwardMatrix p
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g X.1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹ *
        padicCayleyForwardMatrix p
          (X.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (g.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  let W : Matrix (Fin n) (Fin n) ℚ_[p] := g.1.1
  let Y : Matrix (Fin n) (Fin n) ℚ_[p] :=
    skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
      p n F hF hdet g X.1
  let B : Matrix (Fin n) (Fin n) ℚ_[p] := 1 - (X.1 : Matrix _ _ ℚ_[p])
  let D : Matrix (Fin n) (Fin n) ℚ_[p] := 1 - Y
  have hWunit : IsUnit W := Units.isUnit g.1.1
  have hWdet : IsUnit W.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hWunit
  have hWmul : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv _ hWdet
  have hWinv : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul _ hWdet
  have hBunit : IsUnit B := X.2
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hBunit
  have hBmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hD : D = W⁻¹ * B * W := by
    exact one_sub_skewAdjointPadicSpecialOrthogonalAdjoint
      p n F hF hdet g X.1
  have hN : 1 + Y = W⁻¹ * (1 + (X.1 : Matrix _ _ ℚ_[p])) * W := by
    dsimp [Y, W]
    rw [coe_skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv_apply]
    change
      1 + W⁻¹ * (X.1 : Matrix _ _ ℚ_[p]) * W =
        W⁻¹ * (1 + (X.1 : Matrix _ _ ℚ_[p])) * W
    calc
      1 + W⁻¹ * (X.1 : Matrix _ _ ℚ_[p]) * W =
          W⁻¹ * W + W⁻¹ * (X.1 : Matrix _ _ ℚ_[p]) * W := by
            rw [hWinv]
      _ = _ := by noncomm_ring
  have hDinv : D⁻¹ = W⁻¹ * B⁻¹ * W := by
    apply Matrix.inv_eq_right_inv
    rw [hD]
    calc
      (W⁻¹ * B * W) * (W⁻¹ * B⁻¹ * W) =
          W⁻¹ * B * (W * W⁻¹) * B⁻¹ * W := by noncomm_ring
      _ = W⁻¹ * (B * B⁻¹) * W := by rw [hWmul]; noncomm_ring
      _ = 1 := by rw [hBmul, Matrix.mul_one, hWinv]
  change (1 + Y) * D⁻¹ = W⁻¹ * ((1 + X.1) * B⁻¹) * W
  rw [hN, hDinv]
  calc
    (W⁻¹ * (1 + (X.1 : Matrix _ _ ℚ_[p])) * W) *
        (W⁻¹ * B⁻¹ * W) =
      W⁻¹ * (1 + (X.1 : Matrix _ _ ℚ_[p])) *
        (W * W⁻¹) * B⁻¹ * W := by noncomm_ring
    _ = W⁻¹ * ((1 + (X.1 : Matrix _ _ ℚ_[p])) * B⁻¹) * W := by
      rw [hWmul]
      noncomm_ring

end Matrix
