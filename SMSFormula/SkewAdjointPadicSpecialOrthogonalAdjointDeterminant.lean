import SMSFormula.AdelicProperFinitePresentation
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter

/-!
# The p-adic special-orthogonal adjoint determinant

For a nonsingular symmetric rational form, multiplication by the scalar
extended form matrix identifies skew-adjoint matrices with skew-symmetric
matrices.  Under this identification, conjugation by an orthogonal matrix is
ordinary congruence.  The general congruence determinant character therefore
shows that the adjoint action of every determinant-one orthogonal matrix has
determinant one.

The final theorem applies the existing arbitrary-linear-coordinate transport
formula to show that this adjoint action preserves the fixed p-adic
skew-adjoint coordinate Haar measure.  This is the local linear input for
right translation on the nonlinear `SO` charts; by itself it does not give
right invariance of the glued group measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

open PositiveDefiniteIntegralLattice

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance skewAdjointPadicSpecialOrthogonalAdjointMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicSpecialOrthogonalAdjointBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The p-adic adjoint action of a special-orthogonal matrix, constructed by
transporting skew-symmetric congruence through `H ↦ F_p H`. -/
def skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
      p F hF hdet).trans
    ((skewSymmetricPadicCongruenceContinuousLinearEquiv
      p g.1.1).trans
        (skewAdjointPadicSkewSymmetricContinuousLinearEquiv
          p F hF hdet).symm)

@[simp]
theorem coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := Fin n)) :
    ((skewAdjointPadicSkewSymmetricContinuousLinearEquiv
        p F hF hdet).symm Y : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (F.map (algebraMap ℚ ℚ_[p]))⁻¹ *
        (Y : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  rfl

/-- The transported action is literal matrix conjugation `H ↦ g⁻¹ H g`. -/
@[simp]
theorem coe_skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g H : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])⁻¹ *
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (g.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  let Fp : Matrix (Fin n) (Fin n) ℚ_[p] :=
    F.map (algebraMap ℚ ℚ_[p])
  let W : GL (Fin n) ℚ_[p] := g.1.1
  have hFpdet : IsUnit Fp.det :=
    isUnit_iff_ne_zero.mpr (skewAdjointPadicForm_det_ne_zero p F hdet)
  have hWunit :
      IsUnit (W : Matrix (Fin n) (Fin n) ℚ_[p]) :=
    Units.isUnit W
  have hWdet :
      IsUnit (W : Matrix (Fin n) (Fin n) ℚ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hWunit
  have hWinv :
      (W : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
    exact Matrix.mul_nonsing_inv _ hWdet
  have htransport :
      Fp⁻¹ * (W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp =
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    calc
      Fp⁻¹ * (W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp =
          Fp⁻¹ * (W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp * 1 := by
            rw [Matrix.mul_one]
      _ = Fp⁻¹ * (W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp *
          ((W : Matrix (Fin n) (Fin n) ℚ_[p]) *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p])) := by
              rw [hWinv]
      _ = Fp⁻¹ *
          ((W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp *
            (W : Matrix (Fin n) (Fin n) ℚ_[p])) *
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
                noncomm_ring
      _ = Fp⁻¹ * Fp *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
            rw [g.1.2]
      _ = (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) := by
        rw [Matrix.nonsing_inv_mul Fp hFpdet, Matrix.one_mul]
  simp only [skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv,
    ContinuousLinearEquiv.trans_apply,
    coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_apply,
    skewSymmetricPadicCongruenceContinuousLinearEquiv_apply,
    coe_skewSymmetricPadicCongruenceEndomorphism_apply,
    coe_skewAdjointPadicSkewSymmetricContinuousLinearEquiv_symm_apply]
  change
    Fp⁻¹ *
        ((W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ *
          (Fp * (H : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (W : Matrix (Fin n) (Fin n) ℚ_[p])) =
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (W : Matrix (Fin n) (Fin n) ℚ_[p])
  calc
    Fp⁻¹ *
        ((W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ *
          (Fp * (H : Matrix (Fin n) (Fin n) ℚ_[p])) *
            (W : Matrix (Fin n) (Fin n) ℚ_[p])) =
      (Fp⁻¹ * (W : Matrix (Fin n) (Fin n) ℚ_[p])ᵀ * Fp) *
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) *
          (W : Matrix (Fin n) (Fin n) ℚ_[p]) := by
            noncomm_ring
    _ = _ := by rw [htransport]

/-- The determinant of p-adic special-orthogonal conjugation on the
skew-adjoint Lie algebra is one. -/
theorem det_skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    LinearMap.det
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g).toLinearMap = 1 := by
  let E := skewAdjointPadicSkewSymmetricContinuousLinearEquiv
    p F hF hdet
  let C := skewSymmetricPadicCongruenceContinuousLinearEquiv p g.1.1
  have hconj :
      LinearEquiv.det (E.toLinearEquiv.trans
          (C.toLinearEquiv.trans E.symm.toLinearEquiv)) =
        LinearEquiv.det C.toLinearEquiv := by
    exact LinearEquiv.det_conj C.toLinearEquiv E.symm.toLinearEquiv
  have hconj' :
      LinearMap.det
          (E.toLinearEquiv.trans
            (C.toLinearEquiv.trans E.symm.toLinearEquiv)).toLinearMap =
        LinearMap.det C.toLinearMap := by
    have hval := congrArg (fun z : ℚ_[p]ˣ ↦ (z : ℚ_[p])) hconj
    simpa only [LinearEquiv.coe_det] using hval
  change LinearMap.det
      (E.toLinearEquiv.trans
        (C.toLinearEquiv.trans E.symm.toLinearEquiv)).toLinearMap = 1
  rw [hconj']
  change LinearMap.det
      (skewSymmetricPadicCongruenceEndomorphism
        p (g.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])).toLinearMap = 1
  rw [det_skewSymmetricPadicCongruenceEndomorphism_eq_det_pow]
  have hgdet :
      Matrix.det (g.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 :=
    (mem_specialFormPreservingMatrixSubgroup_iff
      (F.map (algebraMap ℚ ℚ_[p])) g.1).mp g.2
  rw [hgdet, one_pow]

/-- Special-orthogonal conjugation preserves the fixed p-adic skew-adjoint
coordinate Haar measure. -/
theorem map_skewAdjointPadicCoordinateMeasure_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g)
        (skewAdjointPadicCoordinateMeasure F p) =
      skewAdjointPadicCoordinateMeasure F p := by
  rw [map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det,
    det_skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv_eq_one,
    nnnorm_one, inv_one, one_smul]

end Matrix
