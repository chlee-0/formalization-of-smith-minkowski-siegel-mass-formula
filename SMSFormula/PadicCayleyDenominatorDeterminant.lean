import SMSFormula.PadicCayleyDenominatorConjugation
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter

/-!
# Determinant of the p-adic Cayley denominator action

For a symmetric nonsingular rational form, the existing equivalence
`H ↦ F_p H` conjugates the intrinsic unscaled Cayley denominator action to
skew-symmetric congruence by `(1-X)⁻¹`. The general congruence determinant
formula therefore evaluates the intrinsic determinant exactly.

This file does not evaluate the full left-trivialized determinant, take norms,
pull back determinant forms, transport measures, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

/-- The intrinsic unscaled Cayley denominator action has determinant
`det((1-X)⁻¹)^(n-1)`. -/
theorem
    det_skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism_eq_det_inv_pow
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
          F p X hX).toLinearMap =
      Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹ ^ (n - 1) := by
  let A : Matrix (Fin n) (Fin n) ℚ_[p] :=
    1 - (X : Matrix (Fin n) (Fin n) ℚ_[p])
  have hAunit : IsUnit A := hX
  have hAinvUnit : IsUnit A⁻¹ :=
    Matrix.isUnit_nonsing_inv_iff.mpr hAunit
  have hAinvDetUnit : IsUnit A⁻¹.det :=
    (Matrix.isUnit_iff_isUnit_det A⁻¹).mp hAinvUnit
  have hAinvDet : A⁻¹.det ≠ 0 := hAinvDetUnit.ne_zero
  let W : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A⁻¹ hAinvDet
  let E :=
    skewAdjointPadicSkewSymmetricContinuousLinearEquiv
      p F hF hdet
  let U :=
    skewAdjointPadicCayleyLeftTrivializedDenominatorEndomorphism
      F p X hX
  let C :=
    skewSymmetricPadicCongruenceEndomorphism p A⁻¹
  have hcomm :
      E.toContinuousLinearMap.comp U =
        C.comp E.toContinuousLinearMap := by
    exact skewAdjointPadicCayleyDenominatorEndomorphism_conjugation
      p F hF hdet X hX
  have hconj :
      E.toLinearEquiv.toLinearMap.comp
          (U.toLinearMap.comp E.symm.toLinearEquiv.toLinearMap) =
        C.toLinearMap := by
    apply LinearMap.ext
    intro Y
    have hY :=
      congrArg (fun T => T (E.symm Y)) hcomm
    simpa [LinearMap.comp_apply] using hY
  calc
    LinearMap.det U.toLinearMap =
        LinearMap.det C.toLinearMap := by
      calc
        LinearMap.det U.toLinearMap =
            LinearMap.det
              (E.toLinearEquiv.toLinearMap.comp
                (U.toLinearMap.comp
                  E.symm.toLinearEquiv.toLinearMap)) := by
          simp
        _ = LinearMap.det C.toLinearMap :=
          congrArg LinearMap.det hconj
    _ = Matrix.det (W : Matrix (Fin n) (Fin n) ℚ_[p]) ^ (n - 1) :=
      det_skewSymmetricPadicCongruenceEndomorphism_eq_det_pow p n W
    _ = Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))⁻¹ ^ (n - 1) := by
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

end Matrix
