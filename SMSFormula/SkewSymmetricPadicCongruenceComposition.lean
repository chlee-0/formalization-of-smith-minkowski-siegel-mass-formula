import SMSFormula.SkewSymmetricPadicDiagonalClosedDeterminant

/-!
# Composition of p-adic skew-symmetric congruence actions

Congruence by a matrix product is the composite of the two corresponding
congruence endomorphisms, in the order forced by transposition. Consequently,
their algebraic determinants multiply.

This file does not evaluate either determinant, take determinant norms, pull
back determinant forms, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Congruence by `C * D` is congruence by `C` followed by congruence by `D`. -/
theorem skewSymmetricPadicCongruenceEndomorphism_mul
    (C D : Matrix ι ι ℚ_[p]) :
    skewSymmetricPadicCongruenceEndomorphism p (C * D) =
      (skewSymmetricPadicCongruenceEndomorphism p D).comp
        (skewSymmetricPadicCongruenceEndomorphism p C) := by
  apply ContinuousLinearMap.ext
  intro Y
  apply Subtype.ext
  simp only [ContinuousLinearMap.comp_apply,
    coe_skewSymmetricPadicCongruenceEndomorphism_apply,
    Matrix.transpose_mul]
  noncomm_ring

/-- Algebraic determinants multiply under composition of skew-symmetric
congruence actions. -/
theorem det_skewSymmetricPadicCongruenceEndomorphism_mul
    (C D : Matrix ι ι ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism p (C * D)).toLinearMap =
      LinearMap.det
          (skewSymmetricPadicCongruenceEndomorphism p C).toLinearMap *
        LinearMap.det
          (skewSymmetricPadicCongruenceEndomorphism p D).toLinearMap := by
  rw [skewSymmetricPadicCongruenceEndomorphism_mul]
  change LinearMap.det
      ((skewSymmetricPadicCongruenceEndomorphism p D).toLinearMap.comp
        (skewSymmetricPadicCongruenceEndomorphism p C).toLinearMap) = _
  rw [LinearMap.det_comp, mul_comm]

end Matrix
