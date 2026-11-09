import SMSFormula.SkewSymmetricPadicCongruenceComposition

/-!
# Invertible p-adic skew-symmetric congruence

Congruence by a p-adic matrix unit is a continuous linear equivalence of the
skew-symmetric matrix model. Its inverse is congruence by the inverse matrix,
so the original congruence endomorphism has nonzero algebraic determinant.

This file does not evaluate that determinant or its norm, pull back a
determinant form, transport a measure, or glue charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Congruence by the identity matrix is the identity endomorphism. -/
@[simp]
theorem skewSymmetricPadicCongruenceEndomorphism_one :
    skewSymmetricPadicCongruenceEndomorphism p
        (1 : Matrix ι ι ℚ_[p]) =
      ContinuousLinearMap.id ℚ_[p]
        (skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) := by
  apply ContinuousLinearMap.ext
  intro Y
  apply Subtype.ext
  simp

/-- Congruence by a matrix unit followed by congruence by its inverse is the
identity endomorphism. -/
theorem skewSymmetricPadicCongruenceEndomorphism_inv_comp
    (W : GL ι ℚ_[p]) :
    (skewSymmetricPadicCongruenceEndomorphism
        p (W⁻¹ : Matrix ι ι ℚ_[p])).comp
      (skewSymmetricPadicCongruenceEndomorphism
        p (W : Matrix ι ι ℚ_[p])) =
      ContinuousLinearMap.id ℚ_[p]
        (skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) := by
  rw [← skewSymmetricPadicCongruenceEndomorphism_mul,
    ← Matrix.GeneralLinearGroup.coe_inv,
    ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel W,
    Matrix.GeneralLinearGroup.coe_one]
  exact skewSymmetricPadicCongruenceEndomorphism_one p

/-- Congruence by the inverse of a matrix unit followed by congruence by the
unit itself is the identity endomorphism. -/
theorem skewSymmetricPadicCongruenceEndomorphism_comp_inv
    (W : GL ι ℚ_[p]) :
    (skewSymmetricPadicCongruenceEndomorphism
        p (W : Matrix ι ι ℚ_[p])).comp
      (skewSymmetricPadicCongruenceEndomorphism
        p (W⁻¹ : Matrix ι ι ℚ_[p])) =
      ContinuousLinearMap.id ℚ_[p]
        (skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) := by
  rw [← skewSymmetricPadicCongruenceEndomorphism_mul,
    ← Matrix.GeneralLinearGroup.coe_inv,
    ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel W,
    Matrix.GeneralLinearGroup.coe_one]
  exact skewSymmetricPadicCongruenceEndomorphism_one p

/-- Congruence by a p-adic matrix unit as a continuous linear equivalence of
skew-symmetric matrices. -/
def skewSymmetricPadicCongruenceContinuousLinearEquiv
    (W : GL ι ℚ_[p]) :
    skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) ≃L[ℚ_[p]]
      skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι) :=
  ContinuousLinearEquiv.mk
    (LinearEquiv.mk
      (skewSymmetricPadicCongruenceEndomorphism
        p (W : Matrix ι ι ℚ_[p])).toLinearMap
      (skewSymmetricPadicCongruenceEndomorphism
        p (W⁻¹ : Matrix ι ι ℚ_[p])).toLinearMap
      (fun Y => by
        exact congrArg (fun L => L Y)
          (skewSymmetricPadicCongruenceEndomorphism_inv_comp p W))
      (fun Y => by
        exact congrArg (fun L => L Y)
          (skewSymmetricPadicCongruenceEndomorphism_comp_inv p W)))
    (skewSymmetricPadicCongruenceEndomorphism
      p (W : Matrix ι ι ℚ_[p])).continuous
    (skewSymmetricPadicCongruenceEndomorphism
      p (W⁻¹ : Matrix ι ι ℚ_[p])).continuous

/-- The continuous linear equivalence applies as congruence by the unit. -/
@[simp]
theorem skewSymmetricPadicCongruenceContinuousLinearEquiv_apply
    (W : GL ι ℚ_[p])
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) :
    skewSymmetricPadicCongruenceContinuousLinearEquiv p W Y =
      skewSymmetricPadicCongruenceEndomorphism
        p (W : Matrix ι ι ℚ_[p]) Y :=
  rfl

/-- The inverse continuous linear equivalence applies as congruence by the
inverse matrix unit. -/
@[simp]
theorem skewSymmetricPadicCongruenceContinuousLinearEquiv_symm_apply
    (W : GL ι ℚ_[p])
    (Y : skewSymmetricMatricesSubmodule (R := ℚ_[p]) (ι := ι)) :
    (skewSymmetricPadicCongruenceContinuousLinearEquiv p W).symm Y =
      skewSymmetricPadicCongruenceEndomorphism
        p (W⁻¹ : Matrix ι ι ℚ_[p]) Y :=
  rfl

/-- Congruence by a p-adic matrix unit has nonzero algebraic determinant. -/
theorem det_skewSymmetricPadicCongruenceEndomorphism_ne_zero
    (W : GL ι ℚ_[p]) :
    LinearMap.det
        (skewSymmetricPadicCongruenceEndomorphism
          p (W : Matrix ι ι ℚ_[p])).toLinearMap ≠ 0 := by
  change LinearMap.det
      (skewSymmetricPadicCongruenceContinuousLinearEquiv
        p W).toLinearEquiv.toLinearMap ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

end Matrix
