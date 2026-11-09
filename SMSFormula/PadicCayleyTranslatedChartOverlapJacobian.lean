import SMSFormula.PadicCayleyTranslatedChartOverlapTangent
import SMSFormula.PadicCayleyTranslatedChartJacobian
import SMSFormula.PadicCayleyLeftTrivializedDetInverse
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus
import SMSFormula.PadicCayleyTangentModulus

/-!
# Determinants and Jacobians of translated p-adic Cayley overlaps

At corresponding source coordinates `X` and `Y`, the intrinsic overlap
derivative is the equivalence `T_Y⁻¹ ∘ T_X`.  Its determinant is
therefore the quotient of the two left-trivialized Cayley determinants, and
the reverse determinant is its inverse.

For a symmetric nonsingular rational form, the nonnegative determinant norm
is the ratio of the coordinate Jacobian densities.  The scalar
Cayley tangent factor cancels, including at the dyadic place.  The same
identity is transported pointwise to the two exact translated target
subtypes.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The determinant of the intrinsic transition tangent equivalence is the
inverse target Cayley tangent determinant times the source determinant. -/
theorem det_skewAdjointPadicCayleyTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap =
      (LinearMap.det
        (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p Y hY).toLinearMap)⁻¹ *
        LinearMap.det
          (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X hX).toLinearMap := by
  change
    LinearMap.det
        ((Matrix.skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
          F p hF Y hY).symm.toLinearMap.comp
            (Matrix.skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
              F p hF X hX).toLinearMap) =
      _⁻¹ * _
  rw [LinearMap.det_comp]
  change
    LinearMap.det
          (Matrix.skewAdjointPadicCayleyLeftTrivializedInverse
            F p Y).toLinearMap *
        LinearMap.det
          (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X hX).toLinearMap =
      _⁻¹ * _
  rw [
    Matrix.det_skewAdjointPadicCayleyLeftTrivializedInverse_eq_inv
      F p hF Y hY]

/-- The determinant of the reverse intrinsic transition is the inverse of the
forward transition determinant. -/
theorem det_skewAdjointPadicCayleyTransitionTangentEquiv_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF Y X hY hX).toLinearMap =
      (LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap)⁻¹ := by
  rw [← skewAdjointPadicCayleyTransitionTangentEquiv_symm]
  exact LinearEquiv.det_coe_symm _

/-- The forward and reverse intrinsic transition determinants multiply to
one. -/
theorem det_skewAdjointPadicCayleyTransitionTangentEquiv_mul_reverse
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    LinearMap.det
          (skewAdjointPadicCayleyTransitionTangentEquiv
            F p hF X Y hX hY).toLinearMap *
        LinearMap.det
          (skewAdjointPadicCayleyTransitionTangentEquiv
            F p hF Y X hY hX).toLinearMap =
      1 := by
  rw [det_skewAdjointPadicCayleyTransitionTangentEquiv_symm
    F p hF X Y hX hY]
  have hdet :
      LinearMap.det
          (skewAdjointPadicCayleyTransitionTangentEquiv
            F p hF X Y hX hY).toLinearMap ≠ 0 := by
    rw [det_skewAdjointPadicCayleyTransitionTangentEquiv]
    exact mul_ne_zero
      (inv_ne_zero
        (Matrix.det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_ne_zero
          F p hF Y hY))
      (Matrix.det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_ne_zero
        F p hF X hX)
  exact mul_inv_cancel₀ hdet

/-- The nonnegative determinant norm of the intrinsic transition is the
source Cayley tangent norm times the inverse target tangent norm. -/
theorem nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap‖₊ =
      ‖LinearMap.det
        (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap‖₊ *
        ‖LinearMap.det
          (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p Y hY).toLinearMap‖₊⁻¹ := by
  rw [det_skewAdjointPadicCayleyTransitionTangentEquiv,
    nnnorm_mul, nnnorm_inv, mul_comm]

/-- The exact forward overlap tangent determinant has the generic quotient
formula at the corresponding source coordinates. -/
theorem det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap =
      (LinearMap.det
        (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
              F p hF c d X).1
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
              F p hF c d X).1.2).toLinearMap)⁻¹ *
        LinearMap.det
          (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X.1 X.1.2).toLinearMap :=
  det_skewAdjointPadicCayleyTransitionTangentEquiv F p hF X.1
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1
    X.1.2
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1.2

/-- The exact reverse overlap tangent determinant is the inverse of the
forward determinant. -/
theorem det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseTangentEquiv
          F p hF c d X).toLinearMap =
      (LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap)⁻¹ := by
  exact LinearEquiv.det_coe_symm _

/-- On the Cayley source, the coordinate Jacobian density is exactly
the inverse nonnegative modulus of the intrinsic left-trivialized tangent
map. -/
theorem skewAdjointPadicCayleyCoordinateJacobianDensity_eq_inv_nnnorm
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p) :
    Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F X =
      ‖LinearMap.det
        (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX).toLinearMap‖₊⁻¹ := by
  exact
    (Matrix.inv_nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      p n F hFsymm hF X hX).symm

/-- The intrinsic transition determinant norm is the target-coordinate
Jacobian density divided by the source-coordinate Jacobian density. -/
theorem nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_density_ratio
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap‖₊ =
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F Y *
        (Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
          p n F X)⁻¹ := by
  rw [nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv,
    skewAdjointPadicCayleyCoordinateJacobianDensity_eq_inv_nnnorm
      F p hFsymm hF X hX,
    skewAdjointPadicCayleyCoordinateJacobianDensity_eq_inv_nnnorm
      F p hFsymm hF Y hY,
    inv_inv, mul_comm]

/-- Equivalently, the target-coordinate Jacobian density is the source
density multiplied by the intrinsic transition determinant norm. -/
theorem skewAdjointPadicCayleyCoordinateJacobianDensity_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F Y =
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F X *
        ‖LinearMap.det
          (skewAdjointPadicCayleyTransitionTangentEquiv
            F p hF X Y hX hY).toLinearMap‖₊ := by
  let JX :=
    Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F X
  let JY :=
    Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F Y
  have hJX : JX ≠ 0 := by
    exact ne_of_gt
      (Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity_pos
        p n F X hX)
  rw [
    nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_density_ratio
      F p hFsymm hF X Y hX hY]
  change JY = JX * (JY * JX⁻¹)
  calc
    JY = JY * 1 := (mul_one JY).symm
    _ = JY * (JX * JX⁻¹) := by rw [mul_inv_cancel₀ hJX]
    _ = JX * (JY * JX⁻¹) := by ac_rfl

/-- The scalar Cayley tangent factor cancels from the overlap determinant
norm, leaving only the ratio of source denominator norms. -/
theorem nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap‖₊ =
      ‖Matrix.det
        (1 - (Y : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1))⁻¹ := by
  rw [
    nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_density_ratio
      F p hFsymm hF X Y hX hY]
  unfold Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
  have htwo : ‖(2 : ℚ_[p])‖₊ ≠ 0 := by
    simp
  field_simp

/-- At an odd prime, the overlap determinant norm has the same denominator
ratio: the scalar factor is already cancelled. -/
theorem nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio_of_ne_two
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2)
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF X Y hX hY).toLinearMap‖₊ =
      ‖Matrix.det
        (1 - (Y : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1))⁻¹ :=
by
  rw [nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv,
    Matrix.nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      p n F hFsymm hF X hX,
    Matrix.nnnorm_det_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      p n F hFsymm hF Y hY,
    Matrix.nnnorm_two_padic_eq_one_of_ne_two p hp_two]
  simp [mul_comm]

/-- At the dyadic place, the factor `2^(n.choose 2)` also cancels from the
overlap determinant norm. -/
theorem nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio_two
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F 2)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F 2) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTransitionTangentEquiv
          F 2 hF X Y hX hY).toLinearMap‖₊ =
      ‖Matrix.det
        (1 - (Y : Matrix (Fin n) (Fin n) ℚ_[2]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X : Matrix (Fin n) (Fin n) ℚ_[2]))‖₊ ^ (n - 1))⁻¹ :=
  nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio
    F 2 hFsymm hF X Y hX hY

/-- The exact overlap transition norm is the ratio of the source
coordinate Jacobian densities at its corresponding coordinates. -/
theorem nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_density_ratio
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊ =
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1 *
        (Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
          p n F X.1)⁻¹ :=
  nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_density_ratio
    F p hFsymm hF X.1
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1
      X.1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.2

/-- The exact overlap transition norm has the scalar-free denominator ratio
at its corresponding source coordinates. -/
theorem nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_denominator_ratio
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊ =
      ‖Matrix.det
        (1 -
          ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^
            (n - 1))⁻¹ :=
  nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio
    F p hFsymm hF X.1
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1
      X.1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.2

/-- At an odd prime, the exact overlap norm is also the scalar-free
source denominator ratio. -/
theorem nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_denominator_ratio_of_ne_two
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2)
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊ =
      ‖Matrix.det
        (1 -
          ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))‖₊ ^
            (n - 1))⁻¹ :=
  nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio_of_ne_two
    F p hp_two hFsymm hF X.1
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1
      X.1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.2

/-- At the dyadic place, the exact overlap norm also has no residual scalar
factor. -/
theorem nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_denominator_ratio_two
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[2])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F 2 hF c d) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F 2 hF c d X).toLinearMap‖₊ =
      ‖Matrix.det
        (1 -
          ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F 2 hF c d X).1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]))‖₊ ^ (n - 1) *
        (‖Matrix.det
          (1 - (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[2]))‖₊ ^
            (n - 1))⁻¹ :=
  nnnorm_det_skewAdjointPadicCayleyTransitionTangentEquiv_eq_denominator_ratio_two
    F hFsymm hF X.1
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F 2 hF c d X).1
      X.1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F 2 hF c d X).1.2

/-- The translated target density evaluated on a translated Cayley
image is the extended source-coordinate density at that source point. -/
theorem padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : Matrix.skewAdjointPadicCayleySource F p) :
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X) =
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal
        p n F X := by
  simp only [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal,
    Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal,
    skewAdjointPadicCayleyTranslatedHomeomorph]
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
    Homeomorph.symm_apply_apply]

/-- On an exact overlap, the determinant norm is the ratio of the two
translated chart densities evaluated at their pointwise common target. -/
theorem coe_nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_targetDensity_ratio
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (‖LinearMap.det
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toLinearMap‖₊ : ℝ≥0∞) =
      padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
          p n F hF d
          (skewAdjointPadicCayleyTranslatedHomeomorph F p hF d
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
              F p hF c d X).1) *
        (padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
          p n F hF c
          (skewAdjointPadicCayleyTranslatedHomeomorph
            F p hF c X.1))⁻¹ := by
  rw [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph,
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph]
  have h :=
    congrArg (fun z : ℝ≥0 ↦ (z : ℝ≥0∞))
      (nnnorm_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv_eq_density_ratio
        F p hFsymm hF c d X)
  have hsourceDensity_ne :
      Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
          p n F X.1 ≠ 0 :=
    ne_of_gt
      (Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity_pos
        p n F X.1 X.1.2)
  change
    (↑‖LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap‖₊ : ℝ≥0∞) =
      (↑(Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity p n F
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1) : ℝ≥0∞) *
        (↑(Matrix.skewAdjointPadicCayleyCoordinateJacobianDensity
          p n F X.1) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv hsourceDensity_ne, ← ENNReal.coe_mul]
  exact h

/-- The translated chart densities satisfy the exact pointwise
center-change cocycle on their two typed representations of the common
target point. -/
theorem padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_center_change
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hFsymm : F.IsSymm) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF d
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF d
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1) =
      padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
          p n F hF c
          (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c X.1) *
        (‖LinearMap.det
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
            F p hF c d X).toLinearMap‖₊ : ℝ≥0∞) := by
  rw [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph,
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_apply_translatedHomeomorph]
  have h :=
    congrArg (fun z : ℝ≥0 ↦ (z : ℝ≥0∞))
      (skewAdjointPadicCayleyCoordinateJacobianDensity_center_change
        F p hFsymm hF X.1
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1
          X.1.2
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1.2)
  simpa only [
    Matrix.skewAdjointPadicCayleyCoordinateJacobianDensityENNReal,
    ENNReal.coe_mul] using h

end PositiveDefiniteIntegralLattice
