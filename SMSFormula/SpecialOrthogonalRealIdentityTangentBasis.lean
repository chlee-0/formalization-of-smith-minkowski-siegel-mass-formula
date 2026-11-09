import SMSFormula.SpecialOrthogonalRealIdentityTangentDecomposition
import SMSFormula.SkewAdjointCongruenceNormalization
import SMSFormula.PadicCayleyTargetChartJacobianFormula

/-!
# Fixed bases for the identity-model tangent decomposition

This module compares the independently fixed rationally normalized
skew-adjoint bases in consecutive ranks with the product of the lower-rank
basis and the standard coordinate basis. The comparison determinant remains
symbolic because the fixed skew-adjoint bases are classical `Module.finBasis`
choices.

No measure, sphere factor, disintegration, or rank recurrence is introduced.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Scalar extension sends the rational identity matrix to the real identity
matrix. -/
theorem rationalIdentityMatrix_map_real (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The scalar-extended rational identity tangent and the literal real
identity tangent are the same ambient matrix submodule. -/
theorem identitySpecialOrthogonalMappedIdentityTangent_eq (n : ℕ) :
    skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) =
      identitySpecialOrthogonalTangent n := by
  change
    (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))).toSubmodule =
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℝ)).toSubmodule
  rw [rationalIdentityMatrix_map_real]

/-- The identity-on-ambient-matrices equivalence from the scalar-extended
rational identity tangent to the literal real identity tangent. -/
def identitySpecialOrthogonalMappedIdentityTangentEquiv (n : ℕ) :
    skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ≃ₗ[ℝ]
      identitySpecialOrthogonalTangent n :=
  LinearEquiv.ofEq
    (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))).toSubmodule
    (identitySpecialOrthogonalTangent n)
    (identitySpecialOrthogonalMappedIdentityTangent_eq n)

@[simp] theorem coe_identitySpecialOrthogonalMappedIdentityTangentEquiv_apply
    (n : ℕ)
    (X : skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    ((identitySpecialOrthogonalMappedIdentityTangentEquiv n X :
        identitySpecialOrthogonalTangent n) :
      Matrix (Fin n) (Fin n) ℝ) = X.1 :=
  LinearEquiv.coe_ofEq_apply _ X

/-- The fixed rational skew-adjoint basis after scalar extension, regarded on
the literal real identity-form tangent carrier. -/
def identitySpecialOrthogonalFixedTangentBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n) :=
  (skewAdjointScalarExtensionFinBasis (K := ℝ)
    (1 : Matrix (Fin n) (Fin n) ℚ)).map
      (identitySpecialOrthogonalMappedIdentityTangentEquiv n)

/-- The rational dimensions in consecutive identity ranks differ by `n`. -/
theorem finrank_identitySpecialOrthogonalTangent_rational_succ (n : ℕ) :
    Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)) =
      Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra
            (1 : Matrix (Fin n) (Fin n) ℚ)) + n := by
  rw [finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
      (n + 1) 1 (by simp) (by simp),
    finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
      n 1 (by simp) (by simp)]
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp
  omega

/-- Reindex the lower-rank tangent indices and the `n` last-column indices by
the fixed consecutive-rank tangent dimension. -/
def identitySpecialOrthogonalTangentProductIndexEquiv (n : ℕ) :
    (Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℚ))) ⊕ Fin n) ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))) :=
  finSumFinEquiv.trans
    (Fin.castOrderIso
      (finrank_identitySpecialOrthogonalTangent_rational_succ n).symm).toEquiv

/-- The product of the fixed lower-rank tangent basis and the standard
last-column coordinate basis, reindexed by the higher-rank tangent dimension.
-/
def identitySpecialOrthogonalTangentProductBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  ((identitySpecialOrthogonalFixedTangentBasis n).prod
      (Pi.basisFun ℝ (Fin n))).reindex
    (identitySpecialOrthogonalTangentProductIndexEquiv n)

/-- The fixed higher-rank tangent basis transported through the explicit
block/last-column decomposition. -/
def identitySpecialOrthogonalTangentSplitTransportedBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ))))
      ℝ
      (identitySpecialOrthogonalTangent n × (Fin n → ℝ)) :=
  (identitySpecialOrthogonalFixedTangentBasis (n + 1)).map
    (identitySpecialOrthogonalTangentContinuousLinearEquiv n).toLinearEquiv

/-- The determinant comparing the transported fixed higher-rank basis with
the independently fixed lower-rank/product-coordinate basis. -/
def identitySpecialOrthogonalTangentSplitDetScalar (n : ℕ) : ℝ :=
  (identitySpecialOrthogonalTangentProductBasis n).det
    (identitySpecialOrthogonalTangentSplitTransportedBasis n)

/-- The identity tangent-splitting comparison determinant is nonzero. -/
theorem identitySpecialOrthogonalTangentSplitDetScalar_ne_zero (n : ℕ) :
    identitySpecialOrthogonalTangentSplitDetScalar n ≠ 0 := by
  rw [identitySpecialOrthogonalTangentSplitDetScalar,
    ← Module.Basis.det_basis
      (identitySpecialOrthogonalTangentSplitTransportedBasis n)
      (identitySpecialOrthogonalTangentProductBasis n),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

end PositiveDefiniteIntegralLattice
