import SMSFormula.SpecialOrthogonalRealIdentityTangentMeasure

/-!
# An elementary basis for the identity special-orthogonal tangent

For the identity form, skew-adjoint matrices are ordinary skew-symmetric
matrices. This file transports `Matrix.skewSymmetricBasis` to obtain the
elementary rational basis

`E i j - E j i`, for `i < j`,

and compares it with the non-explicit
`Matrix.skewAdjointFinBasis`. The resulting determinant remains a symbolic
nonzero rational number. Its scalar extension gives the exact coordinate-Haar
comparison with the single canonical rational differential.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

/-- For the identity form, the skew-adjoint and skew-symmetric rational
matrix spaces are linearly equivalent by the identity on ambient matrices. -/
def identitySkewAdjointSkewSymmetricLinearEquiv (n : ℕ) :
    skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℚ) ≃ₗ[ℚ]
      skewSymmetricMatricesSubmodule (R := ℚ) (ι := Fin n) where
  toFun X := ⟨X.1,
    (LieAlgebra.Orthogonal.mem_so (Fin n) ℚ X.1).mp X.2⟩
  invFun X := ⟨X.1,
    (LieAlgebra.Orthogonal.mem_so (Fin n) ℚ X.1).mpr X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The elementary rational identity tangent basis indexed by strict upper
matrix-coordinate pairs. -/
def identitySpecialOrthogonalElementaryRationalBasis (n : ℕ) :
    Module.Basis (Matrix.StrictUpperPair n) ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℚ)) :=
  (Matrix.skewSymmetricBasis (K := ℚ) (by norm_num)).map
    (identitySkewAdjointSkewSymmetricLinearEquiv n).symm

/-- Each elementary identity tangent basis vector is `E i j - E j i`. -/
@[simp] theorem coe_identitySpecialOrthogonalElementaryRationalBasis_apply
    (n : ℕ) (q : Matrix.StrictUpperPair n) :
    ((identitySpecialOrthogonalElementaryRationalBasis n q :
        skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ)) :
      Matrix (Fin n) (Fin n) ℚ) =
      Matrix.single q.1.1 q.1.2 1 -
        Matrix.single q.1.2 q.1.1 1 := by
  simp [identitySpecialOrthogonalElementaryRationalBasis,
    identitySkewAdjointSkewSymmetricLinearEquiv]

theorem card_strictUpperPair_eq_finrank_identitySkewAdjoint (n : ℕ) :
    Fintype.card (Matrix.StrictUpperPair n) =
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ)) := by
  rw [Matrix.StrictUpperPair.card,
    finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
      n 1 (by simp) (by simp)]

/-- A fixed reindexing of strict upper pairs by the finite index used by the
canonical rational tangent basis. -/
def identitySpecialOrthogonalElementaryIndexEquiv (n : ℕ) :
    Matrix.StrictUpperPair n ≃
      Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))) :=
  Fintype.equivOfCardEq
    (by simpa using
      card_strictUpperPair_eq_finrank_identitySkewAdjoint n)

/-- The elementary rational basis reindexed to match
`Matrix.skewAdjointFinBasis`. -/
def identitySpecialOrthogonalElementaryRationalFinBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℚ)) :=
  (identitySpecialOrthogonalElementaryRationalBasis n).reindex
    (identitySpecialOrthogonalElementaryIndexEquiv n)

/-- The rational determinant of the elementary basis in the fixed
rational tangent coordinates. -/
def identitySpecialOrthogonalFixedElementaryDetScalar (n : ℕ) : ℚ :=
  (skewAdjointFinBasis
    (1 : Matrix (Fin n) (Fin n) ℚ)).det
      (identitySpecialOrthogonalElementaryRationalFinBasis n)

theorem identitySpecialOrthogonalFixedElementaryDetScalar_ne_zero (n : ℕ) :
    identitySpecialOrthogonalFixedElementaryDetScalar n ≠ 0 := by
  rw [identitySpecialOrthogonalFixedElementaryDetScalar,
    ← Module.Basis.det_basis
      (identitySpecialOrthogonalElementaryRationalFinBasis n)
      (skewAdjointFinBasis
        (1 : Matrix (Fin n) (Fin n) ℚ)),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- The elementary rational basis after scalar extension to the native real
identity tangent carrier. -/
def identitySpecialOrthogonalElementaryRealFinBasis (n : ℕ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin n) (Fin n) ℚ))))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  skewAdjointScalarExtensionBasis (K := ℝ)
    (1 : Matrix (Fin n) (Fin n) ℚ)
    (identitySpecialOrthogonalElementaryRationalFinBasis n)

theorem identitySpecialOrthogonalElementaryRealFinBasis_apply
    (n : ℕ)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin n) (Fin n) ℚ)))) :
    identitySpecialOrthogonalElementaryRealFinBasis n j =
      skewAdjointScalarExtensionEquiv (K := ℝ)
        (1 : Matrix (Fin n) (Fin n) ℚ)
        (1 ⊗ₜ[ℚ]
          identitySpecialOrthogonalElementaryRationalFinBasis n j) := by
  apply Subtype.ext
  change
    ((skewAdjointScalarExtensionBasis (K := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℚ)
      (identitySpecialOrthogonalElementaryRationalFinBasis n) j :
        skewAdjointMatricesLieSubalgebra
          ((1 : Matrix (Fin n) (Fin n) ℚ).map
            (algebraMap ℚ ℝ))) :
      Matrix (Fin n) (Fin n) ℝ) = _
  rw [Matrix.coe_skewAdjointScalarExtensionBasis_apply,
    Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
  simp

/-- Scalar extension preserves the rational determinant comparing the fixed
and elementary identity tangent bases. -/
theorem identitySpecialOrthogonalFixedRealBasis_det_elementary
    (n : ℕ) :
    (skewAdjointScalarExtensionFinBasis (K := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℚ)).det
        (identitySpecialOrthogonalElementaryRealFinBasis n) =
      (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) := by
  have h :=
    Matrix.skewAdjointScalarExtensionBasis_det_apply
      (K := ℝ) (1 : Matrix (Fin n) (Fin n) ℚ)
      (skewAdjointFinBasis (1 : Matrix (Fin n) (Fin n) ℚ))
      (identitySpecialOrthogonalElementaryRationalFinBasis n)
  have hv :
      (fun j => skewAdjointScalarExtensionEquiv (K := ℝ)
        (1 : Matrix (Fin n) (Fin n) ℚ)
        (1 ⊗ₜ[ℚ]
          identitySpecialOrthogonalElementaryRationalFinBasis n j)) =
        identitySpecialOrthogonalElementaryRealFinBasis n := by
    funext j
    exact
      (identitySpecialOrthogonalElementaryRealFinBasis_apply n j).symm
  rw [hv] at h
  simpa only [Matrix.skewAdjointScalarExtensionFinBasis,
    identitySpecialOrthogonalFixedElementaryDetScalar] using h

local instance identityElementaryTangentMeasurableSpace (n : ℕ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  borel _

local instance identityElementaryTangentBorelSpace (n : ℕ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Additive Haar measure normalized by the elementary real identity tangent
basis. This is a comparison measure, not a replacement for the canonical
fixed-basis measure. -/
def identitySpecialOrthogonalElementaryTangentCoordinateMeasure (n : ℕ) :
    Measure
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  @Module.Basis.addHaar _
    (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) _ _ _
    (identityElementaryTangentMeasurableSpace n)
    (identityElementaryTangentBorelSpace n)
    (identitySpecialOrthogonalElementaryRealFinBasis n)

/-- The elementary coordinate measure differs from the coordinate measure of
the canonical rational differential by the reciprocal absolute rational
basis-change determinant. -/
theorem identitySpecialOrthogonalElementaryTangentCoordinateMeasure_eq_smul_fixed
    (n : ℕ) :
    identitySpecialOrthogonalElementaryTangentCoordinateMeasure n =
      (Real.toNNReal
        |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)|)⁻¹ •
        Matrix.skewAdjointRealCoordinateDetMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ) 0 := by
  have h := @Module.Basis.map_addHaar_eq_inv_abs_det_smul _
    (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)))
    (skewAdjointMatricesLieSubalgebra
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) _ _ _ _ _ _
    (identityElementaryTangentMeasurableSpace n)
    (identityElementaryTangentBorelSpace n)
    (identityElementaryTangentMeasurableSpace n)
    (identityElementaryTangentBorelSpace n) _ _
    (identitySpecialOrthogonalElementaryRealFinBasis n)
    (skewAdjointScalarExtensionFinBasis (K := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℚ))
    (ContinuousLinearEquiv.refl ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))))
  change Measure.map id
      (@Module.Basis.addHaar _
        (skewAdjointMatricesLieSubalgebra
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) _ _ _
        (identityElementaryTangentMeasurableSpace n)
        (identityElementaryTangentBorelSpace n)
        (identitySpecialOrthogonalElementaryRealFinBasis n)) =
    _ at h
  rw [Measure.map_id] at h
  have hdet :
      (skewAdjointScalarExtensionFinBasis (K := ℝ)
        (1 : Matrix (Fin n) (Fin n) ℚ)).det
          (fun i => (ContinuousLinearEquiv.refl ℝ
            (skewAdjointMatricesLieSubalgebra
              ((1 : Matrix (Fin n) (Fin n) ℚ).map
                (algebraMap ℚ ℝ))))
              (identitySpecialOrthogonalElementaryRealFinBasis n i)) =
        (identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ) := by
    simpa using identitySpecialOrthogonalFixedRealBasis_det_elementary n
  have scaledDet := congrArg (fun determinant : ℝ =>
    (Real.toNNReal |determinant|)⁻¹ •
      (@Module.Basis.addHaar _
        (skewAdjointMatricesLieSubalgebra
          ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) _ _ _
        (identityElementaryTangentMeasurableSpace n)
        (identityElementaryTangentBorelSpace n)
        (skewAdjointScalarExtensionFinBasis (K := ℝ)
          (1 : Matrix (Fin n) (Fin n) ℚ)))) hdet
  simpa [identitySpecialOrthogonalElementaryTangentCoordinateMeasure,
    Matrix.skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    Matrix.skewAdjointRealBasisHaarMeasure] using h.trans scaledDet

end PositiveDefiniteIntegralLattice
