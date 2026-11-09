import SMSFormula.SkewAdjointRationalElementaryBasis

/-!
# Scalar extension of the form-adapted skew-adjoint basis

The form-adapted elementary rational basis is extended to `ℚ_[p]`
through the skew-adjoint scalar-extension equivalence.  Its
determinant in the scalar extension of the fixed rational basis
is exactly the image of the rational comparison determinant.

The determinant and its p-adic norm remain symbolic.  This file does not
define an exceptional-prime set, compare integral coordinate lattices, or
transport a measure.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- The form-adapted elementary rational skew-adjoint basis after scalar
extension to `ℚ_[p]`. -/
def skewAdjointFormElementaryPadicFinBasis
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
      ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  skewAdjointScalarExtensionBasis (K := ℚ_[p]) F
    (skewAdjointFormElementaryRationalFinBasis F hF hdet)

/-- Each p-adic form-adapted basis vector is the entrywise scalar extension
of its rational counterpart. -/
@[simp]
theorem coe_skewAdjointFormElementaryPadicFinBasis_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    (skewAdjointFormElementaryPadicFinBasis p F hF hdet j :
        Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((skewAdjointFormElementaryRationalFinBasis F hF hdet j :
          skewAdjointMatricesLieSubalgebra F) :
        Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℚ_[p]) := by
  exact coe_skewAdjointScalarExtensionBasis_apply F
    (skewAdjointFormElementaryRationalFinBasis F hF hdet) j

/-- The p-adic form-adapted basis vector is also the literal image of its
rational vector under the skew-adjoint scalar-extension equivalence. -/
theorem skewAdjointFormElementaryPadicFinBasis_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointFormElementaryPadicFinBasis p F hF hdet j =
      skewAdjointScalarExtensionEquiv (K := ℚ_[p]) F
        (1 ⊗ₜ[ℚ]
          skewAdjointFormElementaryRationalFinBasis F hF hdet j) := by
  apply Subtype.ext
  rw [coe_skewAdjointFormElementaryPadicFinBasis_apply,
    coe_skewAdjointScalarExtensionEquiv_tmul]
  simp

/-- Scalar extension preserves the rational determinant comparing the
fixed basis and the form-adapted elementary basis. -/
theorem skewAdjointFixedPadicBasis_det_formElementary
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F).det
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet) =
      algebraMap ℚ ℚ_[p]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet) := by
  have h :=
    skewAdjointScalarExtensionBasis_det_apply
      (K := ℚ_[p]) F (skewAdjointFinBasis F)
      (skewAdjointFormElementaryRationalFinBasis F hF hdet)
  have hv :
      (fun j => skewAdjointScalarExtensionEquiv (K := ℚ_[p]) F
        (1 ⊗ₜ[ℚ]
          skewAdjointFormElementaryRationalFinBasis F hF hdet j)) =
        skewAdjointFormElementaryPadicFinBasis p F hF hdet := by
    funext j
    exact
      (skewAdjointFormElementaryPadicFinBasis_apply p F hF hdet j).symm
  rw [hv] at h
  simpa only [skewAdjointScalarExtensionFinBasis,
    skewAdjointFixedFormElementaryDetScalar] using h

/-- The p-adic fixed/form-adapted basis comparison determinant is nonzero. -/
theorem skewAdjointFixedPadicBasis_det_formElementary_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) F).det
        (skewAdjointFormElementaryPadicFinBasis p F hF hdet) ≠ 0 := by
  rw [skewAdjointFixedPadicBasis_det_formElementary]
  intro hz
  apply skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet
  exact (algebraMap ℚ ℚ_[p]).injective (by simpa using hz)

end Matrix
