import SMSFormula.BinaryPrimitiveDiscriminant
import SMSFormula.ProperMass

/-!
# Proper global classes and stabilizers under binary normalization

The existing proper global relation and stabilizer use exactly the same
determinant-one integer coordinate matrices after primitive normalization.
This does not identify these classes or stabilizers with quadratic-order ideals
or units, and it does not assert a global orientation-reversing automorphism.
-/

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Exact proper-global relation on primitive polynomials at fixed content. -/
theorem isProperGlobalIsometry_iff_binaryPrimitivePolynomial_proper_isometry
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent) :
    K.IsProperGlobalIsometry L ↔
      ∃ e : K.binaryPrimitivePolynomial.IsometryEquiv L.binaryPrimitivePolynomial,
        (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = 1 := by
  constructor
  · rintro ⟨U, hU, hdet, hform⟩
    refine ⟨binaryPrimitivePolynomialIsometryEquivOfMatrix K L U hU hform, ?_⟩
    change (LinearMap.toMatrix' (Matrix.toLin' U)).det = 1
    simpa only [LinearMap.toMatrix'_toLin'] using hdet
  · rintro ⟨e, hdet⟩
    let U := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
    have hU : IsUnit U := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact hdet ▸ isUnit_one
    refine ⟨U, hU, hdet, ?_⟩
    have hpoly : ∀ x, L.binaryPrimitivePolynomialOver ℤ (U.mulVec x) =
        K.binaryPrimitivePolynomialOver ℤ x := by
      intro x
      rw [binaryPrimitivePolynomialOver_int, binaryPrimitivePolynomialOver_int]
      dsimp only [U]
      rw [LinearMap.toMatrix'_mulVec]
      exact e.map_app x
    have hmatrix := (binaryPrimitivePolynomialOver_matrix_congruence_iff K L hg U).mpr hpoly
    simpa only [Int.cast_id, Matrix.map_id] using hmatrix

/-- The original proper class equality is detected by the determinant-one
primitive polynomial isometry. These are global integer matrices. -/
theorem properGlobalIsometryClass_eq_iff_binaryPrimitivePolynomial_proper_isometry
    (K L : PositiveDefiniteIntegralLattice 2) (hg : K.binaryContent = L.binaryContent) :
    K.properGlobalIsometryClass = L.properGlobalIsometryClass ↔
      ∃ e : K.binaryPrimitivePolynomial.IsometryEquiv L.binaryPrimitivePolynomial,
        (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = 1 := by
  rw [← isProperGlobalIsometry_iff_binaryPrimitivePolynomial_proper_isometry K L hg]
  exact ⟨isProperGlobalIsometry_of_properGlobalIsometryClass_eq,
    properGlobalIsometryClass_eq_of_isProperGlobalIsometry⟩

/-- The actual proper stabilizer is in bijection with determinant-one
automorphisms of the primitive polynomial, with exactly the same action. -/
noncomputable def properIsometryGroupEquivBinaryPrimitivePolynomial (K : PositiveDefiniteIntegralLattice 2) :
    K.ProperIsometryGroup ≃
      {e : K.binaryPrimitivePolynomial.IsometryEquiv K.binaryPrimitivePolynomial //
        (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = 1} where
  toFun U := ⟨binaryPrimitivePolynomialIsometryEquivOfMatrix K K U.val U.prop.1.1 U.prop.1.2, by
    change (LinearMap.toMatrix' (Matrix.toLin' U.val)).det = 1
    simpa only [LinearMap.toMatrix'_toLin'] using U.prop.2⟩
  invFun e := by
    let U := LinearMap.toMatrix' e.val.toLinearEquiv.toLinearMap
    have hU : IsUnit U := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact e.prop ▸ isUnit_one
    refine ⟨U, ⟨hU, ?_⟩, e.prop⟩
    have hpoly : ∀ x, K.binaryPrimitivePolynomialOver ℤ (U.mulVec x) =
        K.binaryPrimitivePolynomialOver ℤ x := by
      intro x
      rw [binaryPrimitivePolynomialOver_int]
      dsimp only [U]
      rw [LinearMap.toMatrix'_mulVec]
      exact e.val.map_app x
    have hmatrix := (binaryPrimitivePolynomialOver_matrix_congruence_iff K K rfl U).mpr hpoly
    simpa only [Int.cast_id, Matrix.map_id] using hmatrix
  left_inv U := by
    apply Subtype.ext
    change LinearMap.toMatrix' (Matrix.toLin' U.val) = U.val
    exact LinearMap.toMatrix'_toLin' U.val
  right_inv e := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    rw [binaryPrimitivePolynomialIsometryEquivOfMatrix_apply, LinearMap.toMatrix'_mulVec]
    rfl

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.isProperGlobalIsometry_iff_binaryPrimitivePolynomial_proper_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.properGlobalIsometryClass_eq_iff_binaryPrimitivePolynomial_proper_isometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.properIsometryGroupEquivBinaryPrimitivePolynomial
