import SMSFormula.RationalOrthogonalJacobianMaximalMinors
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Local submersive charts for the rational orthogonal carrier

For every maximal-minor embedding, the independent orthogonality quotient is
first packaged as a `PreSubmersivePresentation`.  Its evaluated square
Jacobian is the transpose of the selected maximal minor, so its Jacobian is
the selected minor.

Composing this presentation with the canonical presentation of the
localization away from that minor gives a `SubmersivePresentation`.
The maximal minors span one, hence these standard-smooth localizations cover
the orthogonal coordinate ring.  Mathlib's locally-standard-smooth criterion
then proves that the whole orthogonal coordinate algebra is smooth over
`ℚ`.  Finally, smoothness is transported through the determinant-one
localization and the completed equivalence with the existing special-
orthogonal coordinate ring.

This proves smoothness.  Mathlib currently has no theorem deriving
reducedness of a smooth algebra over a characteristic-zero field.  That
reducedness statement and the injective-Hopf faithful-flatness theorem are not
proved here.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The independent upper-triangular orthogonality relation as an indexed
polynomial family. -/
def orthogonalIndependentRelation
    (ij : SpecialOrthogonalIndependentRelationIndex (n := n)) :
    specialOrthogonalPolynomialRing (n := n) :=
  V.specialOrthogonalRelation ij.1.1 ij.1.2

/-- Evaluation at the universal orthogonal matrix is the orthogonal quotient
map. -/
theorem specialOrthogonalMatrixEvaluation_orthogonalUniversalMatrix :
    V.specialOrthogonalMatrixEvaluation V.orthogonalUniversalMatrix =
      V.orthogonalPolynomialQuotientAlgHom := by
  apply MvPolynomial.algHom_ext
  intro ij
  rw [V.specialOrthogonalMatrixEvaluation_X]
  rfl

/-- The independent orthogonal quotient, equipped with the selected injection
from relation indices to matrix variables. -/
def orthogonalPreSubmersivePresentation
    (e : OrthogonalJacobianMinorIndex (n := n)) :
    Algebra.PreSubmersivePresentation ℚ V.orthogonalCoordinateRing
      (Fin n × Fin n) (SpecialOrthogonalIndependentRelationIndex (n := n)) :=
  Algebra.PreSubmersivePresentation.naive e e.injective

/-- After mapping to the orthogonal quotient, the square Jacobian of the
selected presentation is the transpose of the corresponding universal
maximal-minor matrix. -/
theorem orthogonalPreSubmersivePresentation_jacobiMatrix_map
    (e : OrthogonalJacobianMinorIndex (n := n)) :
    (algebraMap
      (V.orthogonalPreSubmersivePresentation e).Ring
        V.orthogonalCoordinateRing).mapMatrix
          (V.orthogonalPreSubmersivePresentation e).jacobiMatrix =
      (V.orthogonalUniversalIndependentJacobian.submatrix id e)ᵀ := by
  ext i j
  change (algebraMap
      (V.orthogonalPreSubmersivePresentation e).Ring
        V.orthogonalCoordinateRing)
      ((V.orthogonalPreSubmersivePresentation e).jacobiMatrix i j) = _
  rw [Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [show (V.orthogonalPreSubmersivePresentation e).jacobiMatrix i j =
      MvPolynomial.pderiv (e i) (V.orthogonalIndependentRelation j) by
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rfl]
  change V.orthogonalPolynomialQuotientAlgHom
      (MvPolynomial.pderiv (e i) (V.orthogonalIndependentRelation j)) = _
  rw [← V.specialOrthogonalMatrixEvaluation_orthogonalUniversalMatrix]
  rfl

/-- The Jacobian of the selected independent presentation is literally its
universal maximal minor. -/
theorem orthogonalPreSubmersivePresentation_jacobian
    (e : OrthogonalJacobianMinorIndex (n := n)) :
    (V.orthogonalPreSubmersivePresentation e).jacobian =
      V.orthogonalUniversalIndependentJacobianMinor e := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [RingHom.map_det]
  rw [V.orthogonalPreSubmersivePresentation_jacobiMatrix_map]
  rw [Matrix.det_transpose]
  rfl

/-- The independent quotient presentation composed with localization away
from its selected maximal minor.  Both factors of the composite Jacobian are
the localized minor, hence units. -/
def orthogonalJacobianMinorSubmersivePresentation
    (e : OrthogonalJacobianMinorIndex (n := n)) :
    Algebra.SubmersivePresentation ℚ
      (OrthogonalJacobianMinorLocalization V e)
        (Unit ⊕ (Fin n × Fin n))
          (Unit ⊕ SpecialOrthogonalIndependentRelationIndex (n := n)) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (OrthogonalJacobianMinorLocalization V e)
        (V.orthogonalUniversalIndependentJacobianMinor e)).comp
          (V.orthogonalPreSubmersivePresentation e)
  jacobian_isUnit := by
    classical
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
    rw [V.orthogonalPreSubmersivePresentation_jacobian]
    rw [Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    rw [Algebra.smul_def]
    exact (V.orthogonalUniversalIndependentJacobianMinor_isUnit_localization e).mul
      (V.orthogonalUniversalIndependentJacobianMinor_isUnit_localization e)

/-- Every maximal-minor localization is standard smooth over `ℚ`. -/
theorem orthogonalJacobianMinor_isStandardSmooth
    (e : OrthogonalJacobianMinorIndex (n := n)) :
    Algebra.IsStandardSmooth ℚ
      (OrthogonalJacobianMinorLocalization V e) :=
  (V.orthogonalJacobianMinorSubmersivePresentation e).isStandardSmooth

/-- The unit maximal-minor cover makes the complete orthogonal coordinate map
smooth. -/
theorem orthogonalCoordinateRing_ringHom_smooth :
    (algebraMap ℚ V.orthogonalCoordinateRing).Smooth := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth]
  apply RingHom.locally_of_exists RingHom.isStandardSmooth_respectsIso
    (algebraMap ℚ V.orthogonalCoordinateRing)
      (fun e : OrthogonalJacobianMinorIndex (n := n) =>
        V.orthogonalUniversalIndependentJacobianMinor e)
        V.orthogonalUniversalIndependentJacobianMinorIdeal_eq_top
          (fun e => OrthogonalJacobianMinorLocalization V e)
  intro e
  rw [← IsScalarTower.algebraMap_eq ℚ V.orthogonalCoordinateRing
    (OrthogonalJacobianMinorLocalization V e)]
  exact RingHom.isStandardSmooth_algebraMap.mpr
    (V.orthogonalJacobianMinor_isStandardSmooth e)

/-- The orthogonal coordinate algebra is smooth over `ℚ`. -/
theorem orthogonalCoordinateRing_smooth :
    Algebra.Smooth ℚ V.orthogonalCoordinateRing :=
  RingHom.smooth_algebraMap.mp V.orthogonalCoordinateRing_ringHom_smooth

set_option backward.isDefEq.respectTransparency false in
/-- The existing special-orthogonal coordinate algebra is smooth over `ℚ`,
as the determinant-one localization of the orthogonal coordinate algebra. -/
theorem specialOrthogonalCoordinateRing_smooth :
    Algebra.Smooth ℚ V.specialOrthogonalCoordinateRing := by
  letI : Algebra.Smooth ℚ V.orthogonalCoordinateRing :=
    V.orthogonalCoordinateRing_smooth
  letI : Algebra V.orthogonalCoordinateRing V.orthogonalDetOneComponentRing :=
    RingHom.toAlgebra (R := V.orthogonalCoordinateRing)
      (S := V.orthogonalDetOneComponentRing)
      (Ideal.Quotient.mk (Ideal.span {V.orthogonalDeterminant - 1}))
  letI : Algebra.Smooth V.orthogonalCoordinateRing
      V.orthogonalDetOneComponentRing :=
    Algebra.Smooth.of_isLocalization_Away
      (V.orthogonalDeterminant + 1)
  letI : Algebra.Smooth ℚ V.orthogonalDetOneComponentRing :=
    Algebra.Smooth.comp ℚ V.orthogonalCoordinateRing
      V.orthogonalDetOneComponentRing
  exact Algebra.Smooth.of_equiv (R := ℚ) (A := V.orthogonalDetOneComponentRing)
    (B := V.specialOrthogonalCoordinateRing)
    V.orthogonalDetOneComponentAlgEquivSpecialOrthogonalCoordinateRing

end RationalQuadraticSpaceMatrix
