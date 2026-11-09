import SMSFormula.RationalSpecialOrthogonalIndependentRelations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# The determinant-one component of the rational orthogonal carrier

The independent symmetric relations first define the orthogonal coordinate
ring, without imposing determinant one.  In this quotient the universal
matrix satisfies `Xᵀ F X = F`; nonsingularity of `F` then gives

```text
det(X)^2 = 1.
```

Over a ring where two is a unit, the quotient by `det(X) - 1` is the
localization away from `det(X) + 1`.  This file proves that localization
statement generically and applies it to the rational orthogonal coordinate
ring.  It also identifies the resulting double quotient with the
special-orthogonal coordinate ring.

This proves that the determinant-one carrier is an open-and-closed component
of the orthogonal carrier.  Smoothness of the orthogonal carrier from the
independent relation presentation is not proved here; it needs a separate
Jacobian computation.
-/

noncomputable section

open scoped Matrix Pointwise

namespace RationalTamagawa

/-- If `d² = 1` and two is a unit, quotienting by `d - 1` is localization
away from `d + 1`. -/
theorem quotientSpanSubOne_isLocalizationAwayAddOne
    {R : Type*} [CommRing R] (d : R) (hd : d ^ 2 = 1)
    (h2 : IsUnit (2 : R)) :
    letI := (Ideal.Quotient.mk (Ideal.span {d - 1})).toAlgebra
    IsLocalization.Away (d + 1) (R ⧸ Ideal.span {d - 1}) := by
  let I : Ideal R := Ideal.span {d - 1}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  letI : Algebra R S := q.toAlgebra
  have hq_surj : Function.Surjective (algebraMap R S) := by
    change Function.Surjective q
    exact Ideal.Quotient.mk_surjective
  have hqd : algebraMap R S d = 1 := by
    change q d = 1
    rw [← sub_eq_zero, ← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (Set.mem_singleton _))
  have hunit : IsUnit (algebraMap R S (d + 1)) := by
    rw [map_add, hqd, map_one]
    have hmap := h2.map (algebraMap R S)
    rw [map_ofNat] at hmap
    simpa only [one_add_one_eq_two] using hmap
  have hprod : (d + 1) * (d - 1) = 0 := by
    calc
      (d + 1) * (d - 1) = d ^ 2 - 1 := by ring
      _ = 0 := by rw [hd]; ring
  have hkill : (d + 1) • (I : Submodule R R) ≤ ⊥ := by
    intro x hx
    rw [Submodule.mem_bot]
    rcases (Submodule.mem_smul_pointwise_iff_exists x (d + 1)
      (I : Submodule R R)).1 hx with ⟨y, hy, hxy⟩
    rcases Ideal.mem_span_singleton'.1 hy with ⟨a, ha⟩
    calc
      x = (d + 1) * y := by simpa [smul_eq_mul] using hxy.symm
      _ = (d + 1) * (a * (d - 1)) := by rw [ha]
      _ = a * ((d + 1) * (d - 1)) := by ring
      _ = 0 := by rw [hprod, mul_zero]
  apply IsLocalization.Away.of_surjective hq_surj hunit 1
  suffices (d + 1) • RingHom.ker (algebraMap R S) ≤ ⊥ by
    simpa only [pow_one] using this
  rw [show RingHom.ker (algebraMap R S) = I by
    change RingHom.ker q = I
    exact Ideal.mk_ker]
  exact hkill

end RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The coordinate ring of the full orthogonal carrier, before imposing
determinant one. -/
abbrev orthogonalCoordinateRing :=
  specialOrthogonalPolynomialRing (n := n) ⧸
    V.specialOrthogonalIndependentOrthogonalityRelationIdeal

/-- The quotient map to the orthogonal coordinate ring. -/
def orthogonalPolynomialQuotientAlgHom :
    specialOrthogonalPolynomialRing (n := n) →ₐ[ℚ]
      V.orthogonalCoordinateRing :=
  Ideal.Quotient.mkₐ ℚ
    V.specialOrthogonalIndependentOrthogonalityRelationIdeal

/-- The universal matrix over the orthogonal coordinate ring. -/
def orthogonalUniversalMatrix :
    Matrix (Fin n) (Fin n) V.orthogonalCoordinateRing :=
  (specialOrthogonalUniversalMatrix (n := n)).map
    V.orthogonalPolynomialQuotientAlgHom

/-- The stored form matrix mapped to the orthogonal coordinate ring. -/
def orthogonalMappedFormMatrix :
    Matrix (Fin n) (Fin n) V.orthogonalCoordinateRing :=
  V.specialOrthogonalMappedFormMatrix V.orthogonalCoordinateRing

/-- The quotient map kills every entry of the universal orthogonality
relation matrix. -/
theorem orthogonalPolynomialQuotientAlgHom_relationMatrix :
    V.specialOrthogonalRelationMatrix.map
      V.orthogonalPolynomialQuotientAlgHom = 0 := by
  ext i j
  change V.orthogonalPolynomialQuotientAlgHom
      (V.specialOrthogonalRelation i j) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (V.specialOrthogonalRelation_mem_independentOrthogonalityRelationIdeal i j)

/-- The universal orthogonal matrix satisfies `Xᵀ F X = F`. -/
theorem orthogonalUniversalMatrix_relation :
    V.orthogonalUniversalMatrix.transpose *
        V.orthogonalMappedFormMatrix * V.orthogonalUniversalMatrix =
      V.orthogonalMappedFormMatrix := by
  have h := V.orthogonalPolynomialQuotientAlgHom_relationMatrix
  have hFmap : V.specialOrthogonalFormMatrixPolynomial.map
      V.orthogonalPolynomialQuotientAlgHom =
        V.orthogonalMappedFormMatrix := by
    ext i j
    change V.orthogonalPolynomialQuotientAlgHom
        (algebraMap ℚ (specialOrthogonalPolynomialRing (n := n))
          (V.pairingMatrix i j)) =
      algebraMap ℚ V.orthogonalCoordinateRing (V.pairingMatrix i j)
    exact V.orthogonalPolynomialQuotientAlgHom.commutes _
  rw [show V.specialOrthogonalRelationMatrix =
      (specialOrthogonalUniversalMatrix (n := n)).transpose *
          V.specialOrthogonalFormMatrixPolynomial *
            specialOrthogonalUniversalMatrix (n := n) -
        V.specialOrthogonalFormMatrixPolynomial by
      rfl] at h
  rw [Matrix.map_sub _ (map_sub V.orthogonalPolynomialQuotientAlgHom),
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hFmap] at h
  exact sub_eq_zero.mp h

/-- The determinant of the universal orthogonal matrix. -/
def orthogonalDeterminant : V.orthogonalCoordinateRing :=
  V.orthogonalUniversalMatrix.det

/-- In the orthogonal coordinate ring, the universal determinant squares to
one. -/
theorem orthogonalDeterminant_sq : V.orthogonalDeterminant ^ 2 = 1 := by
  have hdet := congrArg Matrix.det V.orthogonalUniversalMatrix_relation
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hFunit : IsUnit V.orthogonalMappedFormMatrix.det := by
    exact V.specialOrthogonalMappedFormMatrix_det_isUnit
      V.orthogonalCoordinateRing
  apply hFunit.mul_left_cancel
  calc
    V.orthogonalMappedFormMatrix.det * V.orthogonalDeterminant ^ 2 =
        V.orthogonalUniversalMatrix.det *
          V.orthogonalMappedFormMatrix.det *
            V.orthogonalUniversalMatrix.det := by
      simp [orthogonalDeterminant]
      ring
    _ = V.orthogonalMappedFormMatrix.det := hdet
    _ = V.orthogonalMappedFormMatrix.det * 1 := by rw [mul_one]

/-- The determinant relation maps to `det(X) - 1` in the orthogonal
coordinate ring. -/
theorem orthogonalPolynomialQuotientAlgHom_detRelation :
    V.orthogonalPolynomialQuotientAlgHom
        V.specialOrthogonalDetRelation =
      V.orthogonalDeterminant - 1 := by
  simp only [specialOrthogonalDetRelation, map_sub, map_one]
  congr 1
  change V.orthogonalPolynomialQuotientAlgHom.toRingHom
      (specialOrthogonalUniversalMatrix (n := n)).det =
    V.orthogonalDeterminant
  rw [RingHom.map_det]
  rfl

/-- The image of the determinant-relation ideal in the orthogonal
coordinate ring is the determinant-one component ideal. -/
theorem specialOrthogonalDetRelationIdeal_map :
    (Ideal.span {V.specialOrthogonalDetRelation}).map
        V.orthogonalPolynomialQuotientAlgHom =
      Ideal.span {V.orthogonalDeterminant - 1} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  exact V.orthogonalPolynomialQuotientAlgHom_detRelation

/-- The independent special-orthogonal ideal is the sum of the independent
orthogonality ideal and the determinant-one ideal. -/
theorem specialOrthogonalIndependentRelationIdeal_eq_sup :
    V.specialOrthogonalIndependentRelationIdeal =
      V.specialOrthogonalIndependentOrthogonalityRelationIdeal ⊔
        Ideal.span {V.specialOrthogonalDetRelation} := by
  simp only [specialOrthogonalIndependentRelationIdeal,
    specialOrthogonalIndependentRelationSet,
    specialOrthogonalIndependentOrthogonalityRelationIdeal,
    Ideal.span_union]

/-- The determinant-one component ring of the orthogonal coordinate ring. -/
abbrev orthogonalDetOneComponentRing :=
  V.orthogonalCoordinateRing ⧸ Ideal.span {V.orthogonalDeterminant - 1}

set_option backward.isDefEq.respectTransparency false in
/-- The determinant-one component is the localization away from
`det(X) + 1`. -/
instance orthogonalDetOneComponentRing_isLocalizationAway :
    letI := RingHom.toAlgebra
      (R := V.orthogonalCoordinateRing) (S := V.orthogonalDetOneComponentRing)
      (Ideal.Quotient.mk (Ideal.span {V.orthogonalDeterminant - 1}))
    IsLocalization.Away (V.orthogonalDeterminant + 1)
      V.orthogonalDetOneComponentRing := by
  letI : Invertible (2 : V.orthogonalCoordinateRing) :=
    Invertible.copy
      (Invertible.map (algebraMap ℚ V.orthogonalCoordinateRing) (2 : ℚ))
      (2 : V.orthogonalCoordinateRing)
      (map_ofNat (algebraMap ℚ V.orthogonalCoordinateRing) 2).symm
  exact RationalTamagawa.quotientSpanSubOne_isLocalizationAwayAddOne
    V.orthogonalDeterminant V.orthogonalDeterminant_sq
      (isUnit_of_invertible (2 : V.orthogonalCoordinateRing))

/-- The determinant-one component of the orthogonal coordinate ring is
literally the existing special-orthogonal coordinate ring, via the third
isomorphism theorem. -/
noncomputable def orthogonalDetOneComponentAlgEquivSpecialOrthogonalCoordinateRing :
    V.orthogonalDetOneComponentRing ≃ₐ[ℚ]
      V.specialOrthogonalCoordinateRing :=
  (Ideal.quotientEquivAlgOfEq ℚ
      V.specialOrthogonalDetRelationIdeal_map.symm).trans <|
    (DoubleQuot.quotQuotEquivQuotSupₐ ℚ
      V.specialOrthogonalIndependentOrthogonalityRelationIdeal
        (Ideal.span {V.specialOrthogonalDetRelation})).trans <|
      Ideal.quotientEquivAlgOfEq ℚ <| by
        rw [← V.specialOrthogonalIndependentRelationIdeal_eq_sup,
          V.specialOrthogonalIndependentRelationIdeal_eq]

end RationalQuadraticSpaceMatrix
