import SMSFormula.RationalOrthogonalDifferentialAtPoint

/-!
# The evaluated polynomial Jacobian of the orthogonal presentation

This file connects the independent polynomial relations to the arbitrary-point
linear differential.  The Jacobian entry indexed by an upper-triangular
relation `ij` and a matrix variable `kl` is the evaluation of

```text
pderiv kl (specialOrthogonalRelation i j).
```

Lean proves its explicit two-term formula and proves that matrix-vector
multiplication by this rectangular Jacobian is the independent differential
`H ↦ Hᵀ F M + Mᵀ F H`.  At the universal orthogonal point the right inverse of
that differential therefore gives a right inverse for the polynomial Jacobian
matrix.

A separate Cauchy--Binet/maximal-minor argument converts this rectangular
right-inverse identity into a principal-open cover by unit square minors.
-/

noncomputable section

open scoped Matrix BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The evaluated Jacobian matrix of the independent orthogonality relations. -/
def specialOrthogonalIndependentJacobianAt
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (M : Matrix (Fin n) (Fin n) A) :
    Matrix (SpecialOrthogonalIndependentRelationIndex (n := n))
      (Fin n × Fin n) A :=
  fun ij kl => V.specialOrthogonalMatrixEvaluation M
    (MvPolynomial.pderiv kl (V.specialOrthogonalRelation ij.1.1 ij.1.2))

/-- Entrywise formula for the evaluated independent Jacobian. -/
theorem specialOrthogonalIndependentJacobianAt_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (M : Matrix (Fin n) (Fin n) A)
    (ij : SpecialOrthogonalIndependentRelationIndex (n := n))
    (kl : Fin n × Fin n) :
    V.specialOrthogonalIndependentJacobianAt A M ij kl =
      (if kl.2 = ij.1.1 then
          (V.specialOrthogonalMappedFormMatrix A * M) kl.1 ij.1.2
        else 0) +
      (if kl.2 = ij.1.2 then
          (Mᵀ * V.specialOrthogonalMappedFormMatrix A) ij.1.1 kl.1
        else 0) := by
  have hsum (j : Fin n) (c : Fin n → A) :
      (∑ x, c x *
        (MvPolynomial.aeval fun (ab : Fin n × Fin n) => M ab.1 ab.2)
          ((Pi.single kl
            (1 : specialOrthogonalPolynomialRing (n := n)) :
              (Fin n × Fin n) → specialOrthogonalPolynomialRing (n := n))
                (x, j))) =
        if kl.2 = j then c kl.1 else 0 := by
    classical
    by_cases h : kl.2 = j
    · subst j
      have heval (x : Fin n) :
          (MvPolynomial.aeval fun (ab : Fin n × Fin n) => M ab.1 ab.2)
            ((Pi.single kl
              (1 : specialOrthogonalPolynomialRing (n := n)) :
                (Fin n × Fin n) → specialOrthogonalPolynomialRing (n := n))
                  (x, kl.2)) = if x = kl.1 then 1 else 0 := by
        rw [Pi.single_apply]
        simp [Prod.ext_iff]
      simp_rw [heval]
      simp
    · have heval (x : Fin n) :
          (MvPolynomial.aeval fun (ab : Fin n × Fin n) => M ab.1 ab.2)
            ((Pi.single kl
              (1 : specialOrthogonalPolynomialRing (n := n)) :
                (Fin n × Fin n) → specialOrthogonalPolynomialRing (n := n))
                  (x, j)) = 0 := by
        rw [Pi.single_apply]
        rw [if_neg]
        · simp
        · intro hpair
          exact h (congrArg Prod.snd hpair).symm
      simp_rw [heval]
      rw [if_neg h]
      simp
  simp [specialOrthogonalIndependentJacobianAt,
    specialOrthogonalRelation, specialOrthogonalMatrixEvaluation,
    specialOrthogonalUniversalMatrix, specialOrthogonalFormMatrixPolynomial,
    specialOrthogonalMappedFormMatrix, Matrix.mul_apply]
  rw [Finset.sum_add_distrib]
  simp_rw [hsum]
  by_cases hi : kl.2 = ij.1.1 <;>
    by_cases hj : kl.2 = ij.1.2 <;>
      simp [hi, hj, mul_comm] <;> abel

/-- Multiplying the evaluated polynomial Jacobian by matrix coordinates is
the independent arbitrary-point differential. -/
theorem specialOrthogonalIndependentJacobianAt_mulVec
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (M H : Matrix (Fin n) (Fin n) A) :
    (V.specialOrthogonalIndependentJacobianAt A M).mulVec
        (fun kl => H kl.1 kl.2) =
      independentOrthogonalRelationDifferentialAt A
        (V.specialOrthogonalMappedFormMatrix A) M
          (V.form_symm.map (algebraMap ℚ A)) H := by
  funext ij
  have hsum (j : Fin n) (c : Fin n → A) :
      (∑ kl : Fin n × Fin n,
        (if kl.2 = j then c kl.1 else 0) * H kl.1 kl.2) =
        ∑ k, c k * H k j := by
    rw [Fintype.sum_prod_type]
    simp
  have hfirst :
      (∑ k, (V.specialOrthogonalMappedFormMatrix A * M) k ij.1.2 *
        H k ij.1.1) =
      ∑ x, (∑ k, H k ij.1.1 *
        V.specialOrthogonalMappedFormMatrix A k x) * M x ij.1.2 := by
    simp only [Matrix.mul_apply]
    calc
      (∑ k, (∑ x, V.specialOrthogonalMappedFormMatrix A k x *
          M x ij.1.2) * H k ij.1.1) =
          ∑ k, ∑ x, (V.specialOrthogonalMappedFormMatrix A k x *
            M x ij.1.2) * H k ij.1.1 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
      _ = ∑ x, ∑ k, (V.specialOrthogonalMappedFormMatrix A k x *
            M x ij.1.2) * H k ij.1.1 := by
        rw [Finset.sum_comm]
      _ = ∑ x, (∑ k, H k ij.1.1 *
            V.specialOrthogonalMappedFormMatrix A k x) * M x ij.1.2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [show
    independentOrthogonalRelationDifferentialAt A
      (V.specialOrthogonalMappedFormMatrix A) M
        (V.form_symm.map (algebraMap ℚ A)) H ij =
      (Matrix.orthogonalRelationDifferentialAt
        (V.specialOrthogonalMappedFormMatrix A) M H) ij.1.1 ij.1.2 by
          rfl]
  rw [Matrix.mulVec, dotProduct]
  simp_rw [V.specialOrthogonalIndependentJacobianAt_apply, add_mul,
    Finset.sum_add_distrib]
  rw [hsum ij.1.1 (fun k =>
      (V.specialOrthogonalMappedFormMatrix A * M) k ij.1.2),
    hsum ij.1.2 (fun k =>
      (Mᵀ * V.specialOrthogonalMappedFormMatrix A) ij.1.1 k),
    hfirst]
  rfl

/-- The actual universal polynomial Jacobian over the orthogonal coordinate
ring. -/
def orthogonalUniversalIndependentJacobian :
    Matrix (SpecialOrthogonalIndependentRelationIndex (n := n))
      (Fin n × Fin n) V.orthogonalCoordinateRing :=
  V.specialOrthogonalIndependentJacobianAt V.orthogonalCoordinateRing
    V.orthogonalUniversalMatrix

/-- The canonical invertibility witness for two in the rational orthogonal
coordinate ring. -/
def orthogonalCoordinateRingInvertibleTwo :
    Invertible (2 : V.orthogonalCoordinateRing) :=
  Invertible.copy
    (Invertible.map (algebraMap ℚ V.orthogonalCoordinateRing) (2 : ℚ))
    (2 : V.orthogonalCoordinateRing)
    (map_ofNat (algebraMap ℚ V.orthogonalCoordinateRing) 2).symm

/-- The explicit right inverse of the universal polynomial Jacobian, written
as a rectangular matrix. -/
def orthogonalUniversalIndependentJacobianRightInverse :
    Matrix (Fin n × Fin n)
      (SpecialOrthogonalIndependentRelationIndex (n := n))
        V.orthogonalCoordinateRing := by
  letI := V.orthogonalCoordinateRingInvertibleTwo
  exact fun kl ij =>
    independentOrthogonalRelationDifferentialAtRightInverse
      V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
        V.orthogonalUniversalMatrix
          (Pi.single ij 1) kl.1 kl.2

/-- The universal evaluated polynomial Jacobian has the displayed rectangular
matrix as a right inverse. -/
theorem orthogonalUniversalIndependentJacobian_mul_rightInverse :
    V.orthogonalUniversalIndependentJacobian *
        V.orthogonalUniversalIndependentJacobianRightInverse = 1 := by
  letI := V.orthogonalCoordinateRingInvertibleTwo
  let g := independentOrthogonalRelationDifferentialAtRightInverse
    V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
      V.orthogonalUniversalMatrix
  have hsplit := independentOrthogonalRelationDifferentialAt_split_surjective
    V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
      V.orthogonalUniversalMatrix
        (V.form_symm.map (algebraMap ℚ V.orthogonalCoordinateRing))
          (V.specialOrthogonalMappedFormMatrix_det_isUnit
            V.orthogonalCoordinateRing)
              V.orthogonalUniversalMatrix_relation
  ext ij ij'
  have hmul := congrFun
    (V.specialOrthogonalIndependentJacobianAt_mulVec
      V.orthogonalCoordinateRing V.orthogonalUniversalMatrix
        (g (Pi.single ij' 1))) ij
  have hright := congrFun (LinearMap.congr_fun hsplit (Pi.single ij' 1)) ij
  have hright' :
      independentOrthogonalRelationDifferentialAt
          V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
            V.orthogonalUniversalMatrix
              (V.form_symm.map
                (algebraMap ℚ V.orthogonalCoordinateRing))
          (g (Pi.single ij' 1)) ij =
        ((Pi.single ij' (1 : V.orthogonalCoordinateRing) :
          (SpecialOrthogonalIndependentRelationIndex (n := n) →
            V.orthogonalCoordinateRing)) ij) := by
    simpa using hright
  change
    (V.orthogonalUniversalIndependentJacobian.mulVec
      (fun kl => g (Pi.single ij' 1) kl.1 kl.2)) ij =
        (1 : Matrix
          (SpecialOrthogonalIndependentRelationIndex (n := n))
          (SpecialOrthogonalIndependentRelationIndex (n := n))
            V.orthogonalCoordinateRing) ij ij'
  unfold orthogonalUniversalIndependentJacobian
  rw [hmul]
  change
    (independentOrthogonalRelationDifferentialAt
      V.orthogonalCoordinateRing V.orthogonalMappedFormMatrix
        V.orthogonalUniversalMatrix
          (V.form_symm.map (algebraMap ℚ V.orthogonalCoordinateRing)))
      (g (Pi.single ij' 1)) ij =
        (1 : Matrix
          (SpecialOrthogonalIndependentRelationIndex (n := n))
          (SpecialOrthogonalIndependentRelationIndex (n := n))
            V.orthogonalCoordinateRing) ij ij'
  rw [hright']
  simp [Matrix.one_apply, Pi.single_apply]

end RationalQuadraticSpaceMatrix
