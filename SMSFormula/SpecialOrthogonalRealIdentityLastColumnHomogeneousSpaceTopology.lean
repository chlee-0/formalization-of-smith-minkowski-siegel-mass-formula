import SMSFormula.SpecialOrthogonalRealIdentityLastColumnHomogeneousSpace

/-!
# Topology of the identity last-column homogeneous space

The identity-form special orthogonal matrix carrier is closed and every
matrix entry lies in `[-1, 1]`. Compactness of that finite coordinate box
therefore gives compactness of the matrix carrier, which is transported
through the fixed homeomorphism to the group.

Its quotient by the last-column stabilizer is consequently compact. The
continuous quotient-to-sphere equivalence from the homogeneous-space module
is therefore a homeomorphism.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable (n : ℕ)

/-- The identity-form determinant-one orthogonal matrix carrier is closed. -/
theorem isClosed_identitySpecialOrthogonalMatrixSet :
    IsClosed
      (Matrix.specialOrthogonalMatrixSet
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) := by
  let I : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1
  have hc : Continuous (Matrix.formPreservingConstraint I) := by
    simpa [Matrix.formPreservingConstraint] using
      (((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
        continuous_id).sub continuous_const)
  have hd : Continuous
      (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => A.det) := by
    fun_prop
  change IsClosed ({A | Matrix.formPreservingConstraint I A = 0} ∩
    {A | A.det = 1})
  exact (isClosed_eq hc continuous_const).inter
    (isClosed_eq hd continuous_const)

/-- Every entry of an identity-form orthogonal matrix lies in `[-1, 1]`. -/
theorem identitySpecialOrthogonalMatrixSet_subset_unitBox :
    (Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
        Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) ⊆
      (Set.Icc (-1 : ℝ) 1).matrix := by
  intro A hA
  rw [Set.mem_matrix]
  intro i j
  have hpres :
      Aᵀ * A = 1 := by
    have h := (Matrix.formPreservingConstraint_eq_zero_iff _ _).mp hA.1
    simpa using h
  have hsum := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M j j) hpres
  have hsq : A i j ^ 2 ≤ 1 := by
    calc
      A i j ^ 2 ≤ ∑ k, A k j ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (A k j))
          (Finset.mem_univ i)
      _ = 1 := by
        simpa [Matrix.mul_apply, pow_two] using hsum
  rw [sq_le_one_iff_abs_le_one, abs_le] at hsq
  exact hsq

/-- The identity-form determinant-one orthogonal matrix carrier is compact. -/
theorem isCompact_identitySpecialOrthogonalMatrixSet :
    IsCompact
      (Matrix.specialOrthogonalMatrixSet
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
          Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) :=
  IsCompact.of_isClosed_subset
    (isCompact_Icc.matrix)
    (isClosed_identitySpecialOrthogonalMatrixSet n)
    (identitySpecialOrthogonalMatrixSet_subset_unitBox n)

/-- The project identity-form special orthogonal group is compact. -/
noncomputable instance identitySpecialOrthogonalGroupCompactSpace :
    CompactSpace (identitySpecialOrthogonalGroup n) := by
  letI : CompactSpace
      (Matrix.specialOrthogonalMatrixSet
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_identitySpecialOrthogonalMatrixSet n)
  let e :=
    specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  apply isCompact_univ_iff.mp
  have hrange : Set.range e = Set.univ :=
    e.surjective.range_eq
  rw [← hrange]
  simpa only [Set.image_univ] using
    (isCompact_univ.image e.continuous)

/-- In rank at least two, the stabilizer quotient is homeomorphic to the unit
sphere through the last-column map. -/
def identitySpecialOrthogonalLastColumnQuotientHomeomorph
    (hn : 0 < n) :
    identitySpecialOrthogonalLastColumnHomogeneousSpace n ≃ₜ
      identitySpecialOrthogonalLastColumnSphere n :=
  (continuous_identitySpecialOrthogonalLastColumnQuotientEquiv n hn)
    |>.homeoOfEquivCompactToT2

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientHomeomorph_mk
    (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnQuotientHomeomorph n hn
        (QuotientGroup.mk g) =
      identitySpecialOrthogonalLastColumn n g :=
  rfl

theorem identitySpecialOrthogonalLastColumnQuotientHomeomorph_toEquiv
    (hn : 0 < n) :
    (identitySpecialOrthogonalLastColumnQuotientHomeomorph n hn).toEquiv =
      identitySpecialOrthogonalLastColumnQuotientEquiv n hn :=
  rfl

end PositiveDefiniteIntegralLattice
