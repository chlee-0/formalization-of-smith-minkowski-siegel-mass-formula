import SMSFormula.SpecialOrthogonalRealIdentityTangentBasis

/-!
# Scalar-extended and literal identity special-orthogonal groups

This module identifies the scalar extension of the rational identity-form
special-orthogonal group with the literal real identity-form group.  Both
directions preserve the ambient matrix definitionally, and form a continuous
multiplicative equivalence.

No Haar measure, product chart, sphere measure, or volume comparison is
introduced here.
-/

open scoped Matrix Matrix.Norms.Operator Topology

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Regard a scalar-extended rational identity-form special-orthogonal point
as a point of the literal real identity-form group.  The carrier is rebuilt
so that its ambient matrix remains definitionally unchanged. -/
def identitySpecialOrthogonalMappedIdentityGroupToLiteral
    (n : ℕ)
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    identitySpecialOrthogonalRankGroup n := by
  let A := g.1.1.1
  let Aset : Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin n) (Fin n) ℝ) :=
    ⟨A,
      (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
        (by
          have hg := g.1.2
          change
            g.1.1.1ᵀ *
                ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) *
                g.1.1.1 =
              (1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ) at hg
          simpa [A, rationalIdentityMatrix_map_real n] using hg),
      (mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup _ Aset

@[simp]
theorem coe_identitySpecialOrthogonalMappedIdentityGroupToLiteral
    (n : ℕ)
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    (identitySpecialOrthogonalMappedIdentityGroupToLiteral n g).1.1.1 =
      g.1.1.1 :=
  rfl

/-- Regard a literal real identity-form special-orthogonal point as a point
of the scalar-extended rational identity-form group, again preserving the
ambient matrix definitionally. -/
def identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n : ℕ) (g : identitySpecialOrthogonalRankGroup n) :
    specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) := by
  let A := g.1.1.1
  let Aset : Matrix.specialOrthogonalMatrixSet
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) :=
    ⟨A,
      (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
        (by
          have hg := g.1.2
          rw [rationalIdentityMatrix_map_real n]
          exact hg),
      (mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup _ Aset

@[simp]
theorem coe_identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n : ℕ) (g : identitySpecialOrthogonalRankGroup n) :
    (identitySpecialOrthogonalLiteralIdentityGroupToMapped n g).1.1.1 =
      g.1.1.1 :=
  rfl

theorem identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse
    (n : ℕ)
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :
    identitySpecialOrthogonalLiteralIdentityGroupToMapped n
        (identitySpecialOrthogonalMappedIdentityGroupToLiteral n g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

theorem identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse
    (n : ℕ) (g : identitySpecialOrthogonalRankGroup n) :
    identitySpecialOrthogonalMappedIdentityGroupToLiteral n
        (identitySpecialOrthogonalLiteralIdentityGroupToMapped n g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

theorem continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalMappedIdentityGroupToLiteral n) := by
  have hmatrix :
      Continuous
        (fun g : specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) =>
          g.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcarrier :
      Continuous
        (fun g : specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) =>
          (⟨g.1.1.1,
            by
              constructor
              · apply (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
                have hg := g.1.2
                change
                  g.1.1.1ᵀ *
                        ((1 : Matrix (Fin n) (Fin n) ℚ).map
                          (algebraMap ℚ ℝ)) *
                        g.1.1.1 =
                      (1 : Matrix (Fin n) (Fin n) ℚ).map
                        (algebraMap ℚ ℝ) at hg
                simpa [rationalIdentityMatrix_map_real n] using hg
              · exact
                  (mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2⟩ :
            Matrix.specialOrthogonalMatrixSet
              (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    hmatrix.subtype_mk _
  exact
    (continuous_specialOrthogonalMatrixSetToSpecialSubgroup
      (1 : Matrix (Fin n) (Fin n) ℝ)).comp hcarrier

theorem continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalLiteralIdentityGroupToMapped n) := by
  have hmatrix :
      Continuous
        (fun g : identitySpecialOrthogonalRankGroup n => g.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcarrier :
      Continuous
        (fun g : identitySpecialOrthogonalRankGroup n =>
          (⟨g.1.1.1,
            by
              constructor
              · apply (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
                have hg := g.1.2
                rw [rationalIdentityMatrix_map_real n]
                exact hg
              · exact
                  (mem_specialFormPreservingMatrixSubgroup_iff _ g.1).mp g.2⟩ :
            Matrix.specialOrthogonalMatrixSet
              ((1 : Matrix (Fin n) (Fin n) ℚ).map
                (algebraMap ℚ ℝ)))) :=
    hmatrix.subtype_mk _
  exact
    (continuous_specialOrthogonalMatrixSetToSpecialSubgroup
      ((1 : Matrix (Fin n) (Fin n) ℚ).map
        (algebraMap ℚ ℝ))).comp hcarrier

/-- The ambient-matrix-preserving continuous multiplicative equivalence
between the scalar-extended rational identity-form group and the literal real
identity-form group. -/
def identitySpecialOrthogonalMappedLiteralContinuousMulEquiv
    (n : ℕ) :
    specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ)) ≃ₜ*
      identitySpecialOrthogonalRankGroup n where
  toFun := identitySpecialOrthogonalMappedIdentityGroupToLiteral n
  invFun := identitySpecialOrthogonalLiteralIdentityGroupToMapped n
  left_inv :=
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_leftInverse n
  right_inv :=
    identitySpecialOrthogonalMappedIdentityGroupToLiteral_rightInverse n
  map_mul' := by
    intro g h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  continuous_toFun :=
    continuous_identitySpecialOrthogonalMappedIdentityGroupToLiteral n
  continuous_invFun :=
    continuous_identitySpecialOrthogonalLiteralIdentityGroupToMapped n

end PositiveDefiniteIntegralLattice
