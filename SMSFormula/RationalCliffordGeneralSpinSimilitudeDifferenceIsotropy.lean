import SMSFormula.RationalCliffordGeneralSpinSimilitudeCommonValue
import SMSFormula.MatrixCongruence

/-!
# Difference-form isotropy and intrinsic general-Spin similitudes

For a nonsingular scalar-extended rational quadratic form, isotropy of
`Q ⊕ -aQ` supplies a common nonzero value of `Q` and `aQ`.  The resulting
anisotropic reflection pair realizes the prescribed similitude `a`
in intrinsic general Spin.

This is the algebraic step used by the local--global
isotropy argument.  It does not assume any rational or local isotropy theorem.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Scaling a Gram matrix scales every represented quadratic value by the
same scalar. -/
theorem gramQuadraticValue_smul_matrix
    {K : Type*} [Field K]
    (a : K) (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    gramQuadraticValue (a • A) v = a * gramQuadraticValue A v := by
  simp only [gramQuadraticValue, Matrix.smul_mulVec]
  rw [dotProduct_smul]
  rfl

/-- If `a` is a nonzero square, then `Q ⊕ -aQ` is isotropic for every
positive-dimensional nonsingular symmetric Gram form `Q`. -/
theorem gramIsotropic_differenceGramBlock_smul_of_isSquare
    {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (a : K) (ha : a ≠ 0)
    (ha_sq : IsSquare a) :
    GramIsotropic (differenceGramBlock A (a • A)) := by
  obtain ⟨z, hz⟩ := ha_sq
  obtain ⟨c, hc, w, hw⟩ :=
    exists_gramQuadraticValue_eq_ne_zero A hA_symm hA_det hchar
  apply (gramIsotropic_differenceGramBlock_iff A (a • A)).mpr
  right
  right
  refine ⟨a * c, mul_ne_zero ha hc, ⟨z • w, ?_⟩, ⟨w, ?_⟩⟩
  · rw [gramQuadraticValue_smul_vector, hw, hz]
    simp [pow_two]
  · rw [gramQuadraticValue_smul_matrix, hw]

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [CharZero K] [NeZero n]

namespace CliffordGeneralSpinIntrinsicPoint

/-- Isotropy of the scaled difference form `Q ⊕ -aQ` realizes `a` as a
literal intrinsic general-Spin similitude. -/
theorem exists_similitude_eq_of_differenceGramBlock_smul_isotropic
    (a : Kˣ)
    (hiso : PositiveDefiniteIntegralLattice.GramIsotropic
      (PositiveDefiniteIntegralLattice.differenceGramBlock
        (V.specialOrthogonalMappedFormMatrix K)
        ((a : K) • V.specialOrthogonalMappedFormMatrix K))) :
    ∃ x : V.CliffordGeneralSpinIntrinsicPoint K,
      similitudeGroupHom V K x = a := by
  let A := V.specialOrthogonalMappedFormMatrix K
  let B := (a : K) • A
  have hA_symm : A.IsSymm := by
    exact V.form_symm.map (algebraMap ℚ K)
  have hA_det : A.det ≠ 0 := by
    exact (V.specialOrthogonalMappedFormMatrix_det_isUnit K).ne_zero
  have hB_symm : B.IsSymm := by
    exact hA_symm.smul (a : K)
  have hB_det : B.det ≠ 0 := by
    simp only [B, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ a.ne_zero) hA_det
  obtain ⟨c, hc, ⟨w, hw⟩, ⟨v, hv⟩⟩ :=
    (PositiveDefiniteIntegralLattice.gramIsotropic_differenceGramBlock_iff_exists_common_value
      A B hA_symm hA_det hB_symm hB_det (by norm_num)).mp hiso
  have hvA : PositiveDefiniteIntegralLattice.gramQuadraticValue A v = (a : K)⁻¹ * c := by
    rw [← hv]
    simp only [B, PositiveDefiniteIntegralLattice.gramQuadraticValue_smul_matrix]
    field_simp [a.ne_zero]
  have hwQ : V.commutativeScalarExtensionQuadraticForm K w = c := by
    rw [V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
    exact hw
  have hvQ : V.commutativeScalarExtensionQuadraticForm K v = (a : K)⁻¹ * c := by
    rw [V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
    exact hvA
  let w' : (V.commutativeScalarExtensionQuadraticForm K).AnisotropicVector :=
    ⟨w, hwQ.trans_ne hc⟩
  let v' : (V.commutativeScalarExtensionQuadraticForm K).AnisotropicVector :=
    ⟨v, by
      rw [hvQ]
      exact mul_ne_zero (inv_ne_zero a.ne_zero) hc⟩
  apply exists_similitude_eq_of_reflectionPair_value_eq_mul V K a v' w'
  change V.commutativeScalarExtensionQuadraticForm K w =
    (a : K) * V.commutativeScalarExtensionQuadraticForm K v
  rw [hwQ, hvQ]
  field_simp [a.ne_zero]

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
