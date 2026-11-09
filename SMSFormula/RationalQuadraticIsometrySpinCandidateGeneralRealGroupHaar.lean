import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRealTangentHaar
import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarCancellation

/-!
# Real SO Haar transport under an arbitrary rational isometry

After the rank equality forced by an arbitrary supplied rational quadratic
isometry, its inverse matrix gives a real form-congruence datum for the two
existing native SO groups.  The datum's tangent map is exactly the scalar
extension already constructed across the original native carriers, so its
determinant is the real image of the canonical rational modulus.  The existing
form-congruence Haar theorem therefore evaluates the SO transport factor.

No new chart or Haar normalization is selected.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator TensorProduct ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}
variable (U V : RationalQuadraticSpaceMatrix n)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

noncomputable local instance realSOGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (W.specialOrthogonalMatrixGroup ℝ) :=
  W.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance realSOGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix n) :
    BorelSpace (W.specialOrthogonalMatrixGroup ℝ) :=
  W.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The inverse isometry matrix as a real general-linear point. -/
def rationalIsometryRealFormCongruenceUnit : GL (Fin n) ℝ := by
  let N := (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ)
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ)
  have hNM : N * M = 1 := by
    simpa [N, M, Matrix.map_mul] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ))
      (rationalIsometryInverseMatrix_mul_matrix U V e)
  have hdet : N.det ≠ 0 := by
    intro h
    have hd := congrArg Matrix.det hNM
    rw [Matrix.det_mul, h] at hd
    simp at hd
  exact Matrix.GeneralLinearGroup.mkOfDetNeZero N hdet

@[simp]
theorem coe_rationalIsometryRealFormCongruenceUnit :
    (rationalIsometryRealFormCongruenceUnit U V e :
      Matrix (Fin n) (Fin n) ℝ) =
      (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ) := by
  simp [rationalIsometryRealFormCongruenceUnit,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

@[simp]
theorem coe_rationalIsometryRealFormCongruenceUnit_inv :
    (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ) := by
  let N := (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ)
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ)
  have hNM : N * M = 1 := by
    simpa [N, M, Matrix.map_mul] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ))
      (rationalIsometryInverseMatrix_mul_matrix U V e)
  have hu :
      (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) * N = 1 := by
    have hgrp : (rationalIsometryRealFormCongruenceUnit U V e)⁻¹ *
        rationalIsometryRealFormCongruenceUnit U V e = 1 := by simp
    have hmat := congrArg
      (fun z : GL (Fin n) ℝ => (z : Matrix (Fin n) (Fin n) ℝ)) hgrp
    have hmat' :
        (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
            Matrix (Fin n) (Fin n) ℝ) *
          (rationalIsometryRealFormCongruenceUnit U V e :
            Matrix (Fin n) (Fin n) ℝ) = 1 := by
      simpa only [Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_one] using hmat
    rw [coe_rationalIsometryRealFormCongruenceUnit] at hmat'
    exact hmat'
  show (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = M
  calc
    (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
        (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) * 1 := by rw [Matrix.mul_one]
    _ = (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) * (N * M) := by rw [hNM]
    _ = M := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

/-- Matrix formula for the scalar-extended real tangent equivalence. -/
theorem coe_rationalIsometryRealSkewAdjointLinearEquiv_apply
    (X : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule) :
    (rationalIsometryRealSkewAdjointLinearEquiv U V e X :
      Matrix (Fin n) (Fin n) ℝ) =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ) * X.1 *
        (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ) := by
  let C : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
      ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ))
      ((rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ))
  let L :
      (skewAdjointMatricesLieSubalgebra
          (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
      (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e
        ).toContinuousLinearMap
  let R :
      (skewAdjointMatricesLieSubalgebra
          (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    C.comp (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL
  have hLR : L = R := by
    have hlin : L.toLinearMap = R.toLinearMap := by
      apply (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
        U.pairingMatrix).ext
      intro i
      change
        ((rationalIsometryRealSkewAdjointLinearEquiv U V e
          (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
            U.pairingMatrix i) :
            (skewAdjointMatricesLieSubalgebra
              (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℝ) =
        C (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
          U.pairingMatrix i)
      simp only [Matrix.skewAdjointScalarExtensionFinBasis,
        Matrix.skewAdjointScalarExtensionBasis, Module.Basis.map_apply,
        Module.Basis.baseChange_apply]
      rw [rationalIsometryRealSkewAdjointLinearEquiv_scalarExtension,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul,
        coe_rationalIsometrySkewAdjointLinearEquiv_apply,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
      simp [C, Matrix.map_mul]
      rfl
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hlin y
  change L X = R X
  exact DFunLike.congr_fun hLR X

/-- Same-rank real form-congruence datum induced by the supplied rational
isometry. -/
def rationalIsometryRealFormCongruenceData :
    SpecialOrthogonalRealFormCongruenceData U.pairingMatrix V.pairingMatrix where
  unit := rationalIsometryRealFormCongruenceUnit U V e
  congruence := by
    rw [coe_rationalIsometryRealFormCongruenceUnit]
    have hQ :
        (rationalIsometryInverseMatrix U V e)ᵀ * U.pairingMatrix *
            rationalIsometryInverseMatrix U V e = V.pairingMatrix := by
      let M := rationalIsometryMatrix U V e
      let N := rationalIsometryInverseMatrix U V e
      have hMN : M * N = 1 :=
        rationalIsometryMatrix_mul_inverseMatrix U V e
      have hform : Mᵀ * V.pairingMatrix * M = U.pairingMatrix :=
        rationalIsometryMatrix_form_congruence U V e
      calc
        Nᵀ * U.pairingMatrix * N = Nᵀ * (Mᵀ * V.pairingMatrix * M) * N := by
          rw [hform]
        _ = (M * N)ᵀ * V.pairingMatrix * (M * N) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = V.pairingMatrix := by rw [hMN, Matrix.transpose_one]; simp
    simpa [Matrix.map_mul, Matrix.transpose_map] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ)) hQ

theorem rationalIsometryRealFormCongruenceData_tangentEquiv_eq :
    (rationalIsometryRealFormCongruenceData U V e).tangentEquiv =
      rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e := by
  apply DFunLike.ext _ _
  intro X
  apply Subtype.ext
  rw [SpecialOrthogonalRealFormCongruenceData.coe_tangentEquiv_apply]
  change
    (rationalIsometryRealFormCongruenceUnit U V e :
        Matrix (Fin n) (Fin n) ℝ)⁻¹ * X.1 *
      (rationalIsometryRealFormCongruenceUnit U V e :
        Matrix (Fin n) (Fin n) ℝ) = _
  rw [show
      ((rationalIsometryRealFormCongruenceUnit U V e :
          Matrix (Fin n) (Fin n) ℝ)⁻¹) =
        (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) by
      exact (Matrix.GeneralLinearGroup.coe_inv _).symm]
  rw [coe_rationalIsometryRealFormCongruenceUnit_inv,
    coe_rationalIsometryRealFormCongruenceUnit]
  exact (coe_rationalIsometryRealSkewAdjointLinearEquiv_apply U V e X).symm

set_option maxRecDepth 10000 in
theorem rationalIsometryRealFormCongruenceData_detScalar :
    (rationalIsometryRealFormCongruenceData U V e).detScalar =
      (rationalIsometrySkewAdjointDetScalar U V e : ℝ) := by
  rw [SpecialOrthogonalRealFormCongruenceData.detScalar,
    rationalIsometryRealFormCongruenceData_tangentEquiv_eq]
  exact rationalIsometryRealSkewAdjointDet_apply U V e

/-- Over the reals, the scalar-extended rational isometry is multiplication
by its entrywise scalar-extended matrix. -/
theorem rationalIsometryBaseChangeIsometryEquiv_real_eq_mulVec
    (y : Fin n → ℝ) :
    rationalIsometryBaseChangeIsometryEquiv U V e ℝ y =
      Matrix.mulVec
        ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ)) y := by
  classical
  let L :=
    (rationalIsometryBaseChangeIsometryEquiv U V e ℝ).toLinearEquiv.toLinearMap
  let R := Matrix.toLin'
    ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ))
  have hLR : L = R := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro i
    have hb : (Pi.basisFun ℝ (Fin n)) i =
        fun j => algebraMap ℚ ℝ ((Pi.basisFun ℚ (Fin n)) i j) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    change rationalIsometryBaseChangeIsometryEquiv U V e ℝ
        ((Pi.basisFun ℝ (Fin n)) i) =
      Matrix.mulVec
        ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ))
        ((Pi.basisFun ℝ (Fin n)) i)
    rw [hb, rationalIsometryBaseChangeIsometryEquiv_rational]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      rationalIsometryMatrix, LinearMap.toMatrix'_apply]
    simp [Pi.single_apply]
  change L y = R y
  rw [hLR]

/-- The inverse scalar-extended real isometry is multiplication by the
entrywise scalar-extended inverse matrix. -/
theorem rationalIsometryBaseChangeIsometryEquiv_real_symm_eq_mulVec
    (y : Fin n → ℝ) :
    (rationalIsometryBaseChangeIsometryEquiv U V e ℝ).symm y =
      Matrix.mulVec
        ((rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ)) y := by
  let E := rationalIsometryBaseChangeIsometryEquiv U V e ℝ
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ)
  let N := (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ)
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ))
      (rationalIsometryMatrix_mul_inverseMatrix U V e)
  apply E.injective
  have hleft : E.toLinearEquiv (E.symm y) = y := E.apply_symm_apply y
  rw [hleft]
  change y = E (Matrix.mulVec N y)
  rw [rationalIsometryBaseChangeIsometryEquiv_real_eq_mulVec]
  change y = Matrix.mulVec M (Matrix.mulVec N y)
  calc
    y = Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℝ) y := by simp
    _ = Matrix.mulVec (M * N) y := by rw [hMN]
    _ = Matrix.mulVec M (Matrix.mulVec N y) :=
      (Matrix.mulVec_mulVec y M N).symm

/-- Matrix formula for arbitrary-isometry conjugation on real SO points. -/
theorem coe_rationalIsometrySpecialOrthogonalMatrixPoint_real
    (g : U.specialOrthogonalMatrixPoint ℝ) :
    (rationalIsometrySpecialOrthogonalMatrixPoint U V e ℝ g).1 =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ) * g.1 *
        (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ) := by
  classical
  ext i j
  let y : Fin n → ℝ := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (rationalIsometrySpecialOrthogonalMatrixPoint U V e ℝ g).1 y =
        Matrix.mulVec
          ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ) * g.1 *
            (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ)) y := by
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    rw [rationalIsometryBaseChangeIsometryEquiv_real_eq_mulVec,
      rationalIsometryBaseChangeIsometryEquiv_real_symm_eq_mulVec]
    rw [Matrix.mulVec_mulVec y]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  simpa [Matrix.mulVec, dotProduct, y, Pi.single_apply] using congrFun hvec i

/-- The real form-congruence group equivalence is exactly arbitrary-isometry
conjugation on the existing SO carrier. -/
theorem rationalIsometryRealFormCongruenceData_groupEquiv_apply
    (g : U.specialOrthogonalMatrixGroup ℝ) :
    (rationalIsometryRealFormCongruenceData U V e).groupEquiv g =
      V.specialOrthogonalMatrixPointToGroup ℝ
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e ℝ
          (U.specialOrthogonalMatrixPointOfGroup ℝ g)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [SpecialOrthogonalRealFormCongruenceData.coe_groupEquiv_apply]
  change
    (((rationalIsometryRealFormCongruenceUnit U V e)⁻¹ : GL (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) * g.1.1.1 *
      (rationalIsometryRealFormCongruenceUnit U V e :
        Matrix (Fin n) (Fin n) ℝ) = _
  rw [coe_rationalIsometryRealFormCongruenceUnit_inv,
    coe_rationalIsometryRealFormCongruenceUnit]
  change
    (rationalIsometryMatrix U V e).map (algebraMap ℚ ℝ) * g.1.1.1 *
        (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℝ) =
      (rationalIsometrySpecialOrthogonalMatrixPoint U V e ℝ
        (U.specialOrthogonalMatrixPointOfGroup ℝ g)).1
  rw [coe_rationalIsometrySpecialOrthogonalMatrixPoint_real]
  rfl

/-- Arbitrary-isometry Spin transport commutes with the represented real
special-orthogonal map and the form-congruence equivalence. -/
theorem rationalIsometrySpinCandidate_realSpecialOrthogonal_commutes
    (z : U.CliffordSpinCandidateGroup ℝ) :
    (rationalIsometryRealFormCongruenceData U V e).groupEquiv
        (U.cliffordSpinCandidateGroupToSpecialOrthogonal ℝ z) =
      V.cliffordSpinCandidateGroupToSpecialOrthogonal ℝ
        (rationalIsometrySpinCandidateMulEquiv U V e ℝ z) := by
  rw [rationalIsometryRealFormCongruenceData_groupEquiv_apply]
  have h :=
    cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
      U V e ℝ z
  have hm := congrArg
    (fun w : V.CliffordGeneralSpinIntrinsicPoint ℝ => w.matrixGroup) h
  exact hm.symm

/-- The real SO image of Spin pulls back to the corresponding source image
under arbitrary-isometry conjugation. -/
theorem preimage_rationalIsometrySpinCandidate_realSpecialOrthogonal_range :
    (rationalIsometryRealFormCongruenceData U V e).groupEquiv ⁻¹'
        {g | ∃ z : V.CliffordSpinCandidateGroup ℝ,
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℝ z = g} =
      {g | ∃ z : U.CliffordSpinCandidateGroup ℝ,
        U.cliffordSpinCandidateGroupToSpecialOrthogonal ℝ z = g} := by
  ext g
  constructor
  · rintro ⟨t, ht⟩
    let z := (rationalIsometrySpinCandidateMulEquiv U V e ℝ).symm t
    refine ⟨z, ?_⟩
    apply (rationalIsometryRealFormCongruenceData U V e).groupEquiv.injective
    rw [rationalIsometrySpinCandidate_realSpecialOrthogonal_commutes]
    simpa [z] using ht
  · rintro ⟨z, rfl⟩
    exact ⟨rationalIsometrySpinCandidateMulEquiv U V e ℝ z,
      (rationalIsometrySpinCandidate_realSpecialOrthogonal_commutes U V e z).symm⟩

/-- The existing invariant-differential SO measure transforms by the
reciprocal archimedean norm of the canonical rational tangent modulus. -/
theorem map_rationalIsometryRealInvariantDifferentialGroupMeasure :
    @Measure.map (U.specialOrthogonalMatrixGroup ℝ)
        (V.specialOrthogonalMatrixGroup ℝ)
        U.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
        V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
        (rationalIsometryRealFormCongruenceData U V e).groupEquiv
        U.realInvariantDifferentialGroupMeasure =
      (Real.toNNReal
        |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)|)⁻¹ •
        V.realInvariantDifferentialGroupMeasure := by
  letI : MeasurableSpace (U.specialOrthogonalMatrixGroup ℝ) :=
    U.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
  letI : BorelSpace (U.specialOrthogonalMatrixGroup ℝ) :=
    U.realSpecialOrthogonalGroupBorelSpace_spinorNorm
  letI : MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
    V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
  letI : BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
    V.realSpecialOrthogonalGroupBorelSpace_spinorNorm
  let c := rationalIsometryRealFormCongruenceData U V e
  have hmap :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
      U.pairingMatrix V.pairingMatrix U.form_symm U.form_det_ne_zero
      V.form_symm V.form_det_ne_zero c
  have hscalar :=
    specialFormPreservingRealFormCongruenceHaarScalar_eq
      U.pairingMatrix V.pairingMatrix U.form_symm U.form_det_ne_zero
      V.form_symm V.form_det_ne_zero c
  rw [hscalar] at hmap
  rw [rationalIsometryRealFormCongruenceData_detScalar] at hmap
  exact hmap

end RationalQuadraticSpaceMatrix

end
