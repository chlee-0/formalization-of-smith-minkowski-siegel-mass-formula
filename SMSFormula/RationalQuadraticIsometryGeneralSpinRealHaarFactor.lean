import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberTransportedTargetDensity
import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarCancellation

/-!
# Real presentation Haar factor

A supplied anisotropic-complement presentation has a rational tangent
determinant even though its block and ambient coordinate ranks are initially
indexed differently.  This file identifies the corresponding real `GSpin`
Haar comparison factor with the reciprocal archimedean norm of that
determinant.

The proof first uses the forced equality of ranks to realize the presentation
as an explicit real-form congruence.  Its exact tangent and special-orthogonal
maps yield the fixed product-density Jacobian.  That density is restricted to
the overlap of the independently chosen central-fiber
charts, and a compact positive-finite Haar neighborhood inside the overlap
cancels the comparison scalar.  No chart domains are equated and no
Haar normalization is chosen or rescaled.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped Matrix Matrix.Norms.Operator TensorProduct ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

noncomputable local instance realFactorRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance realFactorRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance realFactorBlockRealSOGroupMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℝ) :=
  (P.blockSpace hx).realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance realFactorBlockRealSOGroupBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℝ) :=
  (P.blockSpace hx).realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance realFactorAmbientRealSOGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance realFactorAmbientRealSOGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

def blockToAmbientRealFormCongruenceUnit
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : GL (Fin (m + 1)) ℝ := by
  let N := (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ)
  let M := (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ)
  have hNM : N * M = 1 := by
    simpa [N, M, Matrix.map_mul] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ))
      (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx)
  have hdet : N.det ≠ 0 := by
    intro h
    have hd := congrArg Matrix.det hNM
    rw [Matrix.det_mul, h] at hd
    simp at hd
  exact Matrix.GeneralLinearGroup.mkOfDetNeZero N hdet

@[simp]
theorem coe_blockToAmbientRealFormCongruenceUnit
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRealFormCongruenceUnit hx :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ) := by
  simp [blockToAmbientRealFormCongruenceUnit,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

@[simp]
theorem coe_blockToAmbientRealFormCongruenceUnit_inv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
        GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ) := by
  let N := (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ)
  let M := (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ)
  have hNM : N * M = 1 := by
    simpa [N, M, Matrix.map_mul] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ))
      (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx)
  have hu :
      (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
          GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * N = 1 := by
    have hgrp : (P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ *
        P.blockToAmbientRealFormCongruenceUnit hx = 1 := by simp
    have hmat := congrArg
      (fun z : GL (Fin (m + 1)) ℝ =>
        (z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) hgrp
    have hmat' :
        (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
            GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
          (P.blockToAmbientRealFormCongruenceUnit hx :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 1 := by
      simpa only [Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_one] using hmat
    rw [P.coe_blockToAmbientRealFormCongruenceUnit hx] at hmat'
    exact hmat'
  show (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
      GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = M
  calc
    (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
        GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
          GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * 1 := by rw [Matrix.mul_one]
    _ = (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
          GL (Fin (m + 1)) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * (N * M) := by rw [hNM]
    _ = M := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem coe_blockToAmbientRealSkewAdjointLinearEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (X : (skewAdjointMatricesLieSubalgebra
      ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule) :
    (P.blockToAmbientRealSkewAdjointLinearEquiv hx X :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ) * X.1 *
        (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ) := by
  let C :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ
      (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ))
      ((P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ))
  let L :
      (skewAdjointMatricesLieSubalgebra
          ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
      (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx).toContinuousLinearMap
  let R :
      (skewAdjointMatricesLieSubalgebra
          ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    C.comp
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL
  have hLR : L = R := by
    have hlin : L.toLinearMap = R.toLinearMap := by
      apply (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
        (P.blockSpace hx).pairingMatrix).ext
      intro i
      change
        ((P.blockToAmbientRealSkewAdjointLinearEquiv hx
          (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
            (P.blockSpace hx).pairingMatrix i) :
            (skewAdjointMatricesLieSubalgebra
              (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        C (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
          (P.blockSpace hx).pairingMatrix i)
      simp only [Matrix.skewAdjointScalarExtensionFinBasis,
        Matrix.skewAdjointScalarExtensionBasis,
        Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rw [P.blockToAmbientRealSkewAdjointLinearEquiv_scalarExtension hx,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul,
        P.coe_blockToAmbientSkewAdjointLinearEquiv_apply hx,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
      simp only [C, Matrix.map_mul, one_smul]
      exact (ContinuousLinearMap.mulLeftRight_apply ℝ
        (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) _ _ _).symm
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hlin y
  change L X = R X
  exact DFunLike.congr_fun hLR X

def blockToAmbientRealFormCongruenceData
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    SpecialOrthogonalRealFormCongruenceData
      (P.blockSpace hx).pairingMatrix V.pairingMatrix where
  unit := P.blockToAmbientRealFormCongruenceUnit hx
  congruence := by
    rw [P.coe_blockToAmbientRealFormCongruenceUnit hx]
    have hQ :
        (P.ambientToBlockRationalMatrix hx)ᵀ * (P.blockSpace hx).pairingMatrix *
            P.ambientToBlockRationalMatrix hx = V.pairingMatrix := by
      let M := P.blockToAmbientRationalMatrix hx
      let N := P.ambientToBlockRationalMatrix hx
      have hMN : M * N = 1 :=
        P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx
      have hform : Mᵀ * V.pairingMatrix * M = (P.blockSpace hx).pairingMatrix :=
        P.blockToAmbientRationalMatrix_form_congruence hx
      calc
        Nᵀ * (P.blockSpace hx).pairingMatrix * N =
            Nᵀ * (Mᵀ * V.pairingMatrix * M) * N := by rw [hform]
        _ = (M * N)ᵀ * V.pairingMatrix * (M * N) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = V.pairingMatrix := by rw [hMN, Matrix.transpose_one]; simp
    simpa [Matrix.map_mul, Matrix.transpose_map] using congrArg
      (fun A => A.map (algebraMap ℚ ℝ)) hQ

theorem blockToAmbientRealFormCongruenceData_tangentEquiv_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRealFormCongruenceData hx).tangentEquiv =
      P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx := by
  apply DFunLike.ext _ _
  intro X
  apply Subtype.ext
  rw [SpecialOrthogonalRealFormCongruenceData.coe_tangentEquiv_apply]
  change
    (P.blockToAmbientRealFormCongruenceUnit hx :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)⁻¹ * X.1 *
      (P.blockToAmbientRealFormCongruenceUnit hx :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = _
  rw [show
      ((P.blockToAmbientRealFormCongruenceUnit hx :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)⁻¹) =
        (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ :
          GL (Fin (m + 1)) ℝ) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) by
      exact (Matrix.GeneralLinearGroup.coe_inv _).symm]
  rw [P.coe_blockToAmbientRealFormCongruenceUnit_inv hx,
    P.coe_blockToAmbientRealFormCongruenceUnit hx]
  change
    (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ) * X.1 *
        (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ) =
      (P.blockToAmbientRealSkewAdjointLinearEquiv hx X :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  exact (P.coe_blockToAmbientRealSkewAdjointLinearEquiv_apply hx X).symm

set_option maxRecDepth 10000 in
theorem blockToAmbientRealFormCongruenceData_detScalar
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRealFormCongruenceData hx).detScalar =
      (P.blockToAmbientSkewAdjointDetScalar hx : ℝ) := by
  rw [SpecialOrthogonalRealFormCongruenceData.detScalar]
  rw [P.blockToAmbientRealFormCongruenceData_tangentEquiv_eq hx]
  exact P.blockToAmbientRealSkewAdjointDet_apply hx

theorem blockToAmbientBaseChangeIsometryEquiv_real_eq_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : Fin (m + 1) → ℝ) :
    P.blockToAmbientBaseChangeIsometryEquiv hx ℝ y =
      Matrix.mulVec
        ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ)) y := by
  classical
  let L :=
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℝ).toLinearEquiv.toLinearMap
  let R := Matrix.toLin'
    ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ))
  have hLR : L = R := by
    apply (Pi.basisFun ℝ (Fin (m + 1))).ext
    intro i
    have hb : (Pi.basisFun ℝ (Fin (m + 1))) i =
        fun j ↦ algebraMap ℚ ℝ ((Pi.basisFun ℚ (Fin (m + 1))) i j) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    change P.blockToAmbientBaseChangeIsometryEquiv hx ℝ
        ((Pi.basisFun ℝ (Fin (m + 1))) i) =
      Matrix.mulVec
        ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ))
        ((Pi.basisFun ℝ (Fin (m + 1))) i)
    rw [hb, P.blockToAmbientBaseChangeIsometryEquiv_rational hx]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      blockToAmbientRationalMatrix, LinearMap.toMatrix'_apply]
    simp [Pi.single_apply]
  change L y = R y
  rw [hLR]

theorem ambientToBlockBaseChangeIsometryEquiv_real_eq_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : Fin (m + 1) → ℝ) :
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℝ).symm y =
      Matrix.mulVec
        ((P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ)) y := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx ℝ
  let M := (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ)
  let N := (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ)
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℝ))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  apply E.injective
  have hleft : E.toLinearEquiv
      ((P.blockToAmbientBaseChangeIsometryEquiv hx ℝ).symm y) = y :=
    E.apply_symm_apply y
  rw [hleft]
  change y = E (Matrix.mulVec N y)
  rw [P.blockToAmbientBaseChangeIsometryEquiv_real_eq_mulVec hx]
  change y = Matrix.mulVec M (Matrix.mulVec N y)
  calc
    y = Matrix.mulVec (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) y := by simp
    _ = Matrix.mulVec (M * N) y := by rw [hMN]
    _ = Matrix.mulVec M (Matrix.mulVec N y) :=
      (Matrix.mulVec_mulVec y M N).symm

theorem coe_blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixGroup ℝ) :
    (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ g).1.1.1) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ) *
        (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
        (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ) := by
  classical
  ext i j
  let y : Fin (m + 1) → ℝ := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ g).1.1.1) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) y =
        Matrix.mulVec
          ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℝ) *
            (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
            (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℝ)) y := by
    change Matrix.mulVec
        (P.blockToAmbientSpecialOrthogonalMatrixPoint ℝ hx
          ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup ℝ g)).1 y = _
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec ℝ hx]
    change
      P.blockToAmbientBaseChangeIsometryEquiv hx ℝ
          (Matrix.mulVec (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
            ((P.blockToAmbientBaseChangeIsometryEquiv hx ℝ).symm y)) = _
    rw [P.blockToAmbientBaseChangeIsometryEquiv_real_eq_mulVec hx,
      P.ambientToBlockBaseChangeIsometryEquiv_real_eq_mulVec hx]
    rw [Matrix.mulVec_mulVec y]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  simpa [Matrix.mulVec, dotProduct, y, Pi.single_apply] using congrFun hvec i

theorem blockToAmbientRealFormCongruenceData_groupEquiv_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRealFormCongruenceData hx).groupEquiv =
      P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ := by
  apply DFunLike.ext _ _
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [SpecialOrthogonalRealFormCongruenceData.coe_groupEquiv_apply]
  change
    (((P.blockToAmbientRealFormCongruenceUnit hx)⁻¹ : GL (Fin (m + 1)) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * g.1.1.1 *
      (P.blockToAmbientRealFormCongruenceUnit hx :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = _
  rw [P.coe_blockToAmbientRealFormCongruenceUnit_inv hx,
    P.coe_blockToAmbientRealFormCongruenceUnit hx]
  exact
    (P.coe_blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv_apply hx g).symm

theorem map_blockToAmbientRealInvariantDifferentialGroupMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ)
        (P.blockSpace hx).realInvariantDifferentialGroupMeasure =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ •
        V.realInvariantDifferentialGroupMeasure := by
  let c := P.blockToAmbientRealFormCongruenceData hx
  have hmap :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
      (P.blockSpace hx).pairingMatrix V.pairingMatrix
      (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero
      V.form_symm V.form_det_ne_zero c
  have hscalar :=
    specialFormPreservingRealFormCongruenceHaarScalar_eq
      (P.blockSpace hx).pairingMatrix V.pairingMatrix
      (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero
      V.form_symm V.form_det_ne_zero c
  rw [hscalar] at hmap
  rw [P.blockToAmbientRealFormCongruenceData_groupEquiv_eq hx,
    P.blockToAmbientRealFormCongruenceData_detScalar hx] at hmap
  exact hmap

set_option backward.isDefEq.respectTransparency false in
theorem map_blockToAmbientRealCentralFiberProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℝ)
        (P.blockSpace hx).realCliffordGeneralSpinHorizontalDifferentialProductMeasure =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ •
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure := by
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℝˣ)
  letI : SigmaFinite
      (P.blockSpace hx).realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
      (P.blockSpace hx).form_det_ne_zero
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  have hunit : Measurable (id : ℝˣ → ℝˣ) := measurable_id
  have hso : Measurable
      (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ) :=
    (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ).measurable
  change Measure.map
      (Prod.map id
        (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℝ))
      ((Measure.haar : Measure ℝˣ).prod
        (P.blockSpace hx).realInvariantDifferentialGroupMeasure) = _
  rw [← Measure.map_prod_map _ _ hunit hso, Measure.map_id,
    P.map_blockToAmbientRealInvariantDifferentialGroupMeasure hx]
  rw [realCliffordGeneralSpinHorizontalDifferentialProductMeasure]
  exact Measure.prod_smul_right
    (μ := (Measure.haar : Measure ℝˣ))
    (ν := V.realInvariantDifferentialGroupMeasure)
    (((Real.toNNReal
      |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ : ℝ≥0) :
        ℝ≥0∞)

set_option backward.isDefEq.respectTransparency false in
/-- The exact target-overlap transition carries the transported block product
density by the reciprocal archimedean tangent modulus. -/
theorem map_transportedRealCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx)
        (P.transportedRealCentralFiberTargetOverlapProductMeasure hx) =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ •
        P.ambientRealCentralFiberTargetOverlapProductMeasure hx := by
  let e := P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx
  let S := P.transportedRealCentralFiberTargetOverlap hx
  let T := P.ambientRealCentralFiberTargetOverlap hx
  let μ := P.transportedBlockRealCentralFiberProductMeasure hx
  let ν := V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
  let q : ℝ≥0 :=
    (Real.toNNReal
      |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹
  have hS : MeasurableSet S :=
    (P.isOpen_transportedRealCentralFiberTargetOverlap hx).measurableSet
  have hT : MeasurableSet T :=
    (P.isOpen_ambientRealCentralFiberTargetOverlap hx).measurableSet
  apply (MeasurableEmbedding.subtype_coe hT).map_injective
  rw [Measure.map_map continuous_subtype_val.measurable e.measurable]
  rw [show (Subtype.val ∘ e) =
      (Subtype.val : S → ℝˣ × V.specialOrthogonalMatrixGroup ℝ) by
        funext y
        exact P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph_apply
          hx y]
  rw [transportedRealCentralFiberTargetOverlapProductMeasure,
    ambientRealCentralFiberTargetOverlapProductMeasure]
  rw [map_comap_subtype_coe hS, Measure.map_smul,
    map_comap_subtype_coe hT]
  change μ.restrict S = q • ν.restrict T
  rw [show S = T by
    exact P.transportedRealCentralFiberTargetOverlap_eq_ambient hx]
  rw [← Measure.restrict_smul]
  congr 1
  exact P.map_blockToAmbientRealCentralFiberProductMeasure hx

/-- The real presentation Haar factor is the reciprocal archimedean norm of
the rational tangent determinant. -/
theorem blockToAmbientRealGeneralSpinHorizontalHaarScalar_fin_add_one_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ := by
  let e := P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx
  let T := P.ambientRealCentralFiberTargetOverlap hx
  let μ := P.ambientRealCentralFiberTargetOverlapProductMeasure hx
  let ν := V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
  let c := P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx
  let q : ℝ≥0 :=
    (Real.toNNReal
      |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹
  have hc :=
    P.map_transportedRealCentralFiberTargetOverlapHaarMeasure_eq_smul hx
  rw [P.transportedRealCentralFiberTargetOverlapHaarMeasure_eq_product hx,
    P.ambientRealCentralFiberTargetOverlapHaarMeasure_eq_product hx] at hc
  have hq :=
    P.map_transportedRealCentralFiberTargetOverlapProductMeasure hx
  have hscalarMeasure : (c : ℝ≥0∞) • μ = (q : ℝ≥0∞) • μ := by
    calc
      (c : ℝ≥0∞) • μ = Measure.map e
          (P.transportedRealCentralFiberTargetOverlapProductMeasure hx) :=
        hc.symm
      _ = (q : ℝ≥0∞) • μ := hq
  have hT : IsOpen T :=
    P.isOpen_ambientRealCentralFiberTargetOverlap hx
  have honeTransported :
      (1 : V.CliffordGeneralSpinIntrinsicPoint ℝ) ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source := by
    rw [P.mem_blockToAmbientTransportedRealCentralFiberIdentityChart_source_iff hx]
    change (P.blockToAmbientGeneralSpinMulEquiv (A := ℝ) hx).symm 1 ∈
      (P.blockSpace hx
        |>.realCliffordGeneralSpinCentralFiberIdentityChart).source
    rw [map_one]
    exact P.blockSpace hx
      |>.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
  have honeAmbient :
      (1 : V.CliffordGeneralSpinIntrinsicPoint ℝ) ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source :=
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
  have hTnonempty : T.Nonempty := by
    refine ⟨V.realCliffordGeneralSpinCentralFiberIdentityChart 1,
      V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source honeAmbient,
      ?_⟩
    change V.realCliffordGeneralSpinCentralFiberIdentityChart.symm
        (V.realCliffordGeneralSpinCentralFiberIdentityChart 1) ∈
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
    rw [V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv honeAmbient]
    exact honeTransported
  obtain ⟨y, hy⟩ := hTnonempty
  obtain ⟨K, hK, hyK, hKT⟩ := exists_compact_subset hT hy
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hμmap : Measure.map
      (Subtype.val : P.ambientRealCentralFiberTargetOverlap hx →
        ℝˣ × V.specialOrthogonalMatrixGroup ℝ) μ = ν.restrict T := by
    dsimp only [μ, ν, T]
    rw [ambientRealCentralFiberTargetOverlapProductMeasure]
    exact map_comap_subtype_coe hT.measurableSet _
  have hpush := congrArg
    (Measure.map
      (Subtype.val : P.ambientRealCentralFiberTargetOverlap hx →
        ℝˣ × V.specialOrthogonalMatrixGroup ℝ)) hscalarMeasure
  rw [Measure.map_smul, Measure.map_smul, hμmap] at hpush
  have hmass := congrArg
    (fun ρ : Measure (ℝˣ × V.specialOrthogonalMatrixGroup ℝ) => ρ K) hpush
  change (c : ℝ≥0∞) * (ν.restrict T) K =
    (q : ℝ≥0∞) * (ν.restrict T) K at hmass
  rw [Measure.restrict_apply hKmeas, Set.inter_eq_left.mpr hKT] at hmass
  letI : Measure.IsHaarMeasure ν :=
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure_isHaarMeasure
  have hν0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨y, hyK⟩).ne'
  have hνtop : ν K ≠ ∞ := hK.measure_ne_top
  apply ENNReal.coe_injective
  apply (ENNReal.mul_right_inj hν0 hνtop).mp
  simpa only [mul_comm] using hmass

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The real presentation Haar factor is the reciprocal archimedean norm of
the rational tangent determinant, in the presentation's intrinsic ranks. -/
theorem blockToAmbientRealGeneralSpinHorizontalHaarScalar_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ := by
  have hdim := P.dimension_add_one hx
  subst n
  exact P.blockToAmbientRealGeneralSpinHorizontalHaarScalar_fin_add_one_eq hx

/-- Consequently the fixed real horizontal group Haar commutes with the
presentation map with the literal reciprocal tangent modulus. -/
theorem map_blockToAmbientRealGeneralSpinHorizontalMeasure_eq_modulus_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure) =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ •
        V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  rw [P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_eq_smul hx,
    P.blockToAmbientRealGeneralSpinHorizontalHaarScalar_eq hx]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
