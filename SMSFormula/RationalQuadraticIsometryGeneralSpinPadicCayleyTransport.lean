import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicTangentHaar
import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberTopology
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyTranslatedChartTopology

/-!
# P-adic Cayley transport across anisotropic presentations

For a supplied anisotropic-complement presentation of the same native rank,
the scalar-extended tangent and special-orthogonal maps are literal matrix
conjugations.  Conjugation preserves the exact p-adic Cayley source and
identity target, so both restrictions are homeomorphisms and the canonical
identity-centered Cayley square commutes pointwise.

This is the algebraic and topological bridge needed to lift the already
computed additive tangent Haar factor to the local group measure.  It does not
compare independently selected Spin chart domains, transport a measure, or
form a finite-adelic cylinder.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Over `ℚ_p`, the supplied scalar-extended presentation is multiplication
by its rational block-to-ambient matrix. -/
theorem blockToAmbientBaseChangeIsometryEquiv_padic_eq_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (y : Fin (m + 1) → ℚ_[p]) :
    P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] y =
      Matrix.mulVec
        ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])) y := by
  classical
  let L :=
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).toLinearEquiv.toLinearMap
  let R := Matrix.toLin'
    ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]))
  have hLR : L = R := by
    apply (Pi.basisFun ℚ_[p] (Fin (m + 1))).ext
    intro i
    have hb : (Pi.basisFun ℚ_[p] (Fin (m + 1))) i =
        fun j ↦ algebraMap ℚ ℚ_[p] ((Pi.basisFun ℚ (Fin (m + 1))) i j) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    change P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
        ((Pi.basisFun ℚ_[p] (Fin (m + 1))) i) =
      Matrix.mulVec
        ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]))
        ((Pi.basisFun ℚ_[p] (Fin (m + 1))) i)
    rw [hb, P.blockToAmbientBaseChangeIsometryEquiv_rational hx ℚ_[p]]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      blockToAmbientRationalMatrix, LinearMap.toMatrix'_apply]
    simp [Pi.single_apply]
  change L y = R y
  rw [hLR]

/-- The inverse p-adic presentation is multiplication by the rational
ambient-to-block matrix. -/
theorem blockToAmbientBaseChangeIsometryEquiv_padic_symm_eq_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (y : Fin (m + 1) → ℚ_[p]) :
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).symm y =
      Matrix.mulVec
        ((P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])) y := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  apply E.injective
  have hleft : E.toLinearEquiv
      ((P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).symm y) = y :=
    E.apply_symm_apply y
  rw [hleft]
  change y = E (Matrix.mulVec N y)
  rw [P.blockToAmbientBaseChangeIsometryEquiv_padic_eq_mulVec hx p]
  change y = Matrix.mulVec M (Matrix.mulVec N y)
  calc
    y = Matrix.mulVec (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) y := by simp
    _ = Matrix.mulVec (M * N) y := by rw [hMN]
    _ = Matrix.mulVec M (Matrix.mulVec N y) :=
      (Matrix.mulVec_mulVec y M N).symm

set_option backward.isDefEq.respectTransparency false in
/-- The p-adic tangent transport is literal matrix conjugation. -/
theorem coe_blockToAmbientPadicSkewAdjointLinearEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]) * X.1 *
        (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p]) := by
  let C :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] →L[ℚ_[p]]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    ContinuousLinearMap.mulLeftRight ℚ_[p]
      (Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])
      ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]))
      ((P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p]))
  let L :
      (skewAdjointMatricesLieSubalgebra
          ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule.subtypeL.comp
      (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).toContinuousLinearMap
  let R :
      (skewAdjointMatricesLieSubalgebra
          ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    C.comp
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule.subtypeL
  have hLR : L = R := by
    have hlin : L.toLinearMap = R.toLinearMap := by
      apply (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
        (P.blockSpace hx).pairingMatrix).ext
      intro i
      change
        ((P.blockToAmbientPadicSkewAdjointLinearEquiv hx p
          (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
            (P.blockSpace hx).pairingMatrix i) :
            (skewAdjointMatricesLieSubalgebra
              (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) =
        C (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
          (P.blockSpace hx).pairingMatrix i)
      simp only [Matrix.skewAdjointScalarExtensionFinBasis,
        Matrix.skewAdjointScalarExtensionBasis,
        Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rw [P.blockToAmbientPadicSkewAdjointLinearEquiv_scalarExtension hx p,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul,
        P.coe_blockToAmbientSkewAdjointLinearEquiv_apply hx,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
      simp only [C, Matrix.map_mul, one_smul]
      exact (ContinuousLinearMap.mulLeftRight_apply ℚ_[p]
        (Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) _ _ _).symm
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hlin y
  change L X = R X
  exact DFunLike.congr_fun hLR X

/-- The native p-adic special-orthogonal presentation map is the same matrix
conjugation as the tangent map. -/
theorem coe_blockToAmbientPadicSpecialOrthogonalGroupContinuousMulEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : (P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]) :
    (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p] g).1.1.1) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) =
      (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]) *
        (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) *
        (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p]) := by
  classical
  ext i j
  let y : Fin (m + 1) → ℚ_[p] := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p] g).1.1.1) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) y =
        Matrix.mulVec
          ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p]) *
            (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) *
            (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])) y := by
    change Matrix.mulVec
        (P.blockToAmbientSpecialOrthogonalMatrixPoint ℚ_[p] hx
          ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup ℚ_[p] g)).1 y = _
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec ℚ_[p] hx]
    change
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
          (Matrix.mulVec (g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])
            ((P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).symm y)) = _
    rw [P.blockToAmbientBaseChangeIsometryEquiv_padic_eq_mulVec hx p,
      P.blockToAmbientBaseChangeIsometryEquiv_padic_symm_eq_mulVec hx p]
    rw [Matrix.mulVec_mulVec y]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  simpa [Matrix.mulVec, dotProduct, y, Pi.single_apply] using congrFun hvec i

private theorem isUnit_one_sub_presentationConjugate_iff
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1) :
    IsUnit (1 - M * X * N) ↔ IsUnit (1 - X) := by
  have hM : IsUnit M := isUnit_iff_exists_inv.mpr ⟨N, hMN⟩
  have hN : IsUnit N := isUnit_iff_exists_inv.mpr ⟨M, hNM⟩
  constructor
  · intro h
    have hprod : IsUnit (N * (1 - M * X * N) * M) :=
      by simpa only [Matrix.mul_assoc] using hN.mul (h.mul hM)
    have heq : N * (1 - M * X * N) * M = 1 - X := by
      calc
        N * (1 - M * X * N) * M =
            N * M - N * M * X * N * M := by noncomm_ring
        _ = 1 - X := by
          rw [hNM, Matrix.one_mul, Matrix.mul_assoc X N M, hNM,
            Matrix.mul_one]
    rw [heq] at hprod
    exact hprod
  · intro h
    have hprod : IsUnit (M * (1 - X) * N) :=
      by simpa only [Matrix.mul_assoc] using hM.mul (h.mul hN)
    have heq : M * (1 - X) * N = 1 - M * X * N := by
      calc
        M * (1 - X) * N = M * N - M * X * N := by noncomm_ring
        _ = 1 - M * X * N := by rw [hMN]
    rw [heq] at hprod
    exact hprod

/-- Presentation conjugation preserves the exact identity Cayley source. -/
theorem blockToAmbientPadicCayleySource_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X ∈
        Matrix.skewAdjointPadicCayleySource V.pairingMatrix p ↔
      X ∈ Matrix.skewAdjointPadicCayleySource
        (P.blockSpace hx).pairingMatrix p := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx)
  change IsUnit (1 -
      (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p])) ↔ IsUnit (1 - X.1)
  rw [P.coe_blockToAmbientPadicSkewAdjointLinearEquiv_apply hx p]
  exact isUnit_one_sub_presentationConjugate_iff M N X.1 hMN hNM

private theorem nonsing_inv_one_sub_presentationConjugate
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1)
    (hX : IsUnit (1 - X)) :
    (1 - M * X * N)⁻¹ = M * (1 - X)⁻¹ * N := by
  let B := 1 - M * X * N
  have hB : IsUnit B :=
    (isUnit_one_sub_presentationConjugate_iff M N X hMN hNM).2 hX
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hXdet : IsUnit (1 - X).det :=
    (Matrix.isUnit_iff_isUnit_det (1 - X)).mp hX
  apply hB.mul_left_cancel
  change B * B⁻¹ = B * (M * (1 - X)⁻¹ * N)
  rw [Matrix.mul_nonsing_inv B hBdet]
  change 1 = (1 - M * X * N) * (M * (1 - X)⁻¹ * N)
  symm
  calc
    (1 - M * X * N) * (M * (1 - X)⁻¹ * N) =
        M * (1 - X)⁻¹ * N - M * X * N * M * (1 - X)⁻¹ * N := by
      noncomm_ring
    _ = M * (1 - X)⁻¹ * N - M * X * (1 - X)⁻¹ * N := by
      rw [show M * X * N * M * (1 - X)⁻¹ * N =
          M * X * (N * M) * (1 - X)⁻¹ * N by
        simp only [Matrix.mul_assoc]]
      rw [hNM, Matrix.mul_one]
    _ = M * ((1 - X) * (1 - X)⁻¹) * N := by noncomm_ring
    _ = M * N := by rw [Matrix.mul_nonsing_inv (1 - X) hXdet]; simp
    _ = 1 := hMN

private theorem padicCayleyForwardMatrix_presentationConjugate
    (p : ℕ) [Fact (Nat.Prime p)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι ℚ_[p]) (hMN : M * N = 1) (hNM : N * M = 1)
    (hX : X ∈ Matrix.padicCayleySource p) :
    Matrix.padicCayleyForwardMatrix p (M * X * N) =
      M * Matrix.padicCayleyForwardMatrix p X * N := by
  rw [Matrix.padicCayleyForwardMatrix, Matrix.padicCayleyForwardMatrix]
  rw [nonsing_inv_one_sub_presentationConjugate M N X hMN hNM hX]
  calc
    (1 + M * X * N) * (M * (1 - X)⁻¹ * N) =
        M * (1 - X)⁻¹ * N + M * X * N * M * (1 - X)⁻¹ * N := by
      noncomm_ring
    _ = M * (1 - X)⁻¹ * N + M * X * (1 - X)⁻¹ * N := by
      rw [show M * X * N * M * (1 - X)⁻¹ * N =
          M * X * (N * M) * (1 - X)⁻¹ * N by
        simp only [Matrix.mul_assoc]]
      rw [hNM, Matrix.mul_one]
    _ = M * ((1 + X) * (1 - X)⁻¹) * N := by noncomm_ring

/-- The p-adic presentation tangent equivalence restricted to the exact
Cayley sources. -/
def blockToAmbientPadicCayleySourceHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySource (P.blockSpace hx).pairingMatrix p ≃ₜ
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p where
  toFun X := ⟨P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p X.1,
    (P.blockToAmbientPadicCayleySource_iff hx p X.1).2 X.2⟩
  invFun Y := ⟨(P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm Y.1,
    (P.blockToAmbientPadicCayleySource_iff hx p
      ((P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm Y.1)).1
      (by
        have heq : P.blockToAmbientPadicSkewAdjointLinearEquiv hx p
            ((P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm Y.1) = Y.1 := by
          change (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p)
              ((P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm Y.1) = Y.1
          exact (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).apply_symm_apply Y.1
        rw [heq]
        exact Y.2)⟩
  left_inv X := by
    apply Subtype.ext
    exact (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm_apply_apply X.1
  right_inv Y := by
    apply Subtype.ext
    exact (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).apply_symm_apply Y.1
  continuous_toFun :=
    (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).continuous.comp
      continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).symm.continuous.comp
      continuous_subtype_val |>.subtype_mk _

@[simp]
theorem blockToAmbientPadicCayleySourceHomeomorph_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource (P.blockSpace hx).pairingMatrix p) :
    (P.blockToAmbientPadicCayleySourceHomeomorph hx p X).1 =
      P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X.1 :=
  rfl

private theorem isUnit_one_add_presentationConjugate_iff
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1) :
    IsUnit (M * X * N + 1) ↔ IsUnit (X + 1) := by
  simpa [sub_eq_add_neg, add_comm] using
    (isUnit_one_sub_presentationConjugate_iff M N (-X) hMN hNM)

set_option backward.isDefEq.respectTransparency false in
/-- Presentation conjugation preserves the exact identity Cayley target in
the native units-valued special-orthogonal carrier. -/
theorem blockToAmbientPadicCayleyIdentityTarget_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : (P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]) :
    P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p] g ∈
        padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p ↔
      g ∈ padicCayleySpecialOrthogonalSubgroupInverseDomain
        (P.blockSpace hx).pairingMatrix p := by
  let M := (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  let N := (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx)
  rw [mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff,
    mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff]
  change IsUnit
      (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p] g).1.1.1 :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) + 1) ↔
    IsUnit ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) + 1)
  rw [P.coe_blockToAmbientPadicSpecialOrthogonalGroupContinuousMulEquiv_apply hx p]
  exact isUnit_one_add_presentationConjugate_iff M N (g.1.1.1 : Matrix _ _ ℚ_[p]) hMN hNM

/-- The p-adic special-orthogonal presentation equivalence restricted to the
exact identity Cayley targets. -/
def blockToAmbientPadicCayleyIdentityTargetHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalSubgroupInverseDomain
        (P.blockSpace hx).pairingMatrix p ≃ₜ
      padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p where
  toFun g := ⟨P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p] g.1,
    (P.blockToAmbientPadicCayleyIdentityTarget_iff hx p g.1).2 g.2⟩
  invFun h := ⟨(P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).symm h.1,
    (P.blockToAmbientPadicCayleyIdentityTarget_iff hx p
      ((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).symm h.1)).1
      (by
        have heq : P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]
            ((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).symm h.1) = h.1 :=
          (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).apply_symm_apply h.1
        rw [heq]
        exact h.2)⟩
  left_inv g := by
    apply Subtype.ext
    exact (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).symm_apply_apply g.1
  right_inv h := by
    apply Subtype.ext
    exact (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).apply_symm_apply h.1
  continuous_toFun :=
    (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).continuous.comp
      continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]).symm.continuous.comp
      continuous_subtype_val |>.subtype_mk _

/-- The canonical identity-centered Cayley homeomorphism on the native
units-valued special-orthogonal target. -/
def padicCayleySpecialOrthogonalIdentityHomeomorph
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySource W.pairingMatrix p ≃ₜ
      padicCayleySpecialOrthogonalSubgroupInverseDomain W.pairingMatrix p :=
  (Matrix.skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
      W.pairingMatrix p W.form_det_ne_zero).trans
    (padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
      W.pairingMatrix p)

/-- The canonical identity-centered p-adic Cayley chart commutes literally
with the supplied presentation on source and target. -/
theorem blockToAmbientPadicCayleyIdentityHomeomorph_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource (P.blockSpace hx).pairingMatrix p) :
    P.blockToAmbientPadicCayleyIdentityTargetHomeomorph hx p
        (padicCayleySpecialOrthogonalIdentityHomeomorph (P.blockSpace hx) p X) =
      padicCayleySpecialOrthogonalIdentityHomeomorph V p (P.blockToAmbientPadicCayleySourceHomeomorph hx p X) := by
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p] :=
    (P.ambientToBlockRationalMatrix hx).map (algebraMap ℚ ℚ_[p])
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change
    (((P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx ℚ_[p]
      (padicCayleySpecialOrthogonalIdentityHomeomorph (P.blockSpace hx) p X).1).1.1.1) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) i j = _
  rw [P.coe_blockToAmbientPadicSpecialOrthogonalGroupContinuousMulEquiv_apply hx p]
  change (M * Matrix.padicCayleyForwardMatrix p
      (X.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) * N) i j =
    (Matrix.padicCayleyForwardMatrix p
      (P.blockToAmbientPadicSkewAdjointLinearEquiv hx p X.1 : Matrix _ _ ℚ_[p])) i j
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (P.ambientToBlockRationalMatrix_mul_blockToAmbientRationalMatrix hx)
  rw [P.coe_blockToAmbientPadicSkewAdjointLinearEquiv_apply hx p]
  exact congrArg (fun A : Matrix _ _ ℚ_[p] => A i j)
    (padicCayleyForwardMatrix_presentationConjugate p M N
      (X.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) hMN hNM X.2).symm

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
