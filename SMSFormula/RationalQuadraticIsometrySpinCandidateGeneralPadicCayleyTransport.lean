import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralPadicTangentHaar
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralSpecialOrthogonal
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTransport

/-!
# P-adic Cayley transport under an arbitrary rational isometry

For two native rational quadratic matrices of the same rank, a supplied
rational isometry acts on the existing p-adic tangent and represented
special-orthogonal carriers by the same literal matrix conjugation.  This
conjugation preserves the canonical identity Cayley source and target, and
the resulting restricted homeomorphisms commute with the canonical Cayley
map.

No new chart, Haar measure, integral structure, raw certificate, quotient
measure, or Tamagawa value is selected.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 800000

variable {n : ℕ}
variable (U V : RationalQuadraticSpaceMatrix n)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

/-- Over `ℚ_p`, scalar extension of an arbitrary rational isometry is
multiplication by its entrywise scalar-extended rational matrix. -/
theorem rationalIsometryBaseChangeIsometryEquiv_padic_eq_mulVec
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) :
    rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p] y =
      Matrix.mulVec
        ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])) y := by
  classical
  let L :=
    (rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]
      ).toLinearEquiv.toLinearMap
  let R := Matrix.toLin'
    ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]))
  have hLR : L = R := by
    apply (Pi.basisFun ℚ_[p] (Fin n)).ext
    intro i
    have hb : (Pi.basisFun ℚ_[p] (Fin n)) i =
        fun j ↦ algebraMap ℚ ℚ_[p] ((Pi.basisFun ℚ (Fin n)) i j) := by
      ext j
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    change rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]
        ((Pi.basisFun ℚ_[p] (Fin n)) i) =
      Matrix.mulVec
        ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]))
        ((Pi.basisFun ℚ_[p] (Fin n)) i)
    rw [hb, rationalIsometryBaseChangeIsometryEquiv_rational]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      rationalIsometryMatrix, LinearMap.toMatrix'_apply]
    simp [Pi.single_apply]
  change L y = R y
  rw [hLR]

/-- The inverse scalar-extended p-adic isometry is multiplication by the
entrywise scalar-extended inverse rational matrix. -/
theorem rationalIsometryBaseChangeIsometryEquiv_padic_symm_eq_mulVec
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) :
    (rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]).symm y =
      Matrix.mulVec
        ((rationalIsometryInverseMatrix U V e).map
          (algebraMap ℚ ℚ_[p])) y := by
  let E := rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])
  let N := (rationalIsometryInverseMatrix U V e).map
    (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryMatrix_mul_inverseMatrix U V e)
  apply E.injective
  have hleft : E.toLinearEquiv (E.symm y) = y := E.apply_symm_apply y
  rw [hleft]
  change y = E (Matrix.mulVec N y)
  rw [rationalIsometryBaseChangeIsometryEquiv_padic_eq_mulVec]
  change y = Matrix.mulVec M (Matrix.mulVec N y)
  calc
    y = Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℚ_[p]) y := by simp
    _ = Matrix.mulVec (M * N) y := by rw [hMN]
    _ = Matrix.mulVec M (Matrix.mulVec N y) :=
      (Matrix.mulVec_mulVec y M N).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extended p-adic tangent equivalence is literal matrix
conjugation. -/
theorem coe_rationalIsometryPadicSkewAdjointLinearEquiv_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (rationalIsometryPadicSkewAdjointLinearEquiv U V e p X :
      Matrix (Fin n) (Fin n) ℚ_[p]) =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) * X.1 *
        (rationalIsometryInverseMatrix U V e).map
          (algebraMap ℚ ℚ_[p]) := by
  let C : Matrix (Fin n) (Fin n) ℚ_[p] →L[ℚ_[p]]
      Matrix (Fin n) (Fin n) ℚ_[p] :=
    ContinuousLinearMap.mulLeftRight ℚ_[p]
      (Matrix (Fin n) (Fin n) ℚ_[p])
      ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]))
      ((rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]))
  let L :
      (skewAdjointMatricesLieSubalgebra
          (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix (Fin n) (Fin n) ℚ_[p] :=
    (skewAdjointMatricesLieSubalgebra
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule.subtypeL.comp
      (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p
        ).toContinuousLinearMap
  let R :
      (skewAdjointMatricesLieSubalgebra
          (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
        Matrix (Fin n) (Fin n) ℚ_[p] :=
    C.comp (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule.subtypeL
  have hLR : L = R := by
    have hlin : L.toLinearMap = R.toLinearMap := by
      apply (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
        U.pairingMatrix).ext
      intro i
      change
        ((rationalIsometryPadicSkewAdjointLinearEquiv U V e p
          (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
            U.pairingMatrix i) :
            (skewAdjointMatricesLieSubalgebra
              (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
        C (Matrix.skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
          U.pairingMatrix i)
      simp only [Matrix.skewAdjointScalarExtensionFinBasis,
        Matrix.skewAdjointScalarExtensionBasis, Module.Basis.map_apply,
        Module.Basis.baseChange_apply]
      rw [rationalIsometryPadicSkewAdjointLinearEquiv_scalarExtension,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul,
        coe_rationalIsometrySkewAdjointLinearEquiv_apply,
        Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
      simp only [C, Matrix.map_mul, one_smul]
      exact (ContinuousLinearMap.mulLeftRight_apply ℚ_[p]
        (Matrix (Fin n) (Fin n) ℚ_[p]) _ _ _).symm
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hlin y
  change L X = R X
  exact DFunLike.congr_fun hLR X

/-- The arbitrary-isometry map on the native p-adic special-orthogonal group
is the same literal matrix conjugation. -/
theorem coe_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : U.specialOrthogonalMatrixGroup ℚ_[p]) :
    (((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e ℚ_[p] g).1.1.1) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
        (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
        (rationalIsometryInverseMatrix U V e).map
          (algebraMap ℚ ℚ_[p]) := by
  classical
  ext i j
  let y : Fin n → ℚ_[p] := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
            U V e ℚ_[p] g).1.1.1) : Matrix (Fin n) (Fin n) ℚ_[p]) y =
        Matrix.mulVec
          ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
            (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) *
            (rationalIsometryInverseMatrix U V e).map
              (algebraMap ℚ ℚ_[p])) y := by
    change Matrix.mulVec
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e ℚ_[p]
          (U.specialOrthogonalMatrixPointOfGroup ℚ_[p] g)).1 y = _
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    change rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]
        (Matrix.mulVec
          (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
          ((rationalIsometryBaseChangeIsometryEquiv U V e ℚ_[p]).symm y)) = _
    rw [rationalIsometryBaseChangeIsometryEquiv_padic_eq_mulVec,
      rationalIsometryBaseChangeIsometryEquiv_padic_symm_eq_mulVec]
    rw [Matrix.mulVec_mulVec y]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
  simpa [Matrix.mulVec, dotProduct, y, Pi.single_apply] using congrFun hvec i

private theorem isUnit_one_sub_arbitraryIsometryConjugate_iff
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

/-- Arbitrary-isometry conjugation preserves the exact identity Cayley
source. -/
theorem rationalIsometryPadicCayleySource_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : (skewAdjointMatricesLieSubalgebra
      (U.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    rationalIsometryPadicSkewAdjointLinearEquiv U V e p X ∈
        Matrix.skewAdjointPadicCayleySource V.pairingMatrix p ↔
      X ∈ Matrix.skewAdjointPadicCayleySource U.pairingMatrix p := by
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])
  let N := (rationalIsometryInverseMatrix U V e).map
    (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryMatrix_mul_inverseMatrix U V e)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryInverseMatrix_mul_matrix U V e)
  change IsUnit (1 -
      (rationalIsometryPadicSkewAdjointLinearEquiv U V e p X :
        Matrix (Fin n) (Fin n) ℚ_[p])) ↔ IsUnit (1 - X.1)
  rw [coe_rationalIsometryPadicSkewAdjointLinearEquiv_apply]
  exact isUnit_one_sub_arbitraryIsometryConjugate_iff M N X.1 hMN hNM

private theorem nonsing_inv_one_sub_arbitraryIsometryConjugate
    {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1)
    (hX : IsUnit (1 - X)) :
    (1 - M * X * N)⁻¹ = M * (1 - X)⁻¹ * N := by
  let B := 1 - M * X * N
  have hB : IsUnit B :=
    (isUnit_one_sub_arbitraryIsometryConjugate_iff M N X hMN hNM).2 hX
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

private theorem padicCayleyForwardMatrix_arbitraryIsometryConjugate
    (p : ℕ) [Fact (Nat.Prime p)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι ℚ_[p]) (hMN : M * N = 1) (hNM : N * M = 1)
    (hX : X ∈ Matrix.padicCayleySource p) :
    Matrix.padicCayleyForwardMatrix p (M * X * N) =
      M * Matrix.padicCayleyForwardMatrix p X * N := by
  rw [Matrix.padicCayleyForwardMatrix, Matrix.padicCayleyForwardMatrix]
  rw [nonsing_inv_one_sub_arbitraryIsometryConjugate M N X hMN hNM hX]
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

/-- Restriction of the arbitrary-isometry p-adic tangent equivalence to the
exact identity Cayley sources. -/
def rationalIsometryPadicCayleySourceHomeomorph
    (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySource U.pairingMatrix p ≃ₜ
      Matrix.skewAdjointPadicCayleySource V.pairingMatrix p where
  toFun X := ⟨rationalIsometryPadicSkewAdjointContinuousLinearEquiv
      U V e p X.1,
    (rationalIsometryPadicCayleySource_iff U V e p X.1).2 X.2⟩
  invFun Y :=
    ⟨(rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p).symm Y.1,
      (rationalIsometryPadicCayleySource_iff U V e p
        ((rationalIsometryPadicSkewAdjointContinuousLinearEquiv
          U V e p).symm Y.1)).1 (by
          have heq : rationalIsometryPadicSkewAdjointLinearEquiv U V e p
              ((rationalIsometryPadicSkewAdjointContinuousLinearEquiv
                U V e p).symm Y.1) = Y.1 := by
            change rationalIsometryPadicSkewAdjointContinuousLinearEquiv
                U V e p
                ((rationalIsometryPadicSkewAdjointContinuousLinearEquiv
                  U V e p).symm Y.1) = Y.1
            exact (rationalIsometryPadicSkewAdjointContinuousLinearEquiv
              U V e p).apply_symm_apply Y.1
          rw [heq]
          exact Y.2)⟩
  left_inv X := by
    apply Subtype.ext
    exact (rationalIsometryPadicSkewAdjointContinuousLinearEquiv
      U V e p).symm_apply_apply X.1
  right_inv Y := by
    apply Subtype.ext
    exact (rationalIsometryPadicSkewAdjointContinuousLinearEquiv
      U V e p).apply_symm_apply Y.1
  continuous_toFun :=
    (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p
      ).continuous.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (rationalIsometryPadicSkewAdjointContinuousLinearEquiv U V e p
      ).symm.continuous.comp continuous_subtype_val |>.subtype_mk _

@[simp]
theorem rationalIsometryPadicCayleySourceHomeomorph_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource U.pairingMatrix p) :
    (rationalIsometryPadicCayleySourceHomeomorph U V e p X).1 =
      rationalIsometryPadicSkewAdjointLinearEquiv U V e p X.1 :=
  rfl

private theorem isUnit_one_add_arbitraryIsometryConjugate_iff
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N X : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1) :
    IsUnit (M * X * N + 1) ↔ IsUnit (X + 1) := by
  simpa [sub_eq_add_neg, add_comm] using
    (isUnit_one_sub_arbitraryIsometryConjugate_iff M N (-X) hMN hNM)

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary-isometry conjugation preserves the exact identity Cayley target
in the native units-valued special-orthogonal carrier. -/
theorem rationalIsometryPadicCayleyIdentityTarget_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : U.specialOrthogonalMatrixGroup ℚ_[p]) :
    rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e ℚ_[p] g ∈
        padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p ↔
      g ∈ padicCayleySpecialOrthogonalSubgroupInverseDomain U.pairingMatrix p := by
  let M := (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])
  let N := (rationalIsometryInverseMatrix U V e).map
    (algebraMap ℚ ℚ_[p])
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryMatrix_mul_inverseMatrix U V e)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryInverseMatrix_mul_matrix U V e)
  rw [mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff,
    mem_padicCayleySpecialOrthogonalSubgroupInverseDomain_iff]
  change IsUnit
      (((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
        U V e ℚ_[p] g).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1) ↔
    IsUnit ((g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) + 1)
  rw [coe_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply]
  exact isUnit_one_add_arbitraryIsometryConjugate_iff M N
    (g.1.1.1 : Matrix _ _ ℚ_[p]) hMN hNM

/-- Restriction of arbitrary-isometry special-orthogonal transport to the
exact identity Cayley targets. -/
def rationalIsometryPadicCayleyIdentityTargetHomeomorph
    (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalSubgroupInverseDomain U.pairingMatrix p ≃ₜ
      padicCayleySpecialOrthogonalSubgroupInverseDomain V.pairingMatrix p where
  toFun g :=
    ⟨rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
        U V e ℚ_[p] g.1,
      (rationalIsometryPadicCayleyIdentityTarget_iff U V e p g.1).2 g.2⟩
  invFun h :=
    ⟨(rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
        U V e ℚ_[p]).symm h.1,
      (rationalIsometryPadicCayleyIdentityTarget_iff U V e p
        ((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
          U V e ℚ_[p]).symm h.1)).1 (by
          have heq : rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
              U V e ℚ_[p]
                ((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
                  U V e ℚ_[p]).symm h.1) = h.1 :=
            (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
              U V e ℚ_[p]).apply_symm_apply h.1
          rw [heq]
          exact h.2)⟩
  left_inv g := by
    apply Subtype.ext
    exact (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e ℚ_[p]).symm_apply_apply g.1
  right_inv h := by
    apply Subtype.ext
    exact (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e ℚ_[p]).apply_symm_apply h.1
  continuous_toFun :=
    (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e ℚ_[p]).continuous.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
      U V e ℚ_[p]).symm.continuous.comp continuous_subtype_val |>.subtype_mk _

/-- The canonical identity-centered p-adic Cayley chart commutes literally
with arbitrary-isometry transport on its exact source and target. -/
theorem rationalIsometryPadicCayleyIdentityHomeomorph_commutes
    {m : ℕ}
    (W Z : RationalQuadraticSpaceMatrix (m + 1))
    (f : W.quadraticForm.IsometryEquiv Z.quadraticForm)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource W.pairingMatrix p) :
    rationalIsometryPadicCayleyIdentityTargetHomeomorph W Z f p
        (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
          W p X) =
      AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph Z p
        (rationalIsometryPadicCayleySourceHomeomorph W Z f p X) := by
  let M := (rationalIsometryMatrix W Z f).map (algebraMap ℚ ℚ_[p])
  let N := (rationalIsometryInverseMatrix W Z f).map
    (algebraMap ℚ ℚ_[p])
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change
    (((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv W Z f ℚ_[p]
      (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
        W p X).1).1.1.1) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) i j = _
  rw [coe_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply]
  change (M * Matrix.padicCayleyForwardMatrix p
      (X.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) * N) i j =
    (Matrix.padicCayleyForwardMatrix p
      (rationalIsometryPadicSkewAdjointLinearEquiv W Z f p X.1 :
        Matrix _ _ ℚ_[p])) i j
  have hMN : M * N = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryMatrix_mul_inverseMatrix W Z f)
  have hNM : N * M = 1 := by
    simpa [M, N, Matrix.map_mul] using congrArg
      (fun A ↦ A.map (algebraMap ℚ ℚ_[p]))
      (rationalIsometryInverseMatrix_mul_matrix W Z f)
  rw [coe_rationalIsometryPadicSkewAdjointLinearEquiv_apply]
  exact congrArg (fun A : Matrix _ _ ℚ_[p] ↦ A i j)
    (padicCayleyForwardMatrix_arbitraryIsometryConjugate p M N
      (X.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) hMN hNM X.2).symm

end RationalQuadraticSpaceMatrix

end
