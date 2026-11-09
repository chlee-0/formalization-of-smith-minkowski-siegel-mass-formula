import SMSFormula.RationalAdeleTranslatedTestPoisson
import SMSFormula.RationalAdeleOrthogonalFourierCovariance
import SMSFormula.RationalAdelePolarDualThetaFiniteness
import SMSFormula.RationalCliffordGeneralSpinComplexCutoffIntegral
import SMSFormula.RationalAdeleCovarianceCutoffTransport

/-!
# The geometric covariance for the dual-carrier test

Obligation 4 asks for the covariance on a separating admissible pair with each side proved
independently.  One side is closed: the standard test.  The other side of the pair is the polar
Weyl transform, which is a constant multiple of the dual-carrier test, so what is needed is the
covariance of that test, proved on its own and not read off the first one.

It follows from the same Poisson theorem.  The dual carrier is the preimage of the integral finite
adele vectors under the finite adelic polar matrix, and that matrix is a unit because the polar
determinant is a nonzero rational.  So the translate of the dual-carrier test by a concrete
full-adelic special orthogonal point is the same real Gaussian times the indicator of the preimage
of the integral vectors under the product unit `C_f * g_f` -- exactly the shape the existing
unit-preimage Poisson theorem covers.  Composing with the existing intertwining gives the
covariance, and the existing descent carries it to the complex cutoff integral.

Negative scope: this is a second instance of the same theorem, not a comparison of the two.  No
shell agreement, no Eisenstein comparison and no Tamagawa evaluation is involved, and no relation
between the two tests' shell sums is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The finite adelic polar matrix is a unit: its determinant is the image of the nonzero rational
polar determinant. -/
theorem finiteAdelicPolarMatrix_isUnit_det (V : RationalQuadraticSpaceMatrix n) :
    IsUnit V.finiteAdelicPolarMatrix.det := by
  change IsUnit (((algebraMap ℚ RationalFiniteAdele).mapMatrix V.polarMatrix).det)
  rw [← RingHom.map_det]
  exact IsUnit.map (algebraMap ℚ RationalFiniteAdele)
    (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero)

/-- The finite adelic polar matrix as a matrix unit. -/
def finiteAdelicPolarMatrixUnit (V : RationalQuadraticSpaceMatrix n) :
    (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det _).2 V.finiteAdelicPolarMatrix_isUnit_det).unit

@[simp]
theorem finiteAdelicPolarMatrixUnit_val (V : RationalQuadraticSpaceMatrix n) :
    (V.finiteAdelicPolarMatrixUnit : Matrix (Fin n) (Fin n) RationalFiniteAdele) =
      V.finiteAdelicPolarMatrix :=
  IsUnit.unit_spec _

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The dual-carrier analogue of the carrier identification: the translate of the dual-carrier test
by a concrete full-adelic special orthogonal point keeps the real Gaussian factor exactly and moves
only the finite carrier, which is the preimage of the integral vectors under the product of the
polar matrix and the finite component. -/
theorem rationalAdeleVectorPolarGaussianDualTest_concreteFullAdelicSpecialOrthogonal_mulVec
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianDualTest L b (h.1.1.1.mulVec x) =
      polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
        RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
          ((L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *
            ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1)).mulVec
            (rationalAdeleVectorFinitePart n x)) := by
  unfold rationalAdeleVectorPolarGaussianDualTest
  rw [L.rationalAdeleVectorRealPart_concreteFullAdelicSpecialOrthogonal_mulVec,
    L.rationalAdeleVectorFinitePart_concreteFullAdelicSpecialOrthogonal_mulVec,
    RationalQuadraticSpaceMatrix.polarRealGaussian_realSpecialOrthogonal L b
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1,
    RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator, Matrix.mulVec_mulVec]

/-- The recognition for the dual-carrier test: its translate is a unit-preimage test, so its
rational-diagonal theta equals that of its polar Weyl transform, at the original width. -/
theorem tsum_polarGaussianDualTest_translate_poisson_weyl
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianDualTest L b
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (fun x ↦ rationalAdeleVectorPolarGaussianDualTest L b (h.1.1.1.mulVec x))
          (rationalAdeleVectorDiagonal n y) := by
  classical
  set M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ :=
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixUnit *
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1 with hM
  have hMval : (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *
        ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1) := by
    rw [hM, Units.val_mul,
      RationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixUnit_val]
  have htest : (fun x : Fin n → RationalAdele ↦
      rationalAdeleVectorPolarGaussianDualTest L b (h.1.1.1.mulVec x)) =
      fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
        {y : Fin n → RationalFiniteAdele | (M.1).mulVec y ∈ integralFiniteAdeleVectors n}.indicator
          (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalAdeleVectorFinitePart n x) := by
    funext x
    rw [L.rationalAdeleVectorPolarGaussianDualTest_concreteFullAdelicSpecialOrthogonal_mulVec]
    congr 1
    rw [← hMval]
    by_cases hx : (M.1).mulVec (rationalAdeleVectorFinitePart n x) ∈ integralFiniteAdeleVectors n
    · rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hx,
        Set.indicator_of_mem (by exact hx)]
      rfl
    · rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx,
        Set.indicator_of_notMem (by exact hx)]
  exact Eq.trans (tsum_congr fun q ↦ congrFun htest _)
    (Eq.trans (tsum_polarGaussianTensor_unitPreimageCarrier_poisson_weyl L hb M)
      (by rw [htest]))

/-- The geometric covariance for the dual-carrier test: at every concrete full-adelic special
orthogonal point, its rational-diagonal theta equals that of its polar Weyl transform.  Proved on
its own, from the dual carrier's own Poisson identity and the existing intertwining. -/
theorem tsum_polarGaussianDualTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianDualTest L b
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianDualTest L b)
          (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n y)) := by
  rw [tsum_polarGaussianDualTest_translate_poisson_weyl L hb h]
  refine tsum_congr fun y ↦ ?_
  have hmat : ((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h).1⁻¹.1⁻¹).1 =
      h.1.1.1 := by
    simp [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix]
  have hint := L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_fullAdelicOrthogonal
    ((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h).1⁻¹)
    (rationalAdeleVectorPolarGaussianDualTest L b) (rationalAdeleVectorDiagonal n y)
  rw [hmat] at hint
  exact hint

/-- The covariance at the matrix special orthogonal group. -/
theorem tsum_polarGaussianDualTest_weyl_covariance_matrixGroup
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (k : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianDualTest L b
        (k.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianDualTest L b)
          (k.1.1.1.mulVec (rationalAdeleVectorDiagonal n y)) := by
  have hmat : (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv k).1.1.1 =
      k.1.1.1 := L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix k
  have hcov := tsum_polarGaussianDualTest_weyl_covariance L hb
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv k)
  rwa [hmat] at hcov

/-- The covariance of the complex theta at every actual full-adelic `GSpin` point. -/
theorem fullAdelicCliffordGeneralSpinComplexTheta_polarGaussianDualTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (rationalAdeleVectorPolarGaussianDualTest L b) g =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianDualTest L b)) g :=
  tsum_polarGaussianDualTest_weyl_covariance_matrixGroup L hb (g.matrixGroup⁻¹)

/-- The transport: the complex cutoff integral of the dual-carrier test equals that of its polar
Weyl transform.  The two descended integrands are pointwise equal, so the difference is the zero
function and no further integrability input is needed. -/
theorem complexCutoffIntegral_polarGaussianDualTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (f : ℝ → ENNReal) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (rationalAdeleVectorPolarGaussianDualTest L b) f =
      L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianDualTest L b)) f := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z ↦ ?_)
  induction Z using Quot.ind with
  | _ g =>
    exact fullAdelicCliffordGeneralSpinComplexTheta_polarGaussianDualTest_weyl_covariance L hb g

/-- The existing identification of the polar Weyl transform of the standard test, as a pointwise
identity at a complex width. -/
theorem rationalAdeleRankOneWeylOperator_polarGaussianLattice_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (y : Fin n → RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L b) y =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / b ^ (1 / 2 : ℂ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTest L b⁻¹ y := by
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb,
    rationalAdeleVectorPolarGaussianLatticeFourierProduct_eq_const_mul_dualTest]

/-- The complex cutoff integral of the polar Weyl transform of the standard test, through the
dual-carrier test at the reciprocal width. -/
theorem complexCutoffIntegral_weyl_polarGaussianLatticeTest_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (f : ℝ → ENNReal) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) f =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
          (rationalAdeleVectorPolarGaussianDualTest L ((a⁻¹ : ℝ) : ℂ)) f := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hinv : ((a : ℂ))⁻¹ = ((a⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hpt : L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) =
      fun y ↦ ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTest L ((a⁻¹ : ℝ) : ℂ) y := by
    funext y
    rw [L.rationalAdeleRankOneWeylOperator_polarGaussianLattice_eq_const_mul_dual hb y, hinv]
  rw [hpt]
  exact L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_const_smul _ _ f

/-- The separating pair, both sides independent.  The complex cutoff integral of the standard test
equals the explicit constant times that of the polar Weyl transform of the dual-carrier test at the
reciprocal width.  The first equality is the standard test's own covariance; the second is the
dual-carrier test's own covariance, proved above from its own Poisson identity -- neither side is
read off the other. -/
theorem complexCutoffIntegral_polarGaussianLatticeTest_eq_const_mul_weyl_dual
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (f : ℝ → ENNReal) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) f =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (rationalAdeleVectorPolarGaussianDualTest L ((a⁻¹ : ℝ) : ℂ))) f := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hbinv : 0 < (((a⁻¹ : ℝ) : ℂ)).re := by simpa using inv_pos.2 ha
  rw [complexCutoffIntegral_polarGaussianLatticeTest_weyl_covariance L hb f,
    L.complexCutoffIntegral_weyl_polarGaussianLatticeTest_eq_const_mul_dual ha f,
    ← complexCutoffIntegral_polarGaussianDualTest_weyl_covariance L hbinv f]

end PositiveDefiniteIntegralLattice

end
