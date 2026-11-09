import SMSFormula.RationalAdelePolarDualThetaFiniteness

/-!
# Raw finiteness for the Weyl transform of the standard test

The Weyl generator carries the standard polar Gaussian--lattice test to the polar Gaussian
Fourier product against the polar dual indicator.  The archimedean Fourier product is, by the
already computed coordinate formula, a constant multiple of the polar Gaussian at the
reciprocal width; so the Weyl transform is a constant multiple of the dual-carrier test whose
theta finiteness is available.

This turns the previous obstruction -- that no multiple of the standard test dominates the Weyl
transform -- into a proof, by comparing against the dual carrier instead of the standard one.

Negative scope: only the nonnegative modulus layer is treated.  No Fourier inversion, no
interchange of the transform with an integral, no Poisson identity and no complex integrability
statement is asserted here.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The archimedean Fourier product is a rescaled Gaussian -/

/-- The polar Fourier product is a constant multiple of the polar Gaussian at the
reciprocal width. -/
theorem polarRealGaussianFourierProduct_eq_const_mul
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (y : Fin n → ℝ) :
    polarRealGaussianFourierProduct L b y =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / b ^ (1 / 2 : ℂ)) ^ n) *
        polarRealGaussian L b⁻¹ y := by
  rw [polarRealGaussianFourierProduct, polarRealGaussian,
    realCoordinateGaussianFourierProduct_eq_const_mul]
  ring

/-- The identification: the Weyl transform of the standard test is a constant multiple of the
dual-carrier test at the reciprocal width. -/
theorem rationalAdeleVectorPolarGaussianLatticeFourierProduct_eq_const_mul_dualTest
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (y : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeFourierProduct L b y =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / b ^ (1 / 2 : ℂ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTest L b⁻¹ y := by
  rw [rationalAdeleVectorPolarGaussianLatticeFourierProduct,
    rationalAdeleVectorPolarGaussianDualTest,
    polarRealGaussianFourierProduct_eq_const_mul]
  ring

/-! ## The nonnegative Weyl-transform test -/

/-- The literal nonnegative modulus of the Weyl transform of the standard test. -/
def weylStandardTestENNReal (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (y : Fin n → RationalAdele) : ℝ≥0∞ :=
  ENNReal.ofReal
    ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) y‖

/-- The nonnegative Weyl-transform test is the constant multiple of the nonnegative
dual-carrier test at the reciprocal width. -/
theorem weylStandardTestENNReal_eq (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (y : Fin n → RationalAdele) :
    L.weylStandardTestENNReal a y =
      ENNReal.ofReal
          ‖(L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n‖ *
        rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹ y := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hinv : ((a : ℂ))⁻¹ = ((a⁻¹ : ℝ) : ℂ) := by push_cast; ring
  unfold weylStandardTestENNReal rationalAdeleVectorPolarGaussianDualTestENNReal
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb,
    rationalAdeleVectorPolarGaussianLatticeFourierProduct_eq_const_mul_dualTest,
    hinv, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]

/-! ## Invariance and pointwise theta finiteness -/

/-- The Weyl-transform test has the same stabilizer invariance as the dual carrier. -/
theorem weylStandardTestENNReal_concreteStabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
    (x : Fin n → RationalAdele) :
    L.weylStandardTestENNReal a (h.1.1.1.1.mulVec x) =
      L.weylStandardTestENNReal a x := by
  rw [L.weylStandardTestENNReal_eq ha, L.weylStandardTestENNReal_eq ha,
    L.rationalAdeleVectorPolarGaussianDualTestENNReal_concreteStabilizer_mulVec]

/-- Pointwise finiteness for the Weyl transform: the domination uses the
dual-carrier comparison. -/
theorem concreteSpecialOrthogonalTheta_weylStandard_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteSpecialOrthogonalTheta (L.weylStandardTestENNReal a) g ≠ ⊤ := by
  have hsum :
      L.concreteSpecialOrthogonalTheta (L.weylStandardTestENNReal a) g =
        ENNReal.ofReal
            ‖(L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ n‖ *
          L.concreteSpecialOrthogonalTheta
            (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹) g := by
    unfold concreteSpecialOrthogonalTheta
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun x ↦ L.weylStandardTestENNReal_eq ha _
  rw [hsum]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (L.concreteSpecialOrthogonalTheta_polarGaussianDual_ne_top hn (inv_pos.2 ha) g)

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The cutoff-normalized functional of the Weyl transform of the standard test is
finite. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv
        (L.weylStandardTestENNReal a)
        RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_ne_top_of_stabilizerInvariant
    hr inst hcutoffProduct hconv
    (fun h x ↦ L.weylStandardTestENNReal_concreteStabilizer_mulVec ha h x)
    (fun g ↦ L.concreteSpecialOrthogonalTheta_weylStandard_ne_top (by omega) ha g)

end PositiveDefiniteIntegralLattice

end
