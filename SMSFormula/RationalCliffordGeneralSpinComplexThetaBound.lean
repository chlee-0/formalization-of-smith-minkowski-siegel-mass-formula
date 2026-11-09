import SMSFormula.RationalAdeleWeylTransformThetaFiniteness
import SMSFormula.RationalFiniteAdeleQuadraticGaussDualPeriodicity

/-!
# The complex theta is uniformly bounded on the `GSpin` quotient

The proper-domain bound is a bound on the nonnegative theta of a stabilizer-invariant test.  For
a complex test whose modulus is such a test, the triangle inequality for an absolutely summable
family turns that into a bound on the complex theta itself -- and the bound is the same finite
constant at every point of the group, hence on the whole left quotient.

This is the size half of the integrability the complex layer needs: a bounded function against a
finite measure is integrable once it is measurable.  Measurability of the complex theta is a
separate statement and is not proved here.

Scope: a uniform bound is not integrability, and neither is a Poisson identity, a
Fourier inversion, or any interchange.  Nothing here compares the complex theta of a test with
that of its Weyl transform.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complex theta at a full-adelic `GSpin` point, from the existing complex summand. -/
def fullAdelicCliffordGeneralSpinComplexTheta (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (g : V.FullAdelicCliffordGeneralSpinGroup) : ℂ :=
  ∑' x : Fin n → ℚ,
    V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g x

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The nonnegative modulus test attached to a complex test. -/
def complexTestModulusENNReal (Phi : (Fin n → RationalAdele) → ℂ)
    (y : Fin n → RationalAdele) : ℝ≥0∞ :=
  ENNReal.ofReal ‖Phi y‖

/-- The uniform bound: whenever the modulus of a complex test is stabilizer invariant with
pointwise finite concrete `SO` theta, the complex theta is bounded at every full-adelic `GSpin`
point by the same finite proper-representative sum. -/
theorem ofReal_norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele),
      complexTestModulusENNReal Phi (h.1.1.1.1.mulVec x) = complexTestModulusENNReal Phi x)
    (hfin : ∀ G : L.ConcreteFullAdelicSpecialOrthogonalGroup,
      L.concreteSpecialOrthogonalTheta (complexTestModulusENNReal Phi) G ≠ ⊤)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ENNReal.ofReal
        ‖L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta Phi g‖ ≤
      L.properThetaBound (complexTestModulusENNReal Phi) inst := by
  set M : (Fin n → RationalAdele) → ℝ≥0∞ := complexTestModulusENNReal Phi with hM
  set A : (Fin n → ℚ) → (Fin n → RationalAdele) :=
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction g with hA
  have hbound :
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta M g ≤
        L.properThetaBound M inst := by
    rw [← L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_mk]
    exact L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_le_properThetaBound hinv inst _
  have hne : (∑' x : Fin n → ℚ, ENNReal.ofReal ‖Phi (A x)‖) ≠ ⊤ :=
    (lt_of_le_of_lt hbound
      (lt_top_iff_ne_top.2 (L.properThetaBound_ne_top inst hfin))).ne
  have hsum : Summable (fun x : Fin n → ℚ ↦ ‖Phi (A x)‖) :=
    (ENNReal.summable_toReal hne).congr fun x ↦ ENNReal.toReal_ofReal (norm_nonneg _)
  calc
    ENNReal.ofReal
        ‖L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta Phi g‖ ≤
        ENNReal.ofReal (∑' x : Fin n → ℚ, ‖Phi (A x)‖) :=
      ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsum)
    _ = ∑' x : Fin n → ℚ, ENNReal.ofReal ‖Phi (A x)‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) hsum
    _ ≤ L.properThetaBound M inst := hbound

/-- The real-valued form of the same uniform bound. -/
theorem norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound_toReal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele),
      complexTestModulusENNReal Phi (h.1.1.1.1.mulVec x) = complexTestModulusENNReal Phi x)
    (hfin : ∀ G : L.ConcreteFullAdelicSpecialOrthogonalGroup,
      L.concreteSpecialOrthogonalTheta (complexTestModulusENNReal Phi) G ≠ ⊤)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ‖L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta Phi g‖ ≤
      (L.properThetaBound (complexTestModulusENNReal Phi) inst).toReal := by
  have hle := L.ofReal_norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound
    Phi hinv hfin inst g
  have hbdd := L.properThetaBound_ne_top inst hfin
  have := ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hbdd |>.2 hle
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at this

/-! ## The two instances -/

/-- The dual-carrier complex test is uniformly bounded on the `GSpin` quotient. -/
theorem norm_fullAdelicCliffordGeneralSpinComplexTheta_polarGaussianDual_le
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ‖L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (rationalAdeleVectorPolarGaussianDualTest L (a : ℂ)) g‖ ≤
      (L.properThetaBound (rationalAdeleVectorPolarGaussianDualTestENNReal L a) inst).toReal :=
  L.norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound_toReal
    (rationalAdeleVectorPolarGaussianDualTest L (a : ℂ))
    (fun h x ↦ L.rationalAdeleVectorPolarGaussianDualTestENNReal_concreteStabilizer_mulVec a h x)
    (fun G ↦ L.concreteSpecialOrthogonalTheta_polarGaussianDual_ne_top hn ha G) inst g

/-- The Weyl transform of the standard test is uniformly bounded on the `GSpin` quotient. -/
theorem norm_fullAdelicCliffordGeneralSpinComplexTheta_weylStandard_le
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    ‖L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) g‖ ≤
      (L.properThetaBound (L.weylStandardTestENNReal a) inst).toReal :=
  L.norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound_toReal
    (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))
    (fun h x ↦ L.weylStandardTestENNReal_concreteStabilizer_mulVec ha h x)
    (fun G ↦ L.concreteSpecialOrthogonalTheta_weylStandard_ne_top hn ha G) inst g

/-! ## Measurability of the complex theta -/

/-- The polar dual indicator is the indicator of the existing measurable dual lattice, hence
measurable. -/
theorem measurable_finitePolarDualLatticeIndicator (L : PositiveDefiniteIntegralLattice n) :
    Measurable L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator := by
  have h : L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator =
      Set.indicator L.rationalQuadraticSpaceMatrix.finitePolarDualLattice fun _ ↦ (1 : ℂ) := by
    funext y
    by_cases hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
    · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hy,
        Set.indicator_of_mem hy]
    · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hy,
        Set.indicator_of_notMem hy]
  rw [h]
  exact measurable_const.indicator
    (RationalQuadraticSpaceMatrix.measurableSet_finitePolarDualLattice L)

/-- The complex dual-carrier test is measurable. -/
theorem measurable_rationalAdeleVectorPolarGaussianDualTest
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    Measurable (rationalAdeleVectorPolarGaussianDualTest L b) := by
  let split := rationalAdeleVectorRealFiniteEquiv n
  let f : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ := fun z ↦
    polarRealGaussian L b z.1 *
      L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator z.2
  have hf : Measurable f :=
    ((L.measurable_polarRealGaussian b).comp measurable_fst).mul
      ((L.measurable_finitePolarDualLatticeIndicator).comp measurable_snd)
  simpa [f, split, rationalAdeleVectorPolarGaussianDualTest] using hf.comp split.measurable

/-- The Weyl transform of the standard test is measurable, being a constant multiple of the
dual-carrier test at the reciprocal width. -/
theorem measurable_rationalAdeleRankOneWeylOperator_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) :
    Measurable (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
      (rationalAdeleVectorPolarGaussianLatticeTest L b)) := by
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb]
  have h : rationalAdeleVectorPolarGaussianLatticeFourierProduct L b =
      fun y ↦ ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / b ^ (1 / 2 : ℂ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTest L b⁻¹ y := by
    funext y
    exact L.rationalAdeleVectorPolarGaussianLatticeFourierProduct_eq_const_mul_dualTest b y
  rw [h]
  exact measurable_const.mul (L.measurable_rationalAdeleVectorPolarGaussianDualTest b⁻¹)

/-- A measurable complex test with pointwise absolutely summable theta has a measurable complex
theta on the full-adelic `GSpin` group. -/
theorem measurable_fullAdelicCliffordGeneralSpinComplexTheta
    (V : RationalQuadraticSpaceMatrix n) {Phi : (Fin n → RationalAdele) → ℂ}
    (hmeas : Measurable Phi)
    (hsum : ∀ g : V.FullAdelicCliffordGeneralSpinGroup,
      Summable (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g)) :
    Measurable (V.fullAdelicCliffordGeneralSpinComplexTheta Phi) := by
  apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Fin n → ℚ)))
    (f := fun s g ↦ ∑ x ∈ s,
      V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g x)
  · intro s
    refine Finset.measurable_sum _ fun x _ ↦ ?_
    exact hmeas.comp (V.continuous_fullAdelicCliffordGeneralSpinRationalVectorAction x).measurable
  · rw [tendsto_pi_nhds]
    intro g
    exact (hsum g).hasSum

end PositiveDefiniteIntegralLattice

end
