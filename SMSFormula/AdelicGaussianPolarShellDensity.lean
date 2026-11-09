import SMSFormula.AdelicGaussianNativeShellComparison
import SMSFormula.AdelicGaussianResidueRestrictedUnit
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeNonnegative
import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormNormalizedContribution

/-!
# The polar Gaussian test on one native shell

The rank-one Eisenstein--Siegel functional `E` is unfolded for the polar Gaussian lattice
test `Φ_b = G_b(x_∞) · 1_{Ẑ^n}(x_f)`.  That test is literally a member of the real Gaussian
core: the generator with centre `u = 0`, carrier `c = 1`, period `d = 1` and the full-residue
indicator, which is the integral indicator.  So the actual Riesz identity applies to it on
every supplied represented shell, and in `ℝ≥0∞`, with no division,

`ofReal(Re d_Φ(a)) = (σ(U)/M_native(U)) · ∫⁻ Φ dM_native`,

where `Φ` is the nonnegative (`ℝ≥0∞`) form of the test used by the theta shell expansion.
Since `E`'s nonzero Fourier coefficient is `d_Φ(a)` with weight one, this is the Riesz-side half
of the one-shell comparison.

Composing with the one-shell evaluation of the normalized quotient theta through a supplied
local complement-lattice witness, the represented-norm contribution `Θ_a` satisfies

`(σ(U)/M_native(U)) · Θ_a = (h_amb/h_low) · ofReal(Re d_Φ(a)) · τ_W/τ_V`,

so, when the Riesz ratio is positive finite, the theta shell weight against `d_Φ(a)` is
`(h_amb/h_low)·(τ_W/τ_V)/r_a`, while `E`'s is one. Nothing is chosen: the test, core, presentation,
witness and orbit are constructed earlier or supplied.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open scoped ENNReal

local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- Lintegrals against `map id` across two equal measurable structures are unchanged. -/
theorem lintegral_map_id_spaceEq {X : Type*} {m m' : MeasurableSpace X} (h : m = m')
    (μ : @Measure X m) (g : X → ℝ≥0∞) :
    @lintegral X m' (@Measure.map X X m m' id μ) g = @lintegral X m μ g := by
  cases h
  rw [Measure.map_id]


/-- The polar Gaussian lattice test as a member of the real Gaussian core. -/
def polarGaussianLatticeCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) : realGaussianCore L b :=
  ⟨fun x ↦ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realResidueRestrictedIndicator n 1 Set.univ (rationalAdeleVectorFinitePart n x),
    Submodule.subset_span ⟨0, 1, 1, realResidueRestrictedIndicator n 1 Set.univ, one_ne_zero,
      one_ne_zero,
      by simpa only [coe_realResidueRestrictedIndicator] using
        isStandardCarried_residueRestrictedIndicator (n := n) 1 Set.univ,
      by simpa only [coe_realResidueRestrictedIndicator] using
        isStandardPeriodic_residueRestrictedIndicator (n := n) 1 Set.univ, rfl⟩⟩

/-- The core member is the complex polar Gaussian lattice test. -/
theorem coe_polarGaussianLatticeCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (x : Fin n → RationalAdele) :
    ((polarGaussianLatticeCore L b).val x : ℂ) =
      rationalAdeleVectorPolarGaussianLatticeTest L (b : ℂ) x := by
  change ((realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realResidueRestrictedIndicator n 1 Set.univ (rationalAdeleVectorFinitePart n x) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, coe_realResidueRestrictedIndicator, residueRestrictedIndicator_univ,
    rationalAdeleVectorPolarGaussianLatticeTest]
  congr 1
  simp only [realShiftedGaussian, sub_zero, polarRealGaussian_eq_quadraticShiftedGaussian,
    Complex.ofReal_re]

theorem polarGaussianLatticeCore_nonneg (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (x : Fin n → RationalAdele) : 0 ≤ (polarGaussianLatticeCore L b).val x := by
  change 0 ≤ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realResidueRestrictedIndicator n 1 Set.univ (rationalAdeleVectorFinitePart n x)
  refine mul_nonneg (realShiftedGaussian_pos L b _ _).le ?_
  rcases realResidueRestrictedIndicator_eq_zero_or_one (n := n) 1 Set.univ
    (rationalAdeleVectorFinitePart n x) with h | h <;> rw [h]; exact zero_le_one

/-- The nonnegative form of the test is `ofReal` of the core member. -/
theorem rationalAdeleVectorPolarGaussianLatticeTestENNReal_eq_ofReal (L : PositiveDefiniteIntegralLattice n)
    (b : ℝ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTestENNReal L b x =
      ENNReal.ofReal ((polarGaussianLatticeCore L b).val x) := by
  rw [rationalAdeleVectorPolarGaussianLatticeTestENNReal, ← coe_polarGaussianLatticeCore,
    Complex.norm_real, Real.norm_of_nonneg (polarGaussianLatticeCore_nonneg L b x)]

/-- The real value density of the core member is the real part of the complex density of
the polar Gaussian test. -/
theorem realValueDensity_polarGaussianLatticeCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.realValueDensity (polarGaussianLatticeCore L b).val a =
      (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (b : ℂ)) a).re := by
  change (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
      (fun x ↦ ((polarGaussianLatticeCore L b).val x : ℂ)) a).re = _
  simp_rw [coe_polarGaussianLatticeCore]

variable {m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

/-- The Riesz half of the one-shell comparison for the polar Gaussian test, in `ℝ≥0∞` with
no division: `ofReal(Re d_Φ(a)) = (σ(U)/M_native(U)) · ∫⁻ Φ dM_native`. -/
theorem ofReal_re_complexValueFourierDensity_polarGaussian_eq_ratio_mul_lintegral :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (b : ℂ)) a).re =
      (σ U / M U) * ∫⁻ y : adelicValueFiber L a,
        rationalAdeleVectorPolarGaussianLatticeTestENNReal L b y.val ∂M := by
  intro a σ M U
  have h := realValueDensity_eq_nativeShell_ratio_mul_integral L P hx hn hb x₀ K hc ho
    (polarGaussianLatticeCore L b)
  simp only at h
  rw [← realValueDensity_polarGaussianLatticeCore, h,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (gaussianFiberMeasure_nativeShell_ratio_lt_top L P hx hn hb x₀ K hc ho).ne,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_nativeShellMeasureOnValueFiber_core L P hx (polarGaussianLatticeCore L b))
      (Filter.Eventually.of_forall fun y ↦ polarGaussianLatticeCore_nonneg L b y.val)]
  simp_rw [rationalAdeleVectorPolarGaussianLatticeTestENNReal_eq_ofReal]
  rfl

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance polarShellDensityValueFiberBorelSpace (a : RationalAdele) :
    BorelSpace (adelicValueFiber L a) := by
  unfold adelicValueFiber
  infer_instance

/-- The native lintegral is the ambient-shell lintegral. -/
theorem lintegral_nativeShellMeasureOnValueFiber
    (g : adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) → ℝ≥0∞) :
    ∫⁻ y, g y ∂nativeShellMeasureOnValueFiber L P hx =
      @lintegral _ (borel _) (P.anisotropicRationalAmbientShellMeasure hx) g :=
  lintegral_map_id_spaceEq
    (@BorelSpace.measurable_eq _ _ _
      (polarShellDensityValueFiberBorelSpace L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).symm _ g

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {r s : ℕ}

noncomputable local instance polarShellTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance polarShellTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

set_option maxHeartbeats 1600000 in
/-- The one-shell comparison for the polar Gaussian test: for a represented nonzero norm `a`
with supplied rational vector `x` and local complement-lattice witness `e`, the Riesz ratio times
the normalized represented-norm theta contribution is
`(h_amb/h_low) · ofReal(Re d_Φ(a)) · τ_W/τ_V`. -/
theorem ratio_mul_representedNormTheta_polarGaussian_eq
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r) (hn : 4 < r + 2)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo A ambientCutoffProduct)
    (L : PositiveDefiniteIntegralLattice (s + 2)) [Nonempty (Fin (s + 2))]
    (hs : 1 ≤ s)
    (instL : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {lowerCutoffProduct : ℝ}
    (hLowerCutoffProduct : 0 < lowerCutoffProduct)
    (hconvL : massLocalInverseProductTendsTo L lowerCutoffProduct)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber A.rationalQuadraticSpaceMatrix)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm |>.orthogonalRestriction x.1))
    (hLocal : A.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    {b : ℝ} (hb : 0 < b)
    (x₀ : adelicValueFiber A (algebraMap ℚ RationalAdele
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1)))
    (K : Subgroup A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (ho : IsOpen (K : Set A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) :
    let hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1 ≠ 0 := by
      rw [x.property]; exact a.property.1
    let V := A.rationalQuadraticSpaceMatrix
    let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      A (by omega) instA hAmbientCutoffProduct hconvA
    let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
    let ambientHorizontalScalar :=
      A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instA hAmbientCutoffProduct hconvA
    let lowerHorizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instL hLowerCutoffProduct hconvL
    let aA := algebraMap ℚ RationalAdele (V.nativeRationalQuadraticForm x.1)
    let σ := gaussianFiberMeasure A hn hb aA
    let M := nativeShellMeasureOnValueFiber A P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (σ U / M U) *
        A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          hr instA hAmbientCutoffProduct hconvA a
          (rationalAdeleVectorPolarGaussianLatticeTestENNReal A b) f =
      ((ambientHorizontalScalar : ℝ≥0∞) / (lowerHorizontalScalar : ℝ≥0∞)) *
        ENNReal.ofReal (V.complexValueFourierDensity
          (rationalAdeleVectorPolarGaussianLatticeTest A (b : ℂ)) aA).re *
        V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a := by
  have hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1 ≠ 0 := by
    rw [x.property]; exact a.property.1
  dsimp only
  have htheta :=
    probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_horizontalRatio_mul_shell_mul_coefficient
      A hr instA hAmbientCutoffProduct hconvA L hs instL hLowerCutoffProduct hconvL a x e hLocal
      (rationalAdeleVectorPolarGaussianLatticeTestENNReal A b)
      (measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal A b) f hf
      hcutoffMass_ne_zero hcutoffMass_ne_top
  have hriesz := ofReal_re_complexValueFourierDensity_polarGaussian_eq_ratio_mul_lintegral
    A (integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix x.1 e) hx hn
    hb x₀ K hc ho
  simp only at htheta hriesz
  rw [htheta, hriesz, lintegral_nativeShellMeasureOnValueFiber A
    (integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix x.1 e) hx]
  ring_nf
  conv_rhs => rw [mul_right_comm]
  rfl

end PositiveDefiniteIntegralLattice
