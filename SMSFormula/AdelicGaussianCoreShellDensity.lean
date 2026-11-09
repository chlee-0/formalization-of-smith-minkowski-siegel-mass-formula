import SMSFormula.AdelicGaussianPolarShellDensity

/-!
# The one-shell comparison for every nonnegative core test

The one-shell comparison (`ratio_mul_representedNormTheta_polarGaussian_eq`) used only two facts
about the polar Gaussian lattice test: its theta shell evaluation holds for every measurable test,
and its value density obeys the Riesz identity because it is a core member.  Both hold for every
nonnegative member `ψ` of the real Gaussian core, so for such `ψ`

`(σ(U)/M_native(U)) · Θ_a(ψ) = (h_amb/h_low) · ofReal(d_ψ(a)) · τ_W/τ_V`.

In particular this applies to the dual-carrier test.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

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
theorem ofReal_realValueDensity_core_eq_ratio_mul_lintegral (ψ : realGaussianCore L b)
    (hψ : ∀ y, 0 ≤ ψ.val y) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let M := nativeShellMeasureOnValueFiber L P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val a) =
      (σ U / M U) * ∫⁻ y : adelicValueFiber L a, ENNReal.ofReal (ψ.val y.val) ∂M := by
  intro a σ M U
  have h := realValueDensity_eq_nativeShell_ratio_mul_integral L P hx hn hb x₀ K hc ho ψ
  simp only at h
  rw [h, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (gaussianFiberMeasure_nativeShell_ratio_lt_top L P hx hn hb x₀ K hc ho).ne,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_nativeShellMeasureOnValueFiber_core L P hx ψ)
      (Filter.Eventually.of_forall fun y ↦ hψ y.val)]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {r s : ℕ}

noncomputable local instance coreShellTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance coreShellTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

set_option maxHeartbeats 1600000 in
/-- The one-shell comparison for every nonnegative core test: for a represented nonzero norm `a`
with supplied rational vector `x` and local complement-lattice witness `e`, the Riesz ratio times
the normalized represented-norm theta contribution is
`(h_amb/h_low) · ofReal(Re d_Φ(a)) · τ_W/τ_V`. -/
theorem ratio_mul_representedNormTheta_core_eq
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
    (ho : IsOpen (K : Set A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (ψ : realGaussianCore A b) (hψ : ∀ y, 0 ≤ ψ.val y)
    (hψm : Measurable (fun y ↦ ENNReal.ofReal (ψ.val y))) :
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
          (fun y ↦ ENNReal.ofReal (ψ.val y)) f =
      ((ambientHorizontalScalar : ℝ≥0∞) / (lowerHorizontalScalar : ℝ≥0∞)) *
        ENNReal.ofReal (V.realValueDensity ψ.val aA) *
        V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a := by
  have hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1 ≠ 0 := by
    rw [x.property]; exact a.property.1
  dsimp only
  have htheta :=
    probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_horizontalRatio_mul_shell_mul_coefficient
      A hr instA hAmbientCutoffProduct hconvA L hs instL hLowerCutoffProduct hconvL a x e hLocal
      (fun y ↦ ENNReal.ofReal (ψ.val y)) hψm f hf
      hcutoffMass_ne_zero hcutoffMass_ne_top
  have hriesz := ofReal_realValueDensity_core_eq_ratio_mul_lintegral
    A (integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix x.1 e) hx hn
    hb x₀ K hc ho ψ hψ
  simp only at htheta hriesz
  rw [htheta, hriesz, lintegral_nativeShellMeasureOnValueFiber A
    (integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix x.1 e) hx]
  ring_nf
  conv_rhs => rw [mul_right_comm]
  rfl

end PositiveDefiniteIntegralLattice
