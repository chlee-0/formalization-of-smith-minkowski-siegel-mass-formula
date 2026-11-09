import SMSFormula.AdelicGaussianNativeShellComparison
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicHaarFactor

/-! c_G applied exactly once. The native shell measure is
`M_native = c_G⁻¹ · map(e_X, M_block)` with `c_G` the positive finite horizontal
presentation Haar scalar. Hence the actual Riesz ratio against `M_native` is

`σ(U)/M_native(U) = c_G · σ(U)/N(U)`,  `N = map(e_X, M_block)`,

and on every horizontal integral tail presentation support `S`, `c_G` is the
baseline-weight ratio `w_block(S)/w_V(S)`
(`blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio`):

`σ(U)/M_native(U) = (w_block(S)/w_V(S)) · σ(U)/N(U)`.

So in the analytic density `d_f = (σ(U)/M_native(U)).toReal · ∫_native f`, the
presentation scalar appears once, as the baseline-weight ratio, and is never
confused with a real congruence `.detScalar`. Nothing is chosen. -/
noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open scoped ENNReal

local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

/-- The untransported block pushforward `N = map(e_X, M_block)` on the value fiber. -/
def blockShellMeasureOnValueFiber
    (s : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) : ℝ≥0∞ :=
  (@Measure.map _ _ (borel _) (borel _)
    (P.blockToAmbientShellHomeomorph hx RationalAdele)
    (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) s

theorem nativeShellMeasureOnValueFiber_eq_inv_mul_block
    (s : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) :
    nativeShellMeasureOnValueFiber L P hx s =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹ *
        blockShellMeasureOnValueFiber L P hx s :=
  nativeShellMeasureOnValueFiber_apply_horizontal L P hx s

/-- `c_G` once: `σ(U)/M_native(U) = c_G · σ(U)/N(U)` for every measure `σ` and set `U`. -/
theorem div_nativeShellMeasure_eq_scalar_mul_div_block (σU : ℝ≥0∞)
    (s : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) :
    σU / nativeShellMeasureOnValueFiber L P hx s =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        (σU / blockShellMeasureOnValueFiber L P hx s) := by
  have hc0 : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx).ne'
  have hct : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.coe_ne_top
  rw [nativeShellMeasureOnValueFiber_eq_inv_mul_block, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hct)) (Or.inl (ENNReal.inv_ne_top.mpr hc0)),
    inv_inv]
  ring

/-- On a presentation support, the scalar applied once is the baseline-weight
ratio: `σ(U)/M_native(U) = (w_block(S)/w_V(S)) · σ(U)/N(U)`. -/
theorem div_nativeShellMeasure_eq_weightRatio_mul_div_block (σU : ℝ≥0∞)
    (s : Set (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    σU / nativeShellMeasureOnValueFiber L P hx s =
      P.finiteAdelicPresentationBaselineWeightRatio hx S *
        (σU / blockShellMeasureOnValueFiber L P hx s) := by
  rw [div_nativeShellMeasure_eq_scalar_mul_div_block,
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio hx hS]

section Comparison
variable (hn : 4 < n) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))

include hc ho in
/-- The analytic density with c_G applied once:
`d_f(a) = ((w_block(S)/w_V(S)) · σ(U)/N(U)).toReal · ∫_native f`. -/
theorem realValueDensity_eq_weightRatio_mul_block_ratio_mul_integral (f : realGaussianCore L b)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let σ := gaussianFiberMeasure L hn hb a
    let U := (fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    L.rationalQuadraticSpaceMatrix.realValueDensity f.val a =
      (P.finiteAdelicPresentationBaselineWeightRatio hx S *
          (σ U / blockShellMeasureOnValueFiber L P hx U)).toReal *
        ∫ y : adelicValueFiber L a, f.val y.val ∂(nativeShellMeasureOnValueFiber L P hx) := by
  dsimp only
  rw [realValueDensity_eq_nativeShell_ratio_mul_integral L P hx hn hb x₀ K hc ho f]
  rw [div_nativeShellMeasure_eq_weightRatio_mul_div_block L P hx _ _ hS]

end Comparison
end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
