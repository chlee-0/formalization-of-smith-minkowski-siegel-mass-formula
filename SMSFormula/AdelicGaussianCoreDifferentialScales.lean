import SMSFormula.AdelicGaussianPolarShellDifferentialScales
import SMSFormula.AdelicGaussianCoreShellDensity

/-!
# The idele-free one-shell identity for every nonnegative core test

Core-test version of `ratio_mul_representedNormTheta_mul_differentialScales_eq`: the same proof
with the polar Gaussian test replaced by any nonnegative core member `ψ`.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r s : ℕ}

noncomputable local instance polarShellDiffTargetMeasurableSpaceK
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance polarShellDiffTargetBorelSpaceK
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

set_option maxHeartbeats 3200000 in
/-- The idele-free one-shell identity: the periodization scalars are `h = a · t · b` with the
global idele-class conversion `a` common to both ranks, so it cancels, leaving
`r_a · Θ_a · (t_W · b_W) · τ_V = (t_V · b_V) · τ_W · ofReal(Re d_Φ(a))`
with `t` the differential finite-stabilizer volume and `b` the central-fiber-to-horizontal
scalar (at arbitrary auxiliary blocks `SA`, `SL`). -/
theorem ratio_mul_representedNormTheta_mul_differentialScales_eq_core
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
    (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (ψ : realGaussianCore A b) (hψ : ∀ y, 0 ≤ ψ.val y)
    (hψm : Measurable (fun y ↦ ENNReal.ofReal (ψ.val y))) :
    let hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1 ≠ 0 := by
      rw [x.property]; exact a.property.1
    let V := A.rationalQuadraticSpaceMatrix
    let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
    let tA := A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume ambientCutoffProduct
    let bA := (A.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SA : ℝ≥0∞)
    let tL := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume lowerCutoffProduct
    let bL := (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SL : ℝ≥0∞)
    let τA := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice A (by omega) instA
      hAmbientCutoffProduct hconvA).spinTamagawaNumberENNReal
    let τL := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instL
      hLowerCutoffProduct hconvL).spinTamagawaNumberENNReal
    let aA := algebraMap ℚ RationalAdele (V.nativeRationalQuadraticForm x.1)
    let σ := gaussianFiberMeasure A hn hb aA
    let M := nativeShellMeasureOnValueFiber A P hx
    let U := (fun g ↦ g • x₀) ''
      (K : Set A.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (σ U / M U) *
        A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          hr instA hAmbientCutoffProduct hconvA a
          (fun y ↦ ENNReal.ofReal (ψ.val y)) f * ((tL * bL) * τA) =
      (tA * bA) * τL * ENNReal.ofReal (V.realValueDensity ψ.val aA) := by
  have hone := ratio_mul_representedNormTheta_core_eq A hr hn instA hAmbientCutoffProduct
    hconvA L hs instL hLowerCutoffProduct hconvL a x e hLocal f hf hcutoffMass_ne_zero
    hcutoffMass_ne_top hb x₀ K hc ho ψ hψ hψm
  have hcoef : A.rationalQuadraticSpaceMatrix.representedNormOneShellSpinTamagawaCoefficient
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice A (by omega) instA hAmbientCutoffProduct
        hconvA) hLocal a =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instL hLowerCutoffProduct
          hconvL).spinTamagawaNumberENNReal /
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice A (by omega) instA hAmbientCutoffProduct
          hconvA).spinTamagawaNumberENNReal := by
    rw [RationalQuadraticSpaceMatrix.representedNormOneShellSpinTamagawaCoefficient_eq_witness _ _
      hLocal a ⟨s + 2, L, by omega, x, e,
        cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instL hLowerCutoffProduct
          hconvL⟩]
    rfl
  have hAeq := A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_eq_differentialScales
    (by omega) instA hAmbientCutoffProduct hconvA SA
  have hLeq := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_eq_differentialScales
    (by omega) instL hLowerCutoffProduct hconvL SL
  have hL0 := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero (by omega) instL
    hLowerCutoffProduct hconvL
  have hLt := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_top (by omega) instL
    hLowerCutoffProduct hconvL
  rw [hLeq] at hL0 hLt
  simp only at hone
  dsimp only
  rw [hone, hcoef, hAeq, hLeq, mul_assoc _ (A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume _),
    mul_assoc _ (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume _)]
  rw [mul_assoc _ (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume _)] at hL0 hLt
  have ha0 : (RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr RationalQuadraticSpaceMatrix.rationalIdeleClassHaarToDifferentialWeilScalar_pos.ne'
  refine ENNReal.div_mul_mul_cancel_aux ha0 ENNReal.coe_ne_top
    (right_ne_zero_of_mul hL0)
    (fun h ↦ hLt (by rw [h, ENNReal.mul_top ha0]))
    (RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal_ne_zero _)
    (RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal_ne_top_of_integralLattice
      A (by omega) _)

end PositiveDefiniteIntegralLattice
