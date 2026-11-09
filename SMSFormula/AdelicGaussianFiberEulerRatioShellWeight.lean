import SMSFormula.AdelicGaussianFiberEulerRatioChain
import SMSFormula.AdelicGaussianCoreOneShellWeightCapstone

/-!
# The shell weight for every fiber Euler ratio (rank-free)

The core shell identity `representedNormTheta_mul_spinTamagawa_eq_core`
(`Θ_a(ψ) · τ(Spin_V) = τ(Spin_{W_a}) · ofReal(d_ψ(a))`, lattice rank at least five) uses the Riesz
measure `σ` in exactly two places: the Riesz half `ofReal(d_ψ(a)) = r · ∫⁻ ψ dM_native` of the
one-shell comparison, and the Euler evaluation of the same ratio `r = σ(U)/M_native(U)`.

Here both are replaced by an arbitrary fiber Euler ratio `ρ` (`IsFiberEulerRatio`): the Riesz
half becomes the identity `ρ · ∫⁻ φ dM_native = ρ · ∫⁻ φ dM_native`, for every measurable
`φ ≥ 0`, and the Euler evaluation is the ratio-parametric chain.  The conclusion is

`Θ_a(φ) · τ(Spin_V) = τ(Spin_{W_a}) · (ρ · ∫⁻_{X_a} φ dM_native)`
(`representedNormTheta_mul_spinTamagawa_eq_core_of_ratio`),

with no rank bound beyond the structural ones (`s ≥ 1`, i.e. lattice rank at least four), no
Riesz measure and no Fourier density.  The identity is the instance `ρ = σ(U)/M_native(U)`,
`φ = ofReal ∘ ψ`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

local instance fertDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice

open PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase RationalQuadraticSpaceMatrix

variable {r s : ℕ}

noncomputable local instance fertShellTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance fertShellTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

set_option maxHeartbeats 1600000 in
/-- Ratio-parametric form of `ratio_mul_representedNormTheta_core_eq`: for every ratio `ρ` and
every measurable `φ ≥ 0`,
`ρ · Θ_a(φ) = (h_amb/h_low) · (ρ · ∫⁻_{X_a} φ dM_native) · τ_W/τ_V`.  No Riesz identity is used. -/
theorem ratio_mul_representedNormTheta_eq_of_ratio
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
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
    (ρ : ℝ≥0∞) (φ : (Fin (r + 2) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
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
    let M := nativeShellMeasureOnValueFiber A P hx
    ρ * A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          hr instA hAmbientCutoffProduct hconvA a φ f =
      ((ambientHorizontalScalar : ℝ≥0∞) / (lowerHorizontalScalar : ℝ≥0∞)) *
        (ρ * ∫⁻ y, φ y.val ∂M) *
        V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a := by
  have hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x.1 ≠ 0 := by
    rw [x.property]; exact a.property.1
  dsimp only
  have htheta :=
    probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_horizontalRatio_mul_shell_mul_coefficient
      A hr instA hAmbientCutoffProduct hconvA L hs instL hLowerCutoffProduct hconvL a x e hLocal
      φ hφm f hf hcutoffMass_ne_zero hcutoffMass_ne_top
  simp only at htheta
  have hS : ∫⁻ y, φ y.val ∂nativeShellMeasureOnValueFiber A
        (integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix x.1 e) hx =
      ∫⁻ y, φ y.1 ∂(integralLatticeAnisotropicComplementPresentation L A.rationalQuadraticSpaceMatrix
        x.1 e).anisotropicRationalAmbientShellMeasure hx := by
    rw [lintegral_nativeShellMeasureOnValueFiber]
    rfl
  rw [htheta, hS]
  ring

set_option maxHeartbeats 3200000 in
/-- Ratio-parametric form of `ratio_mul_representedNormTheta_mul_differentialScales_eq_core`:
`ρ · Θ_a(φ) · (t_W · b_W) · τ_V = (t_V · b_V) · τ_W · (ρ · ∫⁻_{X_a} φ dM_native)`. -/
theorem ratio_mul_representedNormTheta_mul_differentialScales_eq_of_ratio
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
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
    (ρ : ℝ≥0∞) (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (φ : (Fin (r + 2) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
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
    let M := nativeShellMeasureOnValueFiber A P hx
    ρ * A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          hr instA hAmbientCutoffProduct hconvA a φ f * ((tL * bL) * τA) =
      (tA * bA) * τL * (ρ * ∫⁻ y, φ y.val ∂M) := by
  have hone := ratio_mul_representedNormTheta_eq_of_ratio A hr instA hAmbientCutoffProduct
    hconvA L hs instL hLowerCutoffProduct hconvL a x e hLocal f hf hcutoffMass_ne_zero
    hcutoffMass_ne_top ρ φ hφm
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

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

section Weight

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fertWeightPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fertWeightPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fertWeightPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fertWeightShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fertWeightShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 8000000 in
/-- Ratio-parametric form of `exists_representedNormTheta_mul_weight_eq_core` (any ratio `ρ` with `IsFiberEulerRatio`): the explicit theta shell weight of one represented shell. -/
theorem exists_representedNormTheta_mul_weight_eq_core_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (hSB : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ S)
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ Uv v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hKlat : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∀ w : Fin ((s + 2) + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin ((s + 2) + 1)) (Fin ((s + 2) + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (LW : PositiveDefiniteIntegralLattice (s + 2)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
    (an : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hxa : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = an.1)
    (eIso : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm |>.orthogonalRestriction x))
    (hP : P = integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x eIso)
    (hLocal : L.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {PA PL : ℝ} (hPA0 : 0 < PA) (hPL0 : 0 < PL) (hA : massLocalInverseProductTendsTo L PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (E : Finset {p : ℕ // Nat.Prime p})
    (hE : ∀ q ∉ E, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ))
    (φ : (Fin (s + 2 + 1) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin ((s + 2) + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (_h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin ((s + 2) + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = (‖P.lowerSpace.lastOrbitGaugeRatio (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin ((s + 2) + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let Mn := nativeShellMeasureOnValueFiber L P hx
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA an φ f *
        ((LW.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SL : ℝ≥0∞) *
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal *
          (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re) *
          ENNReal.ofReal (∏ q ∈ E, L.localResidueDensity M q.1) *
          (∏ q ∈ E, LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) *
          (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
          ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              ((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) =
        (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SA : ℝ≥0∞) *
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
          (ρ * ∫⁻ y, φ y.val ∂Mn) *
          ∏ q ∈ E, L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  subst hP
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_div_nativeShellMeasure_mul_prod_eq_eulerCancelled_of_ratio L _ hx M hM hρ (by omega) S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct
      hKlat hxint hgp LW rfl hPA0 hA hL E hE
  refine ⟨e, R, gF, gR, D, h1, h2, h3, ?_⟩
  have hθ := ratio_mul_representedNormTheta_mul_differentialScales_eq_of_ratio L (by omega) instA hPA0
    hA LW hs instL hPL0 hL an ⟨x, hxa⟩ eIso hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top ρ SA SL
    φ hφm
  simp only at h4 hθ ⊢
  refine ENNReal.thetaShellWeight_eq_of_riesz ?_ h4
    (ENNReal.inv_ne_zero.mpr (LW.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top PL))
    (ENNReal.inv_ne_top.mpr (LW.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero hPL0))
    (ENNReal.inv_ne_zero.mpr (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top PA))
    (ENNReal.inv_ne_top.mpr (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero hPA0))
  exact (mul_assoc _ _ _).trans hθ

end Weight

section RationalWeight

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fertRationalWeightPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fertRationalWeightPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fertRationalWeightPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fertRationalWeightShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fertRationalWeightShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ} (hb : 0 < b)
include hb

set_option maxHeartbeats 8000000 in
/-- Ratio-parametric form of `exists_representedNormTheta_mul_rationalWeight_eq_core` (any ratio `ρ` with `IsFiberEulerRatio`): the explicit shell weight with its archimedean factor rational. -/
theorem exists_representedNormTheta_mul_rationalWeight_eq_core_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (hSB : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ S)
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ Uv v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hKlat : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∀ w : Fin ((s + 2) + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin ((s + 2) + 1)) (Fin ((s + 2) + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (LW : PositiveDefiniteIntegralLattice (s + 2)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
    (an : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hxa : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = an.1)
    (eIso : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm |>.orthogonalRestriction x))
    (hP : P = integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x eIso)
    (hLocal : L.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {PA PL : ℝ} (hPA0 : 0 < PA) (hPL0 : 0 < PL) (hA : massLocalInverseProductTendsTo L PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (E : Finset {p : ℕ // Nat.Prime p})
    (hE : ∀ q ∉ E, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ))
    (Sp : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hSp : P.IsHorizontalIntegralTailPresentationSupport hx Sp)
    (φ : (Fin (s + 2 + 1) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin ((s + 2) + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (_h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin ((s + 2) + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = (‖P.lowerSpace.lastOrbitGaugeRatio (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin ((s + 2) + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let Mn := nativeShellMeasureOnValueFiber L P hx
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA an φ f *
        ((LW.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SL : ℝ≥0∞) *
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal *
          P.finiteAdelicPresentationBaselineWeightRatio hx Sp *
          ENNReal.ofReal (∏ q ∈ E, L.localResidueDensity M q.1) *
          (∏ q ∈ E, LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) *
          ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              P.lowerSpace.pairingMatrix P.lowerSpace.form_symm P.lowerSpace.form_det_ne_zero : ℝ)| /
            (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
              (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
              |(((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)| *
              ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ))) *
                (∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
          ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              (∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) =
        (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar SA : ℝ≥0∞) *
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
          (ρ * ∫⁻ y, φ y.val ∂Mn) *
          ∏ q ∈ E, L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_weight_eq_core_of_ratio L P hx M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL E hE φ hφm
  refine ⟨e, R, gF, gR, D, h1, h2, h3, ?_⟩
  simp only at h4 ⊢
  have harch := ofReal_re_realLocalValueDensity_mul_realMass_eq_presentation L hb (by omega) P hx
    hW ha0
  have hBpos := (P.blockSpace hx).realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top
    (P.lowerSpace.posDef_nonisotropicLastExtension_map_real hW hx ha0)
  have hCpos : 0 < |(Matrix.skewAdjointFixedFormElementaryDetScalar
              (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
              (P.blockSpace hx).form_det_ne_zero : ℝ)| * 2 *
          |(((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ)| *
          ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ) := by
    have hE : (P.blockToAmbientRationalMatrix hx).det ≠ 0 := by
      have h := congrArg Matrix.det
        (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact left_ne_zero_of_mul_eq_one h
    have hdF : (0 : ℝ) < ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ) := by
      have h := L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
      rw [realPolarMatrix_det, polarMatrix, Matrix.det_smul, Fintype.card_fin, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_ofNat] at h
      exact pos_of_mul_pos_right h (by positivity)
    have heB := Rat.cast_ne_zero (α := ℝ) |>.mpr
      (Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero (P.blockSpace hx).pairingMatrix
        (P.blockSpace hx).form_symm (P.blockSpace hx).form_det_ne_zero)
    have hE' : (((P.blockToAmbientRationalMatrix hx).det : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hE
    have := abs_pos.mpr heB
    have := abs_pos.mpr hE'
    positivity
  rw [ENNReal.shellWeight_archimedean_replace harch hBpos.1 hBpos.2
    (ENNReal.ofReal_pos.mpr hCpos).ne' ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_div_of_pos hCpos,
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio hx hSp] at h4
  exact h4

end RationalWeight

section LocalDenominator

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fertLocalDenominatorPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fertLocalDenominatorPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fertLocalDenominatorPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fertLocalDenominatorShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fertLocalDenominatorShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ} (hb : 0 < b)
include hb

set_option maxHeartbeats 8000000 in
/-- Ratio-parametric form of `exists_representedNormTheta_mul_prod_localDenominator_eq_core` (any ratio `ρ` with `IsFiberEulerRatio`): the one-shell identity as a product of local terms. -/
theorem exists_representedNormTheta_mul_prod_localDenominator_eq_core_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (hSB : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ S)
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ Uv v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hKlat : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∀ w : Fin ((s + 2) + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin ((s + 2) + 1)) (Fin ((s + 2) + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (LW : PositiveDefiniteIntegralLattice (s + 2)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
    (an : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hxa : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = an.1)
    (eIso : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm |>.orthogonalRestriction x))
    (hP : P = integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x eIso)
    (hLocal : L.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {PA PL : ℝ} (hPA0 : 0 < PA) (hPL0 : 0 < PL) (hA : massLocalInverseProductTendsTo L PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hE : ∀ q ∉ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ))
    (Sp : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hSp : P.IsHorizontalIntegralTailPresentationSupport hx Sp) (hST : Sp ⊆ T)
    (h2T : RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈ T)
    (hOddA : L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ T)
    (hOddW : LW.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ T)
    (hBT : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ T)
    (hqT : Rat.padicNormPrimeSupport (P.rationalShellFactor hx) ⊆ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)
    (φ : (Fin (s + 2 + 1) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin ((s + 2) + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (_h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin ((s + 2) + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = (‖P.lowerSpace.lastOrbitGaugeRatio (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin ((s + 2) + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let Mn := nativeShellMeasureOnValueFiber L P hx
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA an φ f *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal *
        ∏ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
            else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        (ρ * ∫⁻ y, φ y.val ∂Mn) *
        ∏ v ∈ T, (Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx)
            (Rat.HeightOneSpectrum.primesEquiv v) *
          (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
            else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v)) := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  have hTsupp : P.IsHorizontalIntegralTailPresentationSupport hx T :=
    RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation.IsHorizontalIntegralTailPresentationSupport.mono
      P hx hSp hST
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_rationalWeight_eq_core_of_ratio L P hx hb M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL (T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding) hE T hTsupp φ hφm
  refine ⟨e, R, gF, gR, D, h1, h2, h3, ?_⟩
  simp only at h4 ⊢
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have hdF : (0 : ℝ) < ((L.rationalQuadraticSpaceMatrix.pairingMatrix.det : ℚ) : ℝ) := by
    have h := L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
    rw [realPolarMatrix_det, polarMatrix, Matrix.det_smul, Fintype.card_fin, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_ofNat] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hlow : P.lowerSpace = LW.rationalQuadraticSpaceMatrix := by subst hP; rfl
  have hGA : L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ T :=
    hSp.2.1.trans hST
  have hGW : LW.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ T := by
    intro v hv
    apply hBT
    unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
    rw [hlow]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hβW : ∀ v, LW.rationalQuadraticSpaceMatrix.centralFiberLocalTerm v =
      (LW.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ *
        (P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v *
          (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞))⁻¹ := by
    intro v; rw [hlow]; rfl
  rw [coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_eq_prod_of_subset L SA hGA h2T
      hOddA,
    coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_eq_prod_of_subset LW SL hGW h2T
      hOddW,
    RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation.finiteAdelicPresentationBaselineWeightRatio,
    (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale,
    L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale,
    P.ofReal_archimedeanShellFactor_eq_inv_prod hx hdF hqT,
    ENNReal.ofReal_prod_of_nonneg (fun q _ ↦ localResidueDensity_nonneg L M hM0 q)] at h4
  have hemb : ∀ f : {p : ℕ // Nat.Prime p} → ℝ≥0∞,
      ∏ q ∈ (T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding : Finset {p : ℕ // Nat.Prime p}), f q =
        ∏ v ∈ T, f (Rat.HeightOneSpectrum.primesEquiv v) := fun f ↦ by
    rw [Finset.prod_map]; rfl
  simp only [hemb,
    ← RationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_eq_latticeAtPrime,
    Finset.prod_coe_sort, hβW] at h4
  simp only [RationalQuadraticSpaceMatrix.centralFiberLocalTerm] at h4
  refine ENNReal.shellWeight_localize hBT (fun v _ ↦ ⟨
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v,
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v⟩)
    (fun v _ ↦ ⟨
      LW.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v,
      LW.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v⟩)
    (fun v _ ↦ ⟨L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalBaselineScale_ne_zero v,
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalBaselineScale_ne_top v⟩)
    (fun v _ ↦ ⟨(P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_zero v,
      (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_top v⟩)
    (fun v _ ↦ ⟨P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale_ne_zero v,
      P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale_ne_top v⟩)
    (fun v _ ↦ ⟨ENNReal.coe_ne_zero.mpr (rationalPadicMathlibHaarToDifferentialScalar_ne_zero v),
      ENNReal.coe_ne_top⟩)
    (fun v _ ↦ ⟨?_, ?_⟩) (fun v _ ↦ ENNReal.ofReal_ne_top)
    (fun v hv ↦ ⟨(h3 v hv).1, (h3 v hv).2.1⟩) h4
  · haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
    simp only [Rat.padicNormENNRealAtPrime, ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero,
      map_eq_zero]
    exact P.rationalShellFactor_ne_zero hx
  · simp only [Rat.padicNormENNRealAtPrime]
    exact ENNReal.coe_ne_top

end LocalDenominator

section Capstone

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fertCapstonePrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fertCapstonePadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fertCapstonePadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fertCapstoneShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fertCapstoneShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ} (hb : 0 < b)
include hb

set_option maxHeartbeats 8000000 in
/-- Ratio-parametric form of `representedNormTheta_mul_spinTamagawa_eq_core` (any ratio `ρ` with `IsFiberEulerRatio`): the shell weight of one represented shell: `Θ_a · τ(Spin_V) = τ(Spin_{W_a}) · d_Φ(a)`. -/
theorem representedNormTheta_mul_spinTamagawa_eq_core_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (hSB : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ S)
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ Uv v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hKlat : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∀ w : Fin ((s + 2) + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin ((s + 2) + 1)) (Fin ((s + 2) + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (LW : PositiveDefiniteIntegralLattice (s + 2)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
    (an : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hxa : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = an.1)
    (eIso : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm |>.orthogonalRestriction x))
    (hP : P = integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x eIso)
    (hLocal : L.rationalQuadraticSpaceMatrix.OneShellSpinCoefficientLocallyNonempty)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (SA SL : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {PA PL : ℝ} (hPA0 : 0 < PA) (hPL0 : 0 < PL) (hA : massLocalInverseProductTendsTo L PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hE : ∀ q ∉ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ))
    (Sp : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hSp : P.IsHorizontalIntegralTailPresentationSupport hx Sp) (hST : Sp ⊆ T)
    (h2T : RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈ T)
    (hOddA : L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ T)
    (hOddW : LW.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ T)
    (hBT : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ T)
    (hqT : Rat.padicNormPrimeSupport (P.rationalShellFactor hx) ⊆ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)
    (φ : (Fin (s + 2 + 1) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
        (by omega : 1 ≤ s + 1) instA hPA0 hA an φ f *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
      (ρ * ∫⁻ y, φ y.val ∂nativeShellMeasureOnValueFiber L P hx) := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_prod_localDenominator_eq_core_of_ratio L P hx hb M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL T hE Sp hSp hST h2T hOddA hOddW hBT hqT φ hφm
  simp only at h4
  have hunit : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 →
      ‖algebraMap ℚ ℚ_[(primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)‖ = 1 := by
    intro v hu
    obtain ⟨hu1, hu2⟩ := (mem_padicIntegralUnitsSubgroup_iff _ _).mp hu
    have hval : ((finiteAdelicUnitHeightOneComponentHom v
        (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
          (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) :
          ℚ_[(primesEquiv v).1]ˣ) : ℚ_[(primesEquiv v).1]) =
        algebraMap ℚ ℚ_[(primesEquiv v).1] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) :=
      (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes _
    have hle : ‖algebraMap ℚ ℚ_[(primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)‖ ≤ 1 := by
      rw [← hval]; exact hu1
    have hle' : ‖(algebraMap ℚ ℚ_[(primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))⁻¹‖ ≤ 1 := by
      rw [← hval, ← Units.val_inv_eq_inv_val]; exact hu2
    have hne : algebraMap ℚ ℚ_[(primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) ≠ 0 := (map_ne_zero _).mpr hx
    rw [norm_inv] at hle'
    have hpos := norm_pos_iff.mpr hne
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have : 1 < (‖algebraMap ℚ ℚ_[(primesEquiv v).1]
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)‖)⁻¹ := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  refine theta_mul_eq_of_localized L P hx (by omega) M hM D (T := T) (fun v _ hvB ↦ ?_) h3 h4
  have hvbadB : v ∉ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    intro h; apply hvB
    unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
    exact Finset.mem_union_left _ h
  have hgoodB : v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx := by
    by_cases hvS : v ∈ S
    · exact hgp v hvS hvB
    · have hvSB : v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces := by
        rw [Finset.mem_union, not_or]; exact ⟨hvS, hvbadB⟩
      exact ⟨fun h ↦ hvSB (hodd h), haunit v hvSB, hden v hvSB⟩
  obtain ⟨hvOddB, hvu, hvD⟩ := hgoodB
  have hau := hunit v hvu
  obtain ⟨hvOddW, hvExc, hv2⟩ := goodConditions_of_not_mem_oddUnimodular_block P.lowerSpace
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx v hvOddB hau
  have hvM : ¬ (((primesEquiv v).1 : ℕ) : ℤ) ∣ M := by
    intro hd
    have hau' := hau
    rw [hM] at hau'
    have := (not_dvd_num_den_of_norm_eq_one hau').1
    rw [Rat.num_intCast] at this
    exact this (Int.natCast_dvd.mp hd)
  exact ⟨hvOddB, hvOddW, hvExc, hvD, hv2, hvM⟩

end Capstone

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
