import SMSFormula.AdelicGaussianOneShellWeightRational
import SMSFormula.AdelicGaussianCoreOneShellWeight

/-!
# The rational one-shell weight for every nonnegative core test

Core-test version of `exists_representedNormTheta_mul_rationalWeight_eq`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance oswrDecidableEqK : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance oswrPrimeFactK (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance oswrPadicMeasurableSpaceK (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance oswrPadicBorelSpaceK (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance oswrShellMeasurableSpaceK : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance oswrShellBorelSpaceK : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < s + 2 + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

set_option maxHeartbeats 8000000 in
/-- The explicit shell weight with its archimedean factor rational. -/
theorem exists_representedNormTheta_mul_rationalWeight_eq_core
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
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
    (ψ : realGaussianCore L b) (hψ : ∀ y, 0 ≤ ψ.val y)
    (hψm : Measurable (fun y ↦ ENNReal.ofReal (ψ.val y))) :
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
      let σ := gaussianFiberMeasure L hn hb a
      let Mn := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA an (fun y ↦ ENNReal.ofReal (ψ.val y)) f *
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
          ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val a) *
          ∏ q ∈ E, L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_weight_eq_core L P hx hn hb x₀ K hc ho M hM S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL E hE ψ hψ hψm
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

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
