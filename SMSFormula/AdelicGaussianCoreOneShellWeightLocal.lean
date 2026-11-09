import SMSFormula.AdelicGaussianOneShellWeightLocal
import SMSFormula.AdelicGaussianCoreOneShellWeightRational

/-!
# The localized one-shell identity for every nonnegative core test

Core-test version of `exists_representedNormTheta_mul_prod_localDenominator_eq`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance oswlDecidableEqK : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance oswlPrimeFactK (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance oswlPadicMeasurableSpaceK (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance oswlPadicBorelSpaceK (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance oswlShellMeasurableSpaceK : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance oswlShellBorelSpaceK : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < s + 2 + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

set_option maxHeartbeats 8000000 in
/-- The one-shell identity as a product of local terms. -/
theorem exists_representedNormTheta_mul_prod_localDenominator_eq_core
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
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal *
        ∏ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
            else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val a) *
        ∏ v ∈ T, (Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx)
            (Rat.HeightOneSpectrum.primesEquiv v) *
          (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
            else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v)) := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  have hTsupp : P.IsHorizontalIntegralTailPresentationSupport hx T :=
    RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation.IsHorizontalIntegralTailPresentationSupport.mono
      P hx hSp hST
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_rationalWeight_eq_core L P hx hn hb x₀ K hc ho M hM S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL (T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding) hE T hTsupp ψ hψ hψm
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

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
