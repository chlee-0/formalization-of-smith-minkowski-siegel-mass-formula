import SMSFormula.AdelicGaussianOrbitRatioStabilizerInstance

/-!
# The orbit Riesz ratio from bad-place chart data

The stabilizer identity through carrying sets consumes a package of local chart data at a
bad place: a normed space `E`, a map `S : E → Mat` strictly differentiable at `z` and locally
special-orthogonal, Cayley source points `Y`, `X` with the product relation, a transverse frame `v`
and the two nondegeneracy conditions, and the base condition.  Bundling it as `CarryingChartData`
the cancelled orbit Riesz ratio takes one package per bad place instead of the stabilizer
identity; the gauge is the `‖lastOrbitGaugeRatio‖₊`, positive and finite by the
nonvanishing.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The local chart data of the stabilizer identity through carrying sets, at `p`. -/
structure CarryingChartData (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] where
  E : Type
  [instNormedAddCommGroup : NormedAddCommGroup E]
  [instNormedSpace : NormedSpace ℚ_[p] E]
  S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]
  dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]
  z : E
  hSs : HasStrictFDerivAt S dS z
  hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
    ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])
  Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])
  hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p
  X : skewAdjointMatricesLieSubalgebra
    ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])
  hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p
  hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
    skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X
  v : Fin n → E
  hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
    lastCoordinateVector) (Fin.last n) ≠ 0
  hv : (Pi.basisFun ℚ_[p] (Fin n)).det
    (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0
  hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
    (W.nonisotropicLastExtension a ha).pairingMatrix p
    (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance cdPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance cdPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The stabilizer identity from a chart package. -/
theorem CarryingChartData.stabilizerIdentity (C : W.CarryingChartData a ha p)
    (U : Subgroup ℚ_[p]ˣ)
    (K : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))
    (hKc : IsCompact (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])))
    (hKo : IsOpen (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])))
    (hlift : ∀ g ∈ K, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint
        ℚ_[p], y.similitude ∈ U ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (value : ℚ_[p]) (hvalue : algebraMap ℚ ℚ_[p] a = value) :
    ∀ (point' : ℕ → Fin (n + 1) → ℚ_[p])
      (hpoint' : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p] (point' i) ≠ 0),
      {w | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] w ≠ 0} ⊆
        ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
          ℚ_[p]).padicSquareBranchAtlasRegion p point' hpoint' i →
      ∀ Tb : Set (Fin (n + 1) → ℚ_[p]), MeasurableSet Tb →
        Tb ∩ {z | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
            z = value} =
          Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha
            ℚ_[p]) '' (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
              (W.nonisotropicLastExtension a ha) ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ (K : Set _)))) →
        (W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure p
            (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            W.padicInvariantDifferentialGroupMeasure p
              (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹'
                (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))) *
            ((Measure.addHaar : Measure ℚ_[p]) (closedBall 0 1) *
              ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
                ℚ_[p]).padicSquareBranchAtlasGlue p point' hpoint' (fun _ ↦ Measure.addHaar)
                Measure.addHaar (Padic.unitHaar p (Fin (n + 1))) value (Subtype.val ⁻¹' Tb)) := by
  letI := C.instNormedAddCommGroup
  letI := C.instNormedSpace
  exact W.stabilizerIdentity_centralCutoff_carrying p a ha C.S C.dS C.z C.hSs C.hSO C.Y C.hY C.X C.hX
    C.hproduct C.v C.hs C.hv C.hbase U K hKc hKo hlift value hvalue

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance cdDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cdPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cdPadicMeasurableSpace' (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance cdPadicBorelSpace' (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < n + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

set_option maxHeartbeats 4000000 in
/-- The cancelled orbit Riesz ratio from one chart package per bad place. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_chartData
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
    (hOintB : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, Finset.mem_union_left _ (hSB h)⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (chart : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      P.lowerSpace.CarryingChartData (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx (primesEquiv v.1).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (_h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = (‖P.lowerSpace.lastOrbitGaugeRatio (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let σ := gaussianFiberMeasure L hn hb a
      let Mn := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      σ U / Mn U =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
                  ∏' p : Nat.Primes, L.localResidueDensity M p) *
              (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
            ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              ((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) :=
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_badIntegral L P hx hn hb x₀
    K hc ho M hM S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0
    hc0 hct hOintB
    (fun v ↦ (‖P.lowerSpace.lastOrbitGaugeRatio (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1]‖₊ : ℝ≥0∞))
    (fun v ↦ ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr
      (P.lowerSpace.lastOrbitGaugeRatio_ne_zero (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx _)))
    (fun v ↦ ENNReal.coe_ne_top)
    (fun v point₁ hpoint₁ hcover₁ Tb hTb hTO ↦ by
      have hMx : algebraMap ℚ ℚ_[(primesEquiv v.1).1] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) =
          (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) :=
        (congrArg (algebraMap ℚ ℚ_[(primesEquiv v.1).1]) hM).trans
          (padicIntCast_intCast_eq_algebraMap _ M).symm
      have hs : ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v.1, Finset.mem_union_left _ (hSB v.2)⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1)) =
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (P.blockSpace hx)
            ℚ_[(primesEquiv v.1).1] ⁻¹' (((Uv v) : Set _) ×ˢ ((Kv v) : Set _)) := by
        unfold integralCompletedLocalSubgroups
        rw [dif_pos v.2]
        rfl
      rw [hs] at hTO
      exact (chart v).stabilizerIdentity P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx _ (Uv v) (Kv v) (hKc v) (hK v)
        (hlift v) _ hMx point₁ hpoint₁ hcover₁ Tb hTb hTO)
    hgp

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
