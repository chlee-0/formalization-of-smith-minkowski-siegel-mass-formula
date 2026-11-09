import SMSFormula.AdelicGaussianFiberEulerRatio
import SMSFormula.AdelicGaussianOrbitRatioEulerCancelled

/-!
# The ratio-parametric orbit ratio chain up to the Euler cancellation (rank-free)

The evaluation of the orbit Riesz ratio, from the integral-completed central cutoff
(`exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_orbitMass`) through the local-scale
cancellation, the good-place traces, the bad-place integrality, the chart packages, the identity
chart and lattice-stable cutoffs, to the Euler cancellation against the finite stabilizer volumes
(`exists_div_nativeShellMeasure_mul_prod_eq_eulerCancelled`), uses the Riesz measure only through
the assembled ratio with the singular series.  Each step is restated here verbatim for an arbitrary
fiber Euler ratio `ρ` (`IsFiberEulerRatio`), with the proof, and with no rank bound: the
conclusion `σ(U)/M_native(U) = …` becomes `ρ = …`.  The statements are the instances
`ρ = σ(U)/M_native(U)` (`isFiberEulerRatio_gaussianFiberMeasure`).  Nothing is chosen.
-/

noncomputable section

open scoped Matrix

local instance fercDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

section OrbitMass

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercOrbitMassPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercOrbitMassShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercOrbitMassShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_orbitMass` (any ratio `ρ` with `IsFiberEulerRatio`): the evaluated orbit Riesz ratio at the integral-completed central cutoff. -/
theorem exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_orbitMass_of_ratio
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
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
        (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
        (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
        (z : P.lowerSpace.nonisotropicLastQuadraticShell
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]),
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 ∈
            PadicInt.restrictedIntegralVectors (e (primesEquiv v)) (R (primesEquiv v)) ↔
          z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
            ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
              (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _)) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ 0) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ ⊤) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      let a := algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      ρ =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (((∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gR p) / ∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p) *
              ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
                  ∏' p : Nat.Primes, L.localResidueDensity M p) /
            (((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1 * c v) /
              (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1))) := by
  obtain ⟨hNeq, hN0, hNt⟩ :=
    P.lowerSpace.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_eq_div _ hx hT hneg
      hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct
  have hcs := P.lowerSpace.isCompact_isOpen_integralCompletedLocalSubgroups_padicCentralCutoff _ hx S
    Uv hU hUc Kv hK hKc
  obtain ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc', hr⟩ :=
    exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_of_ratio L P hx M hM hρ S _ hodd
      haunit hden (fun v h ↦ (hcs ⟨v, h⟩).1) (fun v h ↦ (hcs ⟨v, h⟩).2) hOint hN0 hNt
  refine ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc', ?_⟩
  simp only at hr ⊢
  rw [hr, hNeq]

end OrbitMass

section LocalScale

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercLocalScalePrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercLocalScalePadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercLocalScalePadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercLocalScaleShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercLocalScaleShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct` (any ratio `ρ` with `IsFiberEulerRatio`): the orbit Riesz ratio with the local densities cancelled. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_ratio
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
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
        (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (r : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞) (hr0 : ∀ v, r v ≠ 0) (hrt : ∀ v, r v ≠ ⊤)
    (hstab : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}) (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v.1).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasRegion (primesEquiv v.1).1 point₁ hpoint₁ i →
      ∀ Tb : Set (Fin (m + 1) → ℚ_[(primesEquiv v.1).1]), MeasurableSet Tb →
        Tb ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) z = (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1])} = Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v.1, Finset.mem_union_left _ (hSB v.2)⟩ : Set _)) →
        (P.blockSpace hx).padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1])) =
          r v * P.lowerSpace.padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1] ⁻¹'
              (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1]))) *
            ((Measure.addHaar : Measure ℚ_[(primesEquiv v.1).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasGlue (primesEquiv v.1).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v.1).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) (Subtype.val ⁻¹' Tb)))
    (hgood : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)), v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      ∀ w : Fin (n + 1) → ℚ_[(primesEquiv v).1], (((L.pairingMatrix.map (Int.castRingHom ℤ_[(primesEquiv v).1])).map (PadicInt.Coe.ringHom : ℤ_[(primesEquiv v).1] →+* ℚ_[(primesEquiv v).1])).toQuadraticMap') w = (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) →
        (w ∈ ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1)) '' (Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _))) ↔ ‖w‖ ≤ 1)) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = r ⟨v, h⟩ * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      ρ =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
                  ∏' p : Nat.Primes, L.localResidueDensity M p) *
              (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
            ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              ((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) := by
  obtain ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hlocc, hr⟩ :=
    exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_orbitMass_of_ratio L P hx M hM hρ
      S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hOint
  have hBT : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) := hSB.trans Finset.subset_union_left
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have hMx : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) = (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) :=
    fun v ↦ by rw [hM]; exact (padicIntCast_intCast_eq_algebraMap _ M).symm
  have hVAL : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) ≠ 0 :=
    fun v ↦ by rw [PadicInt.coe_intCast]; exact_mod_cast hM0
  have hrep : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)),
      ∃ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _), ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
        PadicInt.subring (primesEquiv v).1 := fun v h ↦
    ⟨_, ⟨1, Subgroup.one_mem _, rfl⟩, hOint v h _ ⟨1, Subgroup.one_mem _, rfl⟩⟩
  have hmemP : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v ∈ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) →
      (primesEquiv v).1 ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) := fun v h ↦ (mem_placeBlockPrimes_iff _ v).mpr h
  have hDex : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, ∃ Dv : ℝ≥0∞,
      gR (primesEquiv v.1).1 * Dv = gF (primesEquiv v.1).1 * c v ∧ Dv ≠ 0 ∧ Dv ≠ ⊤ ∧
      ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v.1).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) (point₁ i) ≠ 0),
        {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasRegion (primesEquiv v.1).1 point₁ hpoint₁ i →
        Dv = r v * ((Measure.addHaar : Measure ℚ_[(primesEquiv v.1).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasGlue (primesEquiv v.1).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v.1).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v.1).1) ⁻¹' Metric.closedBall 0 1))) := fun v ↦
    exists_localScale_of_carry L P hx M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he (hmemP v.1 (hBT v.2))
      (hlocc _ (hmemP v.1 (hBT v.2))) (hVAL v.1) (hMx v.1) (hcar v.1 (hBT v.2))
      (hrep v.1 (hBT v.2)) (hloc v)
      (P.lowerSpace.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_zero _ hx _ (Kv v) (hK v))
      (P.lowerSpace.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_top _ hx _ (hKc v))
      (hr0 v) (hrt v) (hstab v)
  choose Dv hDv using hDex
  let D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞ := fun v ↦
    if h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then Dv ⟨v, h⟩ else 1
  have hDeq : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v = Dv ⟨v, h⟩ :=
    fun v h ↦ dif_pos h
  have hrest : ∀ v ∈ (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) \ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, gR (primesEquiv v).1 = gF (primesEquiv v).1 := by
    intro v hv
    obtain ⟨hvT, hvB⟩ := Finset.mem_sdiff.1 hv
    exact localMass_eq_of_carry_of_integralTrace L P hx M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he (hmemP v hvT)
      (hlocc _ (hmemP v hvT)) (hVAL v) (hMx v) (hcar v hvT) (hrep v hvT) (hgood v hvT hvB)
  refine ⟨e, R, gF, gR, D, he, hlocc, fun v h ↦ ?_, ?_⟩
  · rw [hDeq v h]
    exact ⟨(hDv ⟨v, h⟩).2.1, (hDv ⟨v, h⟩).2.2.1, (hDv ⟨v, h⟩).2.2.2⟩
  · simp only at hr ⊢
    have hW' := P.lowerSpace.realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hW
    have hV' := (P.blockSpace hx).realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top
      (P.lowerSpace.posDef_nonisotropicLastExtension_map_real hW hx ha0)
    exact ENNReal.orbitRatio_eq_of_local_places hBT gF gR c D
      (fun v ↦ (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v)
      (fun v ↦ P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v) hr
      (fun v h ↦ by rw [hDeq v h]; exact (hDv ⟨v, h⟩).1) hrest
      (fun v hv ↦ hgF0 _ (hmemP v hv)) (fun v hv ↦ hgFt _ (hmemP v hv))
      (fun v h ↦ by rw [hDeq v h]; exact (hDv ⟨v, h⟩).2.1)
      (fun v h ↦ by rw [hDeq v h]; exact (hDv ⟨v, h⟩).2.2.1) hc0 hct
      (fun v _ ↦ (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_zero v)
      (fun v _ ↦ (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_top v)
      (fun v _ ↦ P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale_ne_zero v)
      (fun v _ ↦ P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale_ne_top v)
      hV'.1 hV'.2 hW'.1 hW'.2

end LocalScale

section GoodPlaces

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal
open scoped Matrix

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercGoodPlacesPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercGoodPlacesPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercGoodPlacesPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercGoodPlacesShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercGoodPlacesShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces` (any ratio `ρ` with `IsFiberEulerRatio`): the orbit Riesz ratio with the local densities cancelled, with the good-orbit traces
discharged from local good-place conditions on `S \ B`. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_of_ratio
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
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
        (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (r : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞) (hr0 : ∀ v, r v ≠ 0) (hrt : ∀ v, r v ≠ ⊤)
    (hstab : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}) (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v.1).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasRegion (primesEquiv v.1).1 point₁ hpoint₁ i →
      ∀ Tb : Set (Fin (m + 1) → ℚ_[(primesEquiv v.1).1]), MeasurableSet Tb →
        Tb ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) z = (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1])} = Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v.1, Finset.mem_union_left _ (hSB v.2)⟩ : Set _)) →
        (P.blockSpace hx).padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1])) =
          r v * P.lowerSpace.padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1] ⁻¹'
              (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1]))) *
            ((Measure.addHaar : Measure ℚ_[(primesEquiv v.1).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasGlue (primesEquiv v.1).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v.1).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) (Subtype.val ⁻¹' Tb)))
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
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = r ⟨v, h⟩ * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      ρ =
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
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_ratio L P hx M hM hρ S hodd haunit
    hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hOint r hr0 hrt hstab
    (fun v h hvB ↦ by
      have hvS : v ∈ S := by
        rcases Finset.mem_union.1 h with hS | hb
        · exact hS
        · exact (hvB (Finset.mem_union_left _ hb)).elim
      obtain ⟨h1, h2, h3⟩ := hgp v hvS hvB
      exact goodOrbitTrace_of_goodPlace L P hx M hM S Uv Kv v h hvB h1 h2 h3)

end GoodPlaces

section BadIntegral

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology
open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercBadIntegralPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercBadIntegralPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercBadIntegralPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercBadIntegralShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercBadIntegralShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_badIntegral` (any ratio `ρ` with `IsFiberEulerRatio`): the cancelled orbit Riesz ratio with orbit integrality required only at the bad places. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_badIntegral_of_ratio
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
    (hOintB : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, Finset.mem_union_left _ (hSB h)⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (r : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞) (hr0 : ∀ v, r v ≠ 0) (hrt : ∀ v, r v ≠ ⊤)
    (hstab : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}) (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v.1).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasRegion (primesEquiv v.1).1 point₁ hpoint₁ i →
      ∀ Tb : Set (Fin (m + 1) → ℚ_[(primesEquiv v.1).1]), MeasurableSet Tb →
        Tb ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) z = (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1])} = Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v.1, Finset.mem_union_left _ (hSB v.2)⟩ : Set _)) →
        (P.blockSpace hx).padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1])) =
          r v * P.lowerSpace.padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1] ⁻¹'
              (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1]))) *
            ((Measure.addHaar : Measure ℚ_[(primesEquiv v.1).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasGlue (primesEquiv v.1).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v.1).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) (Subtype.val ⁻¹' Tb)))
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
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = r ⟨v, h⟩ * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      ρ =
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
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_of_ratio L P hx M hM hρ
    S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct
    (fun v h z hz i ↦ by
      by_cases hvB : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
      · exact hOintB v hvB z hz i
      · have hvS : v ∈ S := by
          rcases Finset.mem_union.1 h with hS | hb
          · exact hS
          · exact (hvB (Finset.mem_union_left _ hb)).elim
        have hs : ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)) =
            {g | (P.blockSpace hx).PadicCliffordGeneralSpinIsIntegral (primesEquiv v).1 g} := by
          unfold integralCompletedLocalSubgroups
          rw [dif_neg hvB]
          rfl
        rw [hs] at hz
        obtain ⟨g, hg, rfl⟩ := hz
        exact (P.blockToAmbientBaseChangeIsometryEquiv_mem_subring_iff hx (primesEquiv v).1
          (hgp v hvS hvB).2.2 _).mpr
          (fun j ↦ P.lowerSpace.integral_of_padic_nonisotropicLastShellOrbitMap (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx v g hg j) i)
    r hr0 hrt hstab hgp

end BadIntegral

section ChartData

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology
open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercChartDataPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercChartDataPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercChartDataPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercChartDataShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercChartDataShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_chartData` (any ratio `ρ` with `IsFiberEulerRatio`): the cancelled orbit Riesz ratio from one chart package per bad place. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_chartData_of_ratio
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
      ρ =
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
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces_badIntegral_of_ratio L P hx M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0
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

end ChartData

section IdentityChart

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology
open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercIdentityChartPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercIdentityChartPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercIdentityChartPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercIdentityChartShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercIdentityChartShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_identityChart` (any ratio `ρ` with `IsFiberEulerRatio`): the cancelled orbit Riesz ratio with no supplied chart data: the identity chart
`S(c) = Cayley(H(c))` is the chart package at every bad place. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_identityChart_of_ratio
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
    (hOintB : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, Finset.mem_union_left _ (hSB h)⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
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
      ρ =
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
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_chartData_of_ratio L P hx M hM hρ S
    hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hOintB
    (fun v ↦ P.lowerSpace.identityCarryingChartData
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx (primesEquiv v.1).1) hgp

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_latticeStable` (any ratio `ρ` with `IsFiberEulerRatio`): the cancelled orbit Riesz ratio from lattice-stable bad-place cutoffs: no chart data, and the
orbit integrality at the bad places follows from `K_v` preserving `E_v⁻¹ ℤ_p^N` and `x` being
`p`-integral. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_latticeStable_of_ratio
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
      ∀ w : Fin (m + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
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
      ρ =
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
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_identityChart_of_ratio L P hx M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct
    (fun v h z hz ↦ by
      have hs : ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, Finset.mem_union_left _ (hSB h)⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)) =
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (P.blockSpace hx)
            ℚ_[(primesEquiv v).1] ⁻¹' (((Uv ⟨v, h⟩) : Set _) ×ˢ ((Kv ⟨v, h⟩) : Set _)) := by
        unfold integralCompletedLocalSubgroups
        rw [dif_pos h]
        rfl
      rw [hs] at hz
      exact P.integral_of_mem_image_centralCutoffOrbit_of_latticeStable hx (primesEquiv v).1
        (Uv ⟨v, h⟩) (Kv ⟨v, h⟩) (hlift ⟨v, h⟩) (hKlat ⟨v, h⟩) (hxint v h) z hz)
    hgp

end IdentityChart

section EulerCancelled

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology
open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {m : ℕ} (L : PositiveDefiniteIntegralLattice (m + 1)) {x : Fin (m + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance fercEulerCancelledPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance fercEulerCancelledPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance fercEulerCancelledPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance fercEulerCancelledShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance fercEulerCancelledShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

set_option maxHeartbeats 4000000 in
/-- Ratio-parametric form of `exists_div_nativeShellMeasure_mul_prod_eq_eulerCancelled` (any ratio `ρ` with `IsFiberEulerRatio`): the orbit Riesz ratio with its Euler product cancelled against the finite stabilizer volumes. -/
theorem exists_div_nativeShellMeasure_mul_prod_eq_eulerCancelled_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (hm : 3 ≤ m)
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
      ∀ w : Fin (m + 1) → ℚ_[(primesEquiv v.1).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1] w i ∈
          PadicInt.subring (primesEquiv v.1).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v.1).1]
          ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[(primesEquiv v.1).1]) *ᵥ w) i ∈
            PadicInt.subring (primesEquiv v.1).1)
    (hxint : ∀ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, ∀ i,
      algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈ PadicInt.subring (primesEquiv v).1)
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    (LW : PositiveDefiniteIntegralLattice m) (hlow : P.lowerSpace = LW.rationalQuadraticSpaceMatrix)
    {PA PL : ℝ} (hPA0 : 0 < PA) (hA : massLocalInverseProductTendsTo L PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (E : Finset {p : ℕ // Nat.Prime p})
    (hE : ∀ q ∉ E, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (m + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
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
      ρ * ∏ q ∈ E, L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re) *
              (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PA /
                  LW.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PL *
                ENNReal.ofReal (∏ q ∈ E, L.localResidueDensity M q.1) *
                ∏ q ∈ E, LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) *
              (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
            ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              ((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) := by
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_latticeStable_of_ratio L P hx M hM hρ S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct
      hKlat hxint hgp
  refine ⟨e, R, gF, gR, D, h1, h2, h3, ?_⟩
  have hM0 : M ≠ 0 := by
    rintro rfl; exact hx (by rw [hM]; simp)
  have heul := finiteStabilizerVolume_div_mul_prod_eq_prod_mul_tprod_of_three_le L LW P hx hm hlow hPA0
    hA hL M hM E hE
  have hmult : Multipliable (fun q : {p : ℕ // Nat.Prime p} ↦ L.localResidueDensity M q.1) :=
    (L.multipliable_localResidueDensity_of_three_le hm hM0
      (L.isResidueBadBlock_residueBadBlock hM0)).1
  have hΔ0 : 0 ≤ ∏' p : Nat.Primes, L.localResidueDensity M p :=
    ge_of_tendsto (tendsto_prod_rationalPrimesUpTo_tprod hmult)
      (Filter.Eventually.of_forall fun N ↦
        Finset.prod_nonneg fun q _ ↦ localResidueDensity_nonneg L M hM0 q)
  have key : ∀ cG d Δ X Y F : ℝ≥0∞, cG * (d * Δ * X / Y) * F = cG * (d * (F * Δ) * X / Y) := by
    intros; simp only [div_eq_mul_inv]; ring
  have hΔ : ENNReal.ofReal (∏' p : Nat.Primes, L.localResidueDensity M p) =
      ENNReal.ofReal (∏' q : {p : ℕ // Nat.Prime p}, L.localResidueDensity M q.1) := rfl
  simp only at h4 ⊢
  rw [h4, ENNReal.ofReal_mul' hΔ0, hΔ, key, ← heul]

end EulerCancelled

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
