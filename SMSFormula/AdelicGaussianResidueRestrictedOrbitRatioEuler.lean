import SMSFormula.AdelicGaussianResidueRestrictedOrbitRatioAssembly
import SMSFormula.AdelicGaussianIntegralCarrierEulerProduct

/-!
# The assembled orbit Riesz ratio with the singular series inserted

Substituting the Riesz mass of the integral carrier, `ofReal(Re d_∞(Φ_∞)(a_∞) · ∏'_p δ_p(M))`,
into the assembled Riesz ratio at a central-cutoff orbit gives, in lattice rank at least five,

`σ(U)/M_native(U) = c_G · ((∏ gR/∏ gF) · ofReal(Re d_∞ · ∏'_p δ_p(M))) / N(O)`.

Only `N(O)` and the real local density remain unevaluated.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

local instance orbitEulerDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

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

/-- The assembled orbit Riesz ratio with the singular series. -/
theorem exists_div_nativeShellMeasure_eq_localRatio_eulerProduct
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1))
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
    (hsc : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsCompact (s ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)))
    (hso : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      IsOpen (s ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)))
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
          ((P.blockSpace hx).centralCutoffSubgroup ⊤
            ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) : Set _)) ≠ ⊤) :
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
            ℚ_[(primesEquiv v).1]) '' (s ⟨v, h⟩ : Set _)) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ 0) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p ≠ ⊤) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      let a := algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let σ := gaussianFiberMeasure L hn hb a
      let Mn := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      σ U / Mn U =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (((∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gR p) / ∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p) *
              ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
                  ∏' p : Nat.Primes, L.localResidueDensity M p) /
            P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
                (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
                ((P.blockSpace hx).centralCutoffSubgroup ⊤
                  ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
                    Set _))) := by
  obtain ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc, hr⟩ :=
    exists_div_nativeShellMeasure_eq_localRatio_integralCarrier L P hx hn hb x₀ K hc ho M hM S s
      hodd haunit hden hsc hso hOint h0 htop
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have ha : (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)).2 =
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ) := by
    rw [hM]; rfl
  refine ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc, ?_⟩
  simp only at hr ⊢
  rw [hr, gaussianFiberMeasure_fiberDividedCarrier_one_eq_tprod L (by omega) hb _ hM0 ha]

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
