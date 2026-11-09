import SMSFormula.AdelicGaussianResidueRestrictedOrbitRatioEuler

/-!
# The ratio-parametric orbit Riesz ratio (rank-free)

The orbit Riesz-ratio chain (`div_nativeShellMeasure_eq_of_ne` up to
`exists_div_nativeShellMeasure_eq_localRatio_eulerProduct`) evaluates `σ(U)/M_native(U)` for the
Riesz measure `σ = gaussianFiberMeasure`, which exists only in lattice rank at least five.  The
chain uses `σ` only through
* the proportionality `σ = (σ(U)/M_native(U)) · M_native`,
* the local-restriction law `σ(U_R) = (∏ gR/∏ gF) · σ(X_a ∩ {x_f integral})` of carried fiber sets,
* the integral-carrier mass `σ(X_a ∩ {x_f integral}) = ofReal(Re d_∞(a_∞) · ∏'_p δ_p(M))`.

`IsFiberEulerRatio L P hx b M ρ` records the last two laws for the measure `ρ · M_native`; it
mentions no `σ` and no rank bound.  For every such `ρ` the chain gives, verbatim,
`ρ = c_G · ((∏ gR/∏ gF) · ofReal(Re d_∞ · ∏'_p δ_p(M))) / N(O)`
(`exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_of_ratio`).  The ratio is an
instance in rank at least five (`isFiberEulerRatio_gaussianFiberMeasure`).  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

local instance ferT2Infinite : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance ferT2Finite : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance ferT2Adele : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

local instance ferDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

section Predicate

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- A fiber Euler ratio at the lattice value `M = Q(x)`: the measure `ρ · M_native` on the value
fiber obeys the local-restriction law of carried fiber sets and gives the integral carrier the
mass `ofReal(Re d_∞(a_∞) · ∏'_p δ_p(M))`.  No measure, rank bound or normalization is chosen. -/
structure IsFiberEulerRatio (b : ℝ) (M : ℤ) (ρ : ℝ≥0∞) : Prop where
  localRestriction : ∀ (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞),
    (∀ p ∈ Pr, gF p ≠ 0) → (∀ p ∈ Pr, gF p ≠ ⊤) →
    (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
      (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) →
    (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0) →
    haveI : NeZero (localRestrictionLevel Pr e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
    ρ * nativeShellMeasureOnValueFiber L P hx
        (fiberResidueRestrictedSet L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
          (localRestrictionLevel Pr e) (localRestrictionSet Pr e R)) =
      ((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) *
        (ρ * nativeShellMeasureOnValueFiber L P hx
          (fiberDividedCarrier L (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) 1))
  integralCarrier :
    ρ * nativeShellMeasureOnValueFiber L P hx
        (fiberDividedCarrier L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) 1) =
      ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L b (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).re *
        ∏' p : Nat.Primes, L.localResidueDensity M p)

local instance ferShellMeasurableSpace : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance ferShellBorelSpace : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

/-- Every ratio is recovered at a block-shell set: for `O` in the block shell with
`0 < N(O) < ∞`, `ρ = c_G · (ρ · M_native(e_X(O))) / N(O)`. -/
theorem eq_scalar_mul_ratio_mul_nativeShell_blockImage_div (ρ : ℝ≥0∞)
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele))
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ ⊤) :
    ρ = (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
      (ρ * nativeShellMeasureOnValueFiber L P hx
          (P.blockToAmbientShellHomeomorph hx RationalAdele '' O) /
        P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O) := by
  have hc0 : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx).ne'
  have hct : (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.coe_ne_top
  rw [nativeShellMeasureOnValueFiber_eq_inv_mul_block, blockShellMeasureOnValueFiber_image,
    ← mul_assoc ρ, ENNReal.mul_div_cancel_right h0 htop, mul_comm ρ, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hct, one_mul]

variable {b : ℝ}

/-- Ratio-parametric form of `div_nativeShellMeasure_eq_scalar_mul_localRatio_mul_div`: for a
fiber Euler ratio `ρ`, if the presentation image of `O` is the carried fiber set of the CRT product
`R`, then `ρ = c_G · ((∏ gR/∏ gF) · ρ M_native(X_a ∩ {x_f integral})) / N(O)`. -/
theorem div_nativeShellMeasure_eq_scalar_mul_localRatio_mul_div_of_ratio
    (M : ℤ) {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
    (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ Pr, gF p ≠ 0) (hgFt : ∀ p ∈ Pr, gF p ≠ ⊤)
    (hloc : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
      (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0)
    (O : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele))
    (hO : haveI : NeZero (localRestrictionLevel Pr e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
      (P.blockToAmbientShellHomeomorph hx RationalAdele '' O : Set (adelicValueFiber L
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))))
      = fiberResidueRestrictedSet L _ (localRestrictionLevel Pr e) (localRestrictionSet Pr e R))
    (h0 : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ 0)
    (htop : P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O ≠ ⊤) :
    let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
    let Mn := nativeShellMeasureOnValueFiber L P hx
    ρ =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        (((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) * (ρ * Mn (fiberDividedCarrier L a 1)) /
          P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx O) := by
  intro a Mn
  haveI : NeZero (localRestrictionLevel Pr e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
  have h := eq_scalar_mul_ratio_mul_nativeShell_blockImage_div L P hx ρ O h0 htop
  rw [hO, hρ.localRestriction Pr e R hPr gF gR hgF0 hgFt hloc hFne] at h
  exact h

end Predicate

section Assembly

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance ferShellMeasurableSpaceA : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance ferShellBorelSpaceA : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localRatio_integralCarrier` (any ratio `ρ` with `IsFiberEulerRatio`): the assembled Riesz ratio at the central-cutoff orbit. -/
theorem exists_div_nativeShellMeasure_eq_localRatio_integralCarrier_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
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
      let Mn := nativeShellMeasureOnValueFiber L P hx
      ρ =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (((∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gR p) / ∏ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), gF p) *
              (ρ * Mn (fiberDividedCarrier L a 1)) /
            P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
                (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) ''
                ((P.blockSpace hx).centralCutoffSubgroup ⊤
                  ((P.blockSpace hx).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
                    Set _))) := by
  obtain ⟨e, R, he, hcar, hO⟩ := exists_residueData_image_centralCutoffOrbit_eq_of_compactOpen L P hx S s
    hodd haunit hden hsc hso hOint
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have hrep : ∀ p (hp : p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)),
      haveI : Fact p.Prime := ⟨(he p hp).1⟩
      ∃ u : Fin (n + 1) → ℚ_[p], ‖u‖ ≤ 1 ∧
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p]) := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    let z := CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1] 1
    have hz : z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' (s ⟨v, hv⟩ : Set _) := ⟨1, (s ⟨v, hv⟩).one_mem, rfl⟩
    refine ⟨P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1,
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ hOint v hv z hz i, ?_⟩
    rw [← commutativeScalarExtensionQuadraticForm_padic_eq]
    have hshell : L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
        ℚ_[(primesEquiv v).1] (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1) =
          algebraMap ℚ _ (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) :=
      (P.blockToAmbientShellHomeomorph hx ℚ_[(primesEquiv v).1] z).2
    rw [hshell, hM, padicIntCast_intCast_eq_algebraMap]
  obtain ⟨gF, gR, hgF0, hgFt, hloc, hFne⟩ :=
    L.exists_localGlueRatio_family M hM0 (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he hrep
  refine ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc, ?_⟩
  exact div_nativeShellMeasure_eq_scalar_mul_localRatio_mul_div_of_ratio L P hx M hρ
    (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R he gF gR hgF0 hgFt hloc hFne _ hO h0 htop

end Assembly

section Euler

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance ferShellMeasurableSpaceE : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance ferShellBorelSpaceE : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable {b : ℝ}

/-- Ratio-parametric form of `exists_div_nativeShellMeasure_eq_localRatio_eulerProduct` (any ratio `ρ` with `IsFiberEulerRatio`): the assembled orbit Riesz ratio with the singular series. -/
theorem exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_of_ratio
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    {ρ : ℝ≥0∞} (hρ : IsFiberEulerRatio L P hx b M ρ)
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
      ρ =
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
    exists_div_nativeShellMeasure_eq_localRatio_integralCarrier_of_ratio L P hx M hM hρ S s
      hodd haunit hden hsc hso hOint h0 htop
  refine ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hloc, ?_⟩
  simp only at hr ⊢
  rw [hρ.integralCarrier] at hr
  exact hr

end Euler

/-! ## The Riesz ratio is a fiber Euler ratio (rank at least five) -/

section Instance

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- The instance: in lattice rank at least five the raw orbit ratio
`σ(U)/M_native(U)` of the Riesz measure `σ = gaussianFiberMeasure` is a fiber Euler ratio.  The
two laws are the replacement lemma and the integral-carrier Euler product, transported by
the proportionality `σ = (σ(U)/M_native(U)) · M_native`. -/
theorem isFiberEulerRatio_gaussianFiberMeasure (hn : 4 < n + 1) {b : ℝ} (hb : 0 < b)
    (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
    (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ)) :
    IsFiberEulerRatio L P hx b M
      (gaussianFiberMeasure L hn hb (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
        nativeShellMeasureOnValueFiber L P hx
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) := by
  have hσ := gaussianFiberMeasure_eq_smul_nativeShellMeasure L P hx hn hb x₀ K hc ho
  simp only at hσ
  have key : ∀ A, (gaussianFiberMeasure L hn hb (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
        nativeShellMeasureOnValueFiber L P hx
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) *
        nativeShellMeasureOnValueFiber L P hx A =
      gaussianFiberMeasure L hn hb (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) A := fun A ↦ by
    conv_rhs => rw [hσ]
    rfl
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hx (by rw [hM]; simp)
  have ha : (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)).2 =
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ) := by
    rw [hM]; rfl
  refine ⟨fun Pr e R hPr gF gR hgF0 hgFt hloc hFne ↦ ?_, ?_⟩
  · rw [key, key]
    exact gaussianFiberMeasure_fiberResidueRestrictedSet_localRestriction L hn hb _ M ha Pr e R hPr
      gF gR hgF0 hgFt hloc hFne
  · rw [key]
    exact gaussianFiberMeasure_fiberDividedCarrier_one_eq_tprod L (by omega) hb _ hM0 ha

end Instance

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
