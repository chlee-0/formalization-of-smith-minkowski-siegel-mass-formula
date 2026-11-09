import SMSFormula.AdelicGaussianPresentationVolumeDensity
import SMSFormula.RationalCliffordGeneralSpinHorizontalBaselineLedger
import SMSFormula.AdelicGaussianRationalShellFactorProductFormula

/-!
# The local shell-weight term at a fully good place

In the localized one-shell identity (`exists_representedNormTheta_mul_prod_localDenominator_eq`) the
local terms at a place `v ∉ B` are `num_v = ‖q_a‖_v · s_W(v)` and `den_v = s_B(v) · δ_v(a)`.

At a place off the horizontal and odd-unimodular bad sets of `B = W ⊕ ⟨a⟩` and `W`, off the
exceptional primes and with `p ∤ 2 · D_P · M`, the GSpin good-place ledger
(`lastExtensionValueMultiplier_eq_ledger_of_notMem`: `s_W/s_B = ‖r‖·ν(ℤ_p)·glue_B(X_a(ℤ_p))`) and the
identification `ν(ℤ_p)·glue_B(X_a(ℤ_p)) = δ_p(a)` (block glue = lattice glue at `p ∤ D_P`, lattice glue
= local density at odd `p ∤ M`) give

`s_W(v) = ‖r‖_v · δ_v(a) · s_B(v)`,  hence  `num_v = ‖r · q_a‖_v · den_v`,

with `r` the rational orbit gauge ratio.  So at fully good places the local term is the
`v`-adic norm of the single rational number `r · q_a`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum

local instance gptPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance gptPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance gptDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

variable {m : ℕ} (L : PositiveDefiniteIntegralLattice (m + 1)) {x : Fin (m + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance gptPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- `ν(ℤ_p) · glue_B(X_a(ℤ_p)) = δ_p(a)` at an odd prime off `D_P · M`, in any covering block atlas. -/
theorem addHaar_mul_blockGlue_integral_eq_localResidueDensity
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hpM : ¬ ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ) ∣ M)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (m + 1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    ν (closedBall 0 1) *
        ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasGlue
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint tH ν
          (Padic.unitHaar (Rat.HeightOneSpectrum.primesEquiv v).1 (Fin (m + 1)))
          (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) {y | ‖y.1‖ ≤ 1} =
      ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  set p := (Rat.HeightOneSpectrum.primesEquiv v).1
  haveI : Fact (Nat.Prime p) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hM0 : M ≠ 0 := by
    rintro rfl; exact hx (by rw [hM]; simp)
  set G := (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])
  have hvalue : algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) ≠ 0 :=
    (map_ne_zero _).mpr hx
  have hform : ∃ w, G.toQuadraticMap' w ≠ 0 := by
    refine ⟨P.blockToAmbientPadicContinuousLinearEquiv hx p lastCoordinateVector, ?_⟩
    rw [latticeGram_blockToAmbient L P hx p]
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] lastCoordinateVector =
      algebraMap ℚ ℚ_[p] _ at hsh
    rw [hsh]; exact hvalue
  obtain ⟨point₂, hpoint₂, hcover₂⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover p
    (G.toQuadraticMap') hform
  have hbl := blockGlue_integralPoints_eq_latticeGlue L P hx p hp point hpoint tH hcover point₂
    hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ ν hvalue
  have e1 : ({y | ‖y.1‖ ≤ 1} : Set {w // (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[p] w = algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)}) =
      Subtype.val ⁻¹' closedBall 0 1 := by
    ext w; simp [mem_closedBall, dist_zero_right]
  rw [e1, hbl]
  have key : ∀ value : ℚ_[p], (hv : value ≠ 0) → value = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) →
      ν (closedBall 0 1) * (G.toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂
        (fun _ ↦ Measure.addHaar) ν (Padic.unitHaar p (Fin (m + 1))) value
          (Subtype.val ⁻¹' closedBall 0 1) =
        ENNReal.ofReal (L.localResidueDensity M p) := by
    rintro value hv rfl
    have e2 : (Subtype.val ⁻¹' closedBall 0 1 : Set {w // G.toQuadraticMap' w =
        (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) = {y | ‖y.1‖ ≤ 1} := by
      ext w
      change dist (w : Fin (m + 1) → ℚ_[p]) (0 : Fin (m + 1) → ℚ_[p]) ≤ 1 ↔
        ‖(w : Fin (m + 1) → ℚ_[p])‖ ≤ 1
      rw [dist_zero_right]
    have hdens := latticeGlue_toReal_mul_eq_localResidueDensity L p hp2 hM0 hpM point₂ hpoint₂
      (fun _ ↦ Measure.addHaar) hcover₂ ν
    have hgt := padicSquareBranchAtlasGlue_integral_ne_top G point₂ hpoint₂
      (fun _ ↦ Measure.addHaar) ν (Padic.unitHaar p (Fin (m + 1))) hcover₂ hv
    have hνt : ν (closedBall 0 1) ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
    rw [e2, ← hdens, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hgt,
      ENNReal.ofReal_toReal hνt, mul_comm]
  exact key _ hvalue ((congrArg (algebraMap ℚ ℚ_[p]) hM).trans
    (padicIntCast_intCast_eq_algebraMap p M).symm)

/-- The lower baseline scale at a fully good place: `s_W(v) = ‖r‖_v · δ_v(a) · s_B(v)`. -/
theorem lowerBaselineScale_eq_gauge_mul_localResidueDensity_mul_block (hm : 2 ≤ m)
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvB : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hvOddB : v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ P.lowerSpace.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hgood : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉
      P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hpM : ¬ ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ) ∣ M) :
    P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v =
      Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)
          (Rat.HeightOneSpectrum.primesEquiv v) *
        ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1) *
        (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v := by
  set p := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hvExt : v ∉ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    intro h; apply hvB
    unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
    exact Finset.mem_union_left _ h
  have hvW : v ∉ P.lowerSpace.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    intro h; apply hvB
    unfold RationalQuadraticSpaceMatrix.lastExtensionHorizontalBadPlaces
    exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  have hbform : ∃ w, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] w ≠ 0 := by
    refine ⟨lastCoordinateVector, ?_⟩
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm _ lastCoordinateVector =
      algebraMap ℚ _ _ at hsh
    rw [hsh]; exact (map_ne_zero _).mpr hx
  obtain ⟨point, hpoint, hcover⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover p _ hbform
  have hu := P.lowerSpace.lastExtensionValueMultiplier_eq_ledger_of_notMem
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx hm v hvExt hvW hvOddB hvOddW
    hgood Measure.addHaar point hpoint (fun _ ↦ Measure.addHaar) hcover
  have hg := addHaar_mul_blockGlue_integral_eq_localResidueDensity L P hx M hM v hp hp2 hpM
    Measure.addHaar point hpoint (fun _ ↦ Measure.addHaar) hcover
  rw [mul_assoc, hg, lastOrbitGaugeRatio_scalarExtension] at hu
  unfold lastExtensionValueMultiplier at hu
  have hB0 := (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_zero v
  have hBt := (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_top v
  have hdc : P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v =
      P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v /
        (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v *
        (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v :=
    (ENNReal.div_mul_cancel hB0 hBt).symm
  rw [hdc, hu]
  rfl

/-- The local shell-weight term at a fully good place: `num_v = ‖r · q_a‖_v · den_v`. -/
theorem localNumerator_eq_padicNorm_mul_localDenominator (hm : 2 ≤ m)
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvB : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hvOddB : v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ P.lowerSpace.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hgood : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉
      P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hpM : ¬ ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ) ∣ M) :
    Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx) (Rat.HeightOneSpectrum.primesEquiv v) *
        (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
          else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v) =
      Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ *
            P.rationalShellFactor hx) (Rat.HeightOneSpectrum.primesEquiv v) *
        ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) := by
  rw [if_neg hvB, if_neg hvB, lowerBaselineScale_eq_gauge_mul_localResidueDensity_mul_block L P hx hm
    M hM v hvB hvOddB hvOddW hgood hp hp2 hpM]
  have hmul : ∀ c d : ℚ, Rat.padicNormENNRealAtPrime (c * d) (Rat.HeightOneSpectrum.primesEquiv v) =
      Rat.padicNormENNRealAtPrime c (Rat.HeightOneSpectrum.primesEquiv v) *
        Rat.padicNormENNRealAtPrime d (Rat.HeightOneSpectrum.primesEquiv v) := by
    intro c d
    simp only [Rat.padicNormENNRealAtPrime, map_mul, nnnorm_mul, ENNReal.coe_mul]
  rw [hmul]
  ring

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
