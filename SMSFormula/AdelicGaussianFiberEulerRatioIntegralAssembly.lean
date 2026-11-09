import SMSFormula.AdelicGaussianFiberEulerRatioShellWeight
import SMSFormula.AdelicGaussianFiberEulerRatioMeasure
import SMSFormula.AdelicGaussianCapstoneIntegralAssembly

/-!
# Theta identity at an integral representative for every Euler fiber measure (rank at least four)

Let `L` be a lattice of rank at least four, `b` a represented norm with an integral representative
`z`, and `σ` any regular `SO(𝔸)`-invariant measure on the value fiber `X_{Q(z)}` with the two Euler
laws at `M = Q(z)`:
* the local-restriction law `σ(U_R) = (∏ gR/∏ gF) · σ(X ∩ {x_f integral})` of carried fiber sets;
* the integral-carrier mass `σ(X ∩ {x_f integral}) = ofReal(Re d_∞(a_∞) · ∏'_p δ_p(M))`.
Then there is an integral complement lattice `L_W` of `z` with raw Tamagawa data such that for every
measurable `φ ≥ 0`

`Θ_b(φ) · τ(Spin_L) = τ(Spin_{L_W}) · ∫⁻_{X_{Q(z)}} φ dσ`

(`exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_measure`).  Every
other input is supplied as in
`exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral`;
the Riesz measure (rank at least five) is replaced by the supplied `σ`, whose two laws make its
raw orbit ratio a fiber Euler ratio for the internal presentation (`isFiberEulerRatio_of_measure`).
Nothing is chosen in the statement: `σ`, its laws and `φ` are supplied.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Set Filter QuadraticMap
open SMSFormula.CompactOrbit
open scoped ENNReal NNReal Topology

local instance feriT2Infinite : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance feriT2Finite : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance feriT2Adele : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

local instance feriDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance feriPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance feriPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance feriPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

set_option maxHeartbeats 8000000 in
/-- The represented-norm theta identity at an integral representative for a supplied Euler
fiber measure: `Θ_b(φ) · τ_L = τ_{L_W} · ∫⁻ φ dσ` in every rank at least four. -/
theorem exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_of_measure
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA)
    {w : ℝ} (hw : 0 < w)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (z : Fin (s + 2 + 1) → ℤ)
    (hz : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1)
    (σ : Measure (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))) [σ.Regular]
    [SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ))))) σ]
    (hloc : ∀ (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (s + 2 + 1) → ZMod (p ^ e p)))
      (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞),
      (∀ p ∈ Pr, gF p ≠ 0) → (∀ p ∈ Pr, gF p ≠ ⊤) →
      (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount (L.quadForm z) Pr e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount (L.quadForm z) (p ^ v) : ℝ≥0∞) * gR p) →
      (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount (L.quadForm z) (p ^ v) ≠ 0) →
      haveI : NeZero (localRestrictionLevel Pr e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
      σ (fiberResidueRestrictedSet L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ))))
          (localRestrictionLevel Pr e) (localRestrictionSet Pr e R)) =
        ((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) *
          σ (fiberDividedCarrier L (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) 1))
    (hcar : σ (fiberDividedCarrier L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) 1) =
      ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L w (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))))).re *
        ∏' p : Nat.Primes, L.localResidueDensity (L.quadForm z) p))
    (φ : (Fin (s + 2 + 1) → RationalAdele) → ℝ≥0∞) (hφm : Measurable φ) :
    ∃ (LW : PositiveDefiniteIntegralLattice (s + 2))
      (_ : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction
          (fun i ↦ (z i : ℚ))))
      (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA b φ rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        ∫⁻ y, φ y.val ∂σ := by
  revert σ
  set x : Fin (s + 2 + 1) → ℚ := fun i ↦ (z i : ℚ) with hxdef
  intro σ _ _ hloc hcar
  have hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0 := by
    rw [hz]
    exact b.2.1
  have hxint : ∀ i, x i ∈ (algebraMap ℤ ℚ).range := fun i ↦ ⟨z i, rfl⟩
  obtain ⟨LW, eIso, hEint⟩ :=
    L.exists_integralLatticeAnisotropicComplementPresentation_integral x hx hxint
  set P := RationalQuadraticSpaceMatrix.integralLatticeAnisotropicComplementPresentation LW
    L.rationalQuadraticSpaceMatrix x eIso with hPdef
  let instL : Fintype LW.ConcreteProperRationalDoubleCosetSet :=
    LW.concreteProperRationalDoubleCosetSetFintype
  obtain ⟨PL, hPL0, hL⟩ :=
    LW.exists_pos_massLocalInverseProductTendsTo (by omega)
  refine ⟨LW, eIso, instL, PL, hPL0, hL, ?_⟩
  -- the integer value `M = Q(z)`
  set M : ℤ := L.quadForm z with hMdef
  have hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ) :=
    L.nativeRationalQuadraticForm_intVector z
  have hM0 : M ≠ 0 := by
    intro h
    apply hx
    rw [hM, h, Int.cast_zero]
  -- the bad set `B` and its local orbit-mass data
  set B := P.lowerSpace.lastExtensionHorizontalBadPlaces
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx with hBdef
  choose Uv Kv c hloc' using fun v : {v // v ∈ B} ↦ P.exists_capstoneLocalOrbitMassData hx v.1
  -- the tail support
  obtain ⟨Sp, hSp⟩ := P.exists_horizontalIntegralTailPresentationSupport hx
  -- the real central cutoff
  obtain ⟨T, hT, hneg, hT0, hTtop⟩ := exists_realUnitCentralCutoffSet
  -- the finite tail place set
  have hD : P.presentationDenominator hx ≠ 0 := by
    unfold RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation.presentationDenominator
    refine mul_ne_zero ?_ ?_ <;>
      exact Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j _ ↦ Rat.den_ne_zero _
  obtain ⟨TE, hATE, h2T, hqT, hE⟩ := exists_capstoneTailPlaces (P.presentationDenominator hx) hD M hM0
    (P.lowerSpace.goodPlaceExceptionalPrimes
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
      L.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx))
    (P.lowerSpace.lastOrbitGaugeRatio
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)
    (P.rationalShellFactor hx)
    (Sp ∪ B ∪ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ∪
      LW.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
  have hST : Sp ⊆ TE := fun v hv ↦ hATE (by simp [hv])
  have hBT : B ⊆ TE := fun v hv ↦ hATE (by simp [hv])
  have hOddA : L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ TE :=
    fun v hv ↦ hATE (by simp [hv])
  have hOddW : LW.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ TE :=
    fun v hv ↦ hATE (by simp [hv])
  have hxintB : ∀ v ∈ B, ∀ i, algebraMap ℚ ℚ_[(primesEquiv v).1] (x i) ∈
      PadicInt.subring (primesEquiv v).1 := by
    intro v _ i
    rw [hxdef, map_intCast]
    exact intCast_mem _ _
  have hρ := isFiberEulerRatio_of_measure L P hx (by omega) w σ
    (L.rationalDiagonalValueFiberPoint x) L.fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isCompact_fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isOpen_fullAdelicLatticeStabilizerOnMatrixCarrier M hloc hcar
  have h := representedNormTheta_mul_spinTamagawa_eq_core_of_ratio L P hx hw M hM hρ B
    (capstone_hodd_self L P hx) (capstone_haunit_self L P hx)
    (capstone_hden_self L P hx hEint) hT hneg hT0 hTtop (subset_refl _)
    Uv (fun v ↦ (hloc' v).1) (fun v ↦ (hloc' v).2.1) Kv (fun v ↦ (hloc' v).2.2.1)
    (fun v ↦ (hloc' v).2.2.2.1) (fun v ↦ (hloc' v).2.2.2.2.1) c (fun v ↦ (hloc' v).2.2.2.2.2.1)
    (LW.posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real)
    (L.nativeRationalQuadraticForm_pos_of_ne_zero hx)
    (fun v ↦ (hloc' v).2.2.2.2.2.2.1) (fun v ↦ (hloc' v).2.2.2.2.2.2.2.1)
    (fun v ↦ (hloc' v).2.2.2.2.2.2.2.2) hxintB (capstone_hgp_self L P hx)
    LW (by omega) instA instL b hz eIso rfl (L.oneShellSpinCoefficientLocallyNonempty (by omega))
    rationalIdeleClassUnitLogCutoff measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero rationalIdeleClassLogCutoffLIntegral_unit_ne_top
    ∅ ∅ hPA0 hPL0 hA hL TE hE Sp hSp hST h2T hOddA hOddW hBT hqT φ hφm
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ s + 2 + 1)
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  have hσ := eq_smul_of_compactOpen_subgroup σ (nativeShellMeasureOnValueFiber L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) (L.rationalDiagonalValueFiberPoint x)
    L.fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isCompact_fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isOpen_fullAdelicLatticeStabilizerOnMatrixCarrier (nativeShellMeasureOnValueFiber_ne_zero L P hx)
  rw [hσ, lintegral_smul_measure]
  exact h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
