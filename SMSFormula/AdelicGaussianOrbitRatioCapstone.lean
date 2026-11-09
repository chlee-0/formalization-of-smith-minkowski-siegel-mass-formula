import SMSFormula.AdelicGaussianLocalScaleBadPlace
import SMSFormula.AdelicGaussianOrbitRatioCancellation

/-!
# The orbit Riesz ratio with the local densities cancelled

From the evaluated orbit Riesz ratio at the integral-completed central cutoff, the exposed carrying
property of the residue data gives, at each bad place `v ∈ B`, an intrinsic local scale `D_v`
with `gR · D_v = gF · c_v`,

`D_v = r_v · (ν(ℤ_p) · glue_block(E_v⁻¹ ℤ_p^n))`   (in every covering block atlas),

and at the remaining places of `S ∪ bad` (where the presentation image of the local orbit has the
integral lattice shell as trace) `gR = gF`.  The local densities `c_v` then cancel against the
orbit mass:

`σ(U)/M_native(U) = c_G · ofReal(Re d_∞ · ∏'_p δ_p(M)) · μ_W ∏_B s_W / (∏_B D_v · μ_V ∏_B s_V)`.

Supplied: the stabilizer identities through carrying sets at `B` (chart data) with their gauges
`r_v ∈ (0,∞)`, the good-orbit traces off `B`, orbit integrality, and the orbit-mass inputs.
Nothing is chosen in the conclusion; `D_v` is characterized in every block atlas.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal

local instance orbitCapstoneDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance orbitCapstonePrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

local instance ocPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance ocPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The good-place identity from the carrying property: if the presentation image of the local orbit
has the integral lattice shell as trace, then `gR = gF` (the lattice atlas is produced inside). -/
theorem localMass_eq_of_carry_of_integralTrace {n m : ℕ} (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
    (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
    (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
    (M : ℤ) (Pr : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ Pr) {gF gR : ℝ≥0∞}
    (hloc : ∀ᶠ v : ℕ in Filter.atTop, (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF =
      (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR)
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0)
    (hMx : algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) =
      (((M : ℤ) : ℤ_[p]) : ℚ_[p]))
    {O' : Set (P.lowerSpace.nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p])}
    (hcarry : ∀ z : P.lowerSpace.nonisotropicLastQuadraticShell
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p],
      P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 ∈
        PadicInt.restrictedIntegralVectors (e p) (R p) ↔ z ∈ O')
    (hrep : ∃ z ∈ O', ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z.1 i ∈
      PadicInt.subring p)
    (hgood : ∀ w : Fin n → ℚ_[p], (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') w = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) →
      (w ∈ (P.blockToAmbientPadicContinuousLinearEquiv hx p) '' (Subtype.val '' O') ↔ ‖w‖ ≤ 1)) :
    gR = gF := by
  obtain ⟨z₀, _, hz₀⟩ := hrep
  set u := P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] z₀.1 with hudef
  have hu1 : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ hz₀ i
  have hu : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') u = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) := by
    rw [← hMx, hudef, ← P.blockToAmbientPadicContinuousLinearEquiv_apply,
      latticeGram_blockToAmbient L P hx p]
    exact z₀.2
  obtain ⟨point₂, hpoint₂, hcover₂⟩ := (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').exists_padicSquareBranchAtlas_cover p
    ⟨u, by rw [hu]; exact hM⟩
  have hG := padicSquareBranchAtlasGlue_integral_ne_zero_ne_top _ point₂ hpoint₂
    (fun _ ↦ Measure.addHaar) Measure.addHaar Measure.addHaar hcover₂ hM hu1 hu
  have hFne := L.eventually_fullResidueCount_primePow_ne_zero_of_eq M _ rfl _ rfl hM point₂
    hpoint₂ (fun _ ↦ Measure.addHaar) Measure.addHaar Measure.addHaar hcover₂ hG.1
  have htrace := inter_latticeShell_eq_image_of_carry L P hx p hcarry
  rw [hMx] at htrace
  refine localMass_eq_of_slice_eq_integral L M Pr e R hPr hp hloc hFne hM point₂ hpoint₂
    (fun _ ↦ Measure.addHaar) Measure.addHaar Measure.addHaar hcover₂ hG.1 hG.2 ?_
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [← hgood w.1 w.2, ← htrace]
  exact ⟨fun h ↦ ⟨h, w.2⟩, fun h ↦ h.1⟩

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

set_option maxHeartbeats 4000000 in
/-- The orbit Riesz ratio with the local densities cancelled. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct
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
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) := by
  obtain ⟨e, R, gF, gR, he, hcar, hgF0, hgFt, hlocc, hr⟩ :=
    exists_div_nativeShellMeasure_eq_localRatio_eulerProduct_orbitMass L P hx hn hb x₀ K hc ho M hM
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

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
