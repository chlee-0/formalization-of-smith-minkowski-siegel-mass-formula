import SMSFormula.AdelicGaussianOneShellWeightLocal
import SMSFormula.AdelicGaussianShellWeightDeterminantGlue
import SMSFormula.NonisotropicLastExtensionOddUnimodular
import SMSFormula.AdelicGaussianCoreOneShellWeightLocal

/-!
# The shell weight for every nonnegative core test

For every nonnegative member `ψ` of the real Gaussian core at width `b` (in particular the
polar Gaussian lattice test and the dual-carrier test), with the supplied chain data,
`Θ_a(ψ) · τ(Spin_V) = τ(Spin_{W_a}) · ofReal(d_ψ(a))`.  Core-test version of
`representedNormTheta_mul_spinTamagawa_eq`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

variable {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance oswcDecidableEqK : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance oswcPrimeFactK (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance oswcPadicMeasurableSpaceK (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance oswcPadicBorelSpaceK (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance oswcShellMeasurableSpaceK : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance oswcShellBorelSpaceK : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < s + 2 + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

include hb x₀ in
set_option maxHeartbeats 8000000 in
/-- The shell weight of one represented shell: `Θ_a · τ(Spin_V) = τ(Spin_{W_a}) · d_Φ(a)`. -/
theorem representedNormTheta_mul_spinTamagawa_eq_core
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
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
        (by omega : 1 ≤ s + 1) instA hPA0 hA an (fun y ↦ ENNReal.ofReal (ψ.val y)) f *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val
        (algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))) := by
  haveI : NeZero (s + 2) := ⟨by omega⟩
  obtain ⟨e, R, gF, gR, D, h1, h2, h3, h4⟩ :=
    exists_representedNormTheta_mul_prod_localDenominator_eq_core L P hx hn hb x₀ K hc ho M hM S hodd haunit hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hKlat hxint hgp LW hs instA instL an hxa eIso hP hLocal f hf hcutoffMass_ne_zero hcutoffMass_ne_top SA SL hPA0 hPL0 hA hL T hE Sp hSp hST h2T hOddA hOddW hBT hqT ψ hψ hψm
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

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
