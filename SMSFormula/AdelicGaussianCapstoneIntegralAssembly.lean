import SMSFormula.AdelicGaussianCapstoneSimpleInputs
import SMSFormula.AdelicGaussianCapstoneLocalOrbitMassData
import SMSFormula.AdelicGaussianIntegralRepresentativeShells
import SMSFormula.RationalAdeleShellRepresentationNumber

/-!
# The theta–Tamagawa identity at an integral representative

Let `L` be a lattice of rank `≥ 5`, `ψ` a nonnegative member of the real Gaussian core, and `b` a
represented norm with an integral representative `z`.  There is an integral complement lattice `L_W`
of `z` with raw Tamagawa data (class-set finiteness `concreteProperRationalDoubleCosetSetFintype`,
Schulze-Pillot limit) such that

`Θ_b(ψ) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal ρ_ψ(b)`.

All inputs of the general identity are proved here: the integral presentation and complement
(`exists_integralLatticeAnisotropicComplementPresentation_integral`), `S := B` with
`hodd/haunit/hSB/hgp/hden`, the local orbit-mass data at every `v ∈ B`
(`exists_capstoneLocalOrbitMassData`), the elementary inputs (`AdelicGaussianCapstoneSimpleInputs`),
the tail support `Sp`, the Schulze-Pillot limit, and the unit cutoff.

Consequently `τ(Spin_L) = 1` follows from `τ = 1` for every rank-`n - 1` lattice
(`spinTamagawaNumberENNReal_eq_one_of_complementSpinTamagawa`), and by induction `τ(Spin) = 1` in
every rank `≥ 4` follows from rank four alone (`spinTamagawaNumberENNReal_eq_one_of_rankFour`).
-/

noncomputable section

open MeasureTheory Matrix PositiveDefiniteIntegralLattice Set Filter QuadraticMap
open scoped ENNReal NNReal Topology

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

local instance ciaDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance ciaPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance ciaPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance ciaPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

set_option maxHeartbeats 8000000 in
/-- The complement identity at an integral representative:
`Θ_b(ψ) · τ_L = τ_{L_W} · ofReal ρ_ψ(b)` for an integral complement lattice `L_W` of the supplied
integral representative. -/
theorem exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hn : 4 < s + 2 + 1)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA)
    {w : ℝ} (hw : 0 < w) (ψ : realGaussianCore L w) (hψ : ∀ y, 0 ≤ ψ.val y)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (z : Fin (s + 2 + 1) → ℤ)
    (hz : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1) :
    ∃ (LW : PositiveDefiniteIntegralLattice (s + 2)) (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA b (fun y ↦ ENNReal.ofReal (ψ.val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val
          (algebraMap ℚ RationalAdele b.1)) := by
  set x : Fin (s + 2 + 1) → ℚ := fun i ↦ (z i : ℚ) with hxdef
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
  refine ⟨LW, instL, PL, hPL0, hL, ?_⟩
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
  choose Uv Kv c hloc using fun v : {v // v ∈ B} ↦ P.exists_capstoneLocalOrbitMassData hx v.1
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
  have hψm : Measurable (fun y ↦ ENNReal.ofReal (ψ.val y)) :=
    (continuous_of_mem_realGaussianCore L w ψ.2).measurable.ennreal_ofReal
  have h := representedNormTheta_mul_spinTamagawa_eq_core L P hx hn hw
    (L.rationalDiagonalValueFiberPoint x) L.fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isCompact_fullAdelicLatticeStabilizerOnMatrixCarrier
    L.isOpen_fullAdelicLatticeStabilizerOnMatrixCarrier
    M hM B (capstone_hodd_self L P hx) (capstone_haunit_self L P hx)
    (capstone_hden_self L P hx hEint) hT hneg hT0 hTtop (subset_refl _)
    Uv (fun v ↦ (hloc v).1) (fun v ↦ (hloc v).2.1) Kv (fun v ↦ (hloc v).2.2.1)
    (fun v ↦ (hloc v).2.2.2.1) (fun v ↦ (hloc v).2.2.2.2.1) c (fun v ↦ (hloc v).2.2.2.2.2.1)
    (LW.posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real)
    (L.nativeRationalQuadraticForm_pos_of_ne_zero hx)
    (fun v ↦ (hloc v).2.2.2.2.2.2.1) (fun v ↦ (hloc v).2.2.2.2.2.2.2.1)
    (fun v ↦ (hloc v).2.2.2.2.2.2.2.2) hxintB (capstone_hgp_self L P hx)
    LW (by omega) instA instL b hz eIso rfl (L.oneShellSpinCoefficientLocallyNonempty (by omega))
    rationalIdeleClassUnitLogCutoff measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero rationalIdeleClassLogCutoffLIntegral_unit_ne_top
    ∅ ∅ hPA0 hPL0 hA hL TE hE Sp hSp hST h2T hOddA hOddW hBT hqT ψ hψ hψm
  rwa [hz] at h

/-- Some positive width has dilation constant `D · (1/√a)^N ≠ 1` (`N ≠ 0`): `a = 1` or `a = 4`. -/
theorem exists_pos_dilationConstant_ne_one {N : ℕ} (hN : N ≠ 0) (D : ℝ) :
    ∃ a : ℝ, 0 < a ∧ D * (1 / a ^ (1 / 2 : ℝ)) ^ N ≠ 1 := by
  by_cases hD : D = 1
  · refine ⟨4, by norm_num, ?_⟩
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hD, h4, one_mul]
    exact (pow_lt_one₀ (by norm_num) (by norm_num) hN).ne
  · refine ⟨1, one_pos, ?_⟩
    simpa using hD

/-- The rank induction step: if `τ(Spin) = 1` for every lattice of rank `n - 1`, then
`τ(Spin_L) = 1` for every lattice `L` of rank `n ≥ 5`. -/
theorem spinTamagawaNumberENNReal_eq_one_of_complementSpinTamagawa
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hn : 4 < s + 2 + 1)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA)
    (hW : ∀ (LW : PositiveDefiniteIntegralLattice (s + 2)) (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal
        = 1) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal
      = 1 := by
  haveI : Nonempty (Fin (s + 2 + 1)) := ⟨0⟩
  obtain ⟨a, ha, hC⟩ := exists_pos_dilationConstant_ne_one (N := s + 2 + 1) (by omega)
    ((L.polarRealDeterminantScale : ℝ)⁻¹)
  refine L.spinTamagawaNumberENNReal_eq_one_of_integralRepresentativeShellIdentities (r := s + 1)
    (by omega) (by omega) instA hPA0 hA ha hC ?_
  intro w hw ψ hψ b ⟨z, hz⟩
  obtain ⟨LW, instL, PL, hPL0, hL, h⟩ :=
    exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral L hn instA hPA0 hA hw
      ψ hψ b z hz
  rw [h, hW LW instL PL hPL0 hL, one_mul]

/-- The rank induction: `τ(Spin) = 1` in rank four gives `τ(Spin) = 1` in every rank `≥ 4`. -/
theorem spinTamagawaNumberENNReal_eq_one_of_rankFour
    (h4 : ∀ (L : PositiveDefiniteIntegralLattice 4) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
      (P : ℝ) (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P),
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) inst hP hconv).spinTamagawaNumberENNReal
        = 1)
    (k : ℕ) (L : PositiveDefiniteIntegralLattice (k + 4)) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) inst hP hconv).spinTamagawaNumberENNReal
      = 1 := by
  induction k generalizing P with
  | zero => exact h4 L inst P hP hconv
  | succ k ih =>
    exact spinTamagawaNumberENNReal_eq_one_of_complementSpinTamagawa (s := k + 2) L (by omega) inst hP
      hconv (fun LW instL PL hPL0 hL ↦ ih LW instL PL hPL0 hL)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
