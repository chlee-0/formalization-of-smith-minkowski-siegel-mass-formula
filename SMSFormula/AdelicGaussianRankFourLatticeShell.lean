import SMSFormula.AdelicGaussianRankFourDensityUnitLaws
import SMSFormula.RationalAdeleDilatedLatticeTubeLimit
import SMSFormula.AdelicGaussianIntegralRepresentativeShells
import SMSFormula.RationalAdeleRankOneEisensteinPoisson

/-!
# The rank-four shell identity for the lattice test at every shell

For the polar Gaussian lattice test `Φ_a = G_a ⊗ 1_{Ẑⁿ}` and every represented nonzero norm `b`
of a lattice of rank at least four:

`Θ_b(Φ_a) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(ρ_Φ(b))`,  `ρ_Φ(b) = [b ∈ ℤ] Re Â_a(b) · ∏'_p δ_p(b)`

(`exists_complement_representedNormTheta_latticeTest_mul_spinTamagawa_eq_rankFour`). The proof
dilates `b` to `k² b` with an integral representative (`exists_nat_smul_integral`, theta dilation),
applies the rank-four shell identity to the dilated test, and evaluates `D⁴` on it: the Gaussian is
constant on the real sphere, the finite factor is the dilated lattice indicator
(`RationalAdeleDilatedLatticeTubeLimit`), and the archimedean scale is `c_∞(k²b) = k^{n−2} c_∞(b)`.
`Â_a` is the `fourier_polarArchimedeanBruhatFactor_of_pos`. Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix FourierTransform

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The polar Gaussian through the real quadratic value: `G_b(x) = e^{−2π b Q_ℝ(x)}`. -/
theorem realShiftedGaussian_zero_eq_exp (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (x : Fin n → ℝ) :
    realShiftedGaussian L b 0 x =
      Real.exp (-(2 * Real.pi * b) * L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) := by
  rw [realShiftedGaussian_eq, SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  simp only [ContinuousMap.id_apply, sub_zero]
  rw [polarQuadraticForm_apply, realPolarMatrix_eq_two_smul_realFormMatrix, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  congr 1
  unfold RationalQuadraticSpaceMatrix.realQuadraticFormValue
  ring

/-- The dilated lattice test, section by section: on the real sphere `{Q_ℝ = c}` its real section is the
constant `e^{−2π a c/k²}` times the dilated lattice indicator. -/
theorem finiteSectionAverage_dilatedLatticeTest (L : PositiveDefiniteIntegralLattice n) [NeZero n] (a : ℝ) {k : ℕ}
    (hk : k ≠ 0) (x₀ : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    (finiteSectionAverage L x₀ (realGaussianCoreDilate L hk (polarGaussianLatticeCore L a)).val xf : ℂ) =
      ((Real.exp (-(2 * Real.pi * (a * ((k : ℝ))⁻¹ ^ 2)) *
        L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀) : ℝ) : ℂ) *
        dilatedIntegralIndicator n k xf := by
  have hsec : (fun xr ↦ (realGaussianCoreDilate L hk (polarGaussianLatticeCore L a)).val
      (rationalAdeleVectorJoin n xr xf)) =
      realResidueRestrictedIndicator n 1 Set.univ (rationalFiniteAdeleCoordinateScale ((k : ℚ))⁻¹ xf) •
        realShiftedGaussian L (a * ((k : ℝ))⁻¹ ^ 2) 0 := by
    funext xr
    change realShiftedGaussian L a 0 (rationalAdeleVectorRealPart n
        (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ (rationalAdeleVectorJoin n xr xf))) *
      realResidueRestrictedIndicator n 1 Set.univ (rationalAdeleVectorFinitePart n
        (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ (rationalAdeleVectorJoin n xr xf))) = _
    rw [rationalAdeleVectorRealPart_rationalDilation, rationalAdeleVectorFinitePart_rationalDilation,
      rationalAdeleVectorRealPart_join, rationalAdeleVectorFinitePart_join, realShiftedGaussian_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm]
    push_cast
    rfl
  unfold finiteSectionAverage
  rw [hsec, L.rationalQuadraticSpaceMatrix.realOrbitAverage_smul,
    L.rationalQuadraticSpaceMatrix.realOrbitAverage_eq_of_sphere
      L.posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real x₀
      (c := Real.exp (-(2 * Real.pi * (a * ((k : ℝ))⁻¹ ^ 2)) *
        L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀))
      (fun xr hxr ↦ by rw [realShiftedGaussian_zero_eq_exp, hxr])]
  rw [Complex.ofReal_mul, mul_comm, coe_realResidueRestrictedIndicator, residueRestrictedIndicator_univ]
  rfl

/-- The rank-four lattice shell density `ρ_Φ(b) = [b ∈ ℤ] Re Â_a(b) · ∏'_p δ_p(b)`. -/
def latticeShellDensity (L : PositiveDefiniteIntegralLattice (n + 1)) (a : ℝ) (b : ℚ) : ℝ :=
  if b.den = 1 then (𝓕 (L.polarArchimedeanBruhatFactor a) (b.num : ℝ)).re *
    ∏' p : Nat.Primes, L.localResidueDensity b.num p else 0

/-- The archimedean rescaling `(k² m)^{N/2−1} · k²/k^N = m^{N/2−1}`. -/
theorem rpow_dilate_mul (N : ℕ) (hN : 2 ≤ N) {k : ℕ} (hk : k ≠ 0) {m : ℝ} (hm : 0 ≤ m) :
    ((k : ℝ) ^ 2 * m) ^ ((N : ℝ) / 2 - 1) * ((k : ℝ) ^ 2 / (k : ℝ) ^ N) = m ^ ((N : ℝ) / 2 - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Real.mul_rpow (by positivity) hm]
  have hpow : ((k : ℝ) ^ 2) ^ ((N : ℝ) / 2 - 1) = (k : ℝ) ^ (N - 2) := by
    rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_mul hk0.le, ← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hN]
    ring
  rw [hpow]
  have hN' : N = (N - 2) + 2 := by omega
  have hk2 : (k : ℝ) ^ N = (k : ℝ) ^ (N - 2) * (k : ℝ) ^ 2 := by
    rw [← pow_add, ← hN']
  rw [hk2]
  field_simp

set_option maxHeartbeats 1600000 in
/-- `D⁴` of the dilated lattice test: at an integral point `z` of norm `k² b`,
`D⁴_z(Φ_a(·/k)) = ρ_Φ(b)`. -/
theorem rankFourDensityAt_dilatedLatticeTest (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {a : ℝ}
    (ha : 0 < a) {k : ℕ} (hk : k ≠ 0) (z : Fin (n + 1) → ℤ) (hz : L.quadForm z ≠ 0) {b : ℚ}
    (hb : ((k : ℚ)) ^ 2 * b = L.quadForm z) :
    (rankFourDensityAt L hn (w := a * ((k : ℝ))⁻¹ ^ 2)
        (by have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
            positivity) z hz).toLinearMap
      (realGaussianCoreDilate L hk (polarGaussianLatticeCore L a)) = latticeShellDensity L a b := by
  classical
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hQz : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue (fun i ↦ (z i : ℝ)) =
      (k : ℝ) ^ 2 * (b : ℝ) := by
    rw [realQuadraticFormValue_intVector]
    have := congrArg (fun q : ℚ ↦ (q : ℝ)) hb
    push_cast at this
    linarith
  have hbpos : 0 < b := by
    have hpos : 0 < (L.quadForm z : ℚ) := by
      have h := L.nativeRationalQuadraticForm_pos_of_ne_zero (x := fun i ↦ (z i : ℚ)) (by
        rw [L.nativeRationalQuadraticForm_intVector z]; exact_mod_cast hz)
      rwa [L.nativeRationalQuadraticForm_intVector z] at h
    rw [← hb] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
  -- the finite section is the constant `e^{-2π a b}` times the dilated lattice indicator
  have hsec : (fun xf ↦ (finiteSectionAverage L (fun i ↦ (z i : ℝ))
      (realGaussianCoreDilate L hk (polarGaussianLatticeCore L a)).val xf : ℂ)) =
      fun xf ↦ ((Real.exp (-(2 * Real.pi * a) * (b : ℝ)) : ℝ) : ℂ) *
        dilatedIntegralIndicator (n + 1) k xf := by
    funext xf
    rw [finiteSectionAverage_dilatedLatticeTest, hQz]
    congr 3
    field_simp
  rw [rankFourDensityAt_apply]
  unfold rankFourFiniteDensity
  simp_rw [hsec, finiteTubeMass_const_mul]
  -- the archimedean scale
  have hscalar : rationalAdeleRealScalar (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) =
      (k : ℝ) ^ 2 * (b : ℝ) := by
    rw [← hQz, realQuadraticFormValue_intVector_eq_realScalar]
    rfl
  have hcInf := re_realLocalValueDensity_gaussianOrbitTestRealFactor L (b := a * ((k : ℝ))⁻¹ ^ 2)
    (by positivity) (by omega) (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ))))
    (by rw [hscalar]; positivity)
  rw [hcInf, hscalar]
  unfold latticeShellDensity
  by_cases hden : b.den = 1
  · rw [if_pos hden]
    have hbnum : (b.num : ℚ) = b := by
      have := Rat.num_div_den b
      rw [hden, Nat.cast_one, div_one] at this
      exact this
    have hMz : L.quadForm z = (k : ℤ) ^ 2 * b.num := by
      have h := hb
      rw [← hbnum] at h
      exact_mod_cast h.symm
    have hnum0 : b.num ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hMz; exact hz hMz
    have hlim := (L.tendsto_finiteTubeMass_dilatedIntegral_of_int hn hk hnum0).const_mul
      ((Real.exp (-(2 * Real.pi * a) * (b : ℝ)) : ℝ) : ℂ)
    rw [← hMz] at hlim
    rw [hlim.limUnder_eq]
    have hbR : (b : ℝ) = (b.num : ℝ) := by exact_mod_cast hbnum.symm
    rw [fourier_polarArchimedeanBruhatFactor_of_pos L ha (by omega)
      (by rw [← hbR]; exact_mod_cast hbpos), Complex.ofReal_re]
    have hkc : (k : ℂ) ^ 2 / (k : ℂ) ^ (n + 1) = (((k : ℝ) ^ 2 / (k : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hkc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, ← hbR]
    have hr := rpow_dilate_mul (n + 1) (by omega) hk (m := (b : ℝ)) (by exact_mod_cast hbpos.le)
    linear_combination ((L.polarRealDeterminantScale : ℝ)⁻¹ *
      ((2 * Real.pi) ^ (((n + 1 : ℕ) : ℝ) / 2) / Real.Gamma (((n + 1 : ℕ) : ℝ) / 2)) *
      Real.exp (-(2 * Real.pi * a) * (b : ℝ)) * ∏' p : Nat.Primes, L.localResidueDensity b.num p) * hr
  · rw [if_neg hden]
    have hbint : b ∉ (algebraMap ℤ ℚ).range := by
      rintro ⟨m, rfl⟩
      exact hden (by simp)
    have hlim := (L.tendsto_finiteTubeMass_dilatedIntegral_of_not_int hn hk hz hb hbint).const_mul
      ((Real.exp (-(2 * Real.pi * a) * (b : ℝ)) : ℝ) : ℂ)
    rw [mul_zero] at hlim
    rw [hlim.limUnder_eq, Complex.zero_re, mul_zero]

/-- The rank-four shell identity for the lattice test at every shell:
`Θ_b(Φ_a) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(ρ_Φ(b))`. -/
theorem exists_complement_representedNormTheta_latticeTest_mul_spinTamagawa_eq_rankFour
    {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) (hs : 1 ≤ s)
    (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ} (hPA0 : 0 < PA)
    (hA : massLocalInverseProductTendsTo L PA) {a : ℝ} (ha : 0 < a)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm) :
    ∃ (x : Fin (s + 2 + 1) → ℚ) (_ : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
      (LW : PositiveDefiniteIntegralLattice (s + 2))
      (_ : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x))
      (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by omega : 1 ≤ s + 1) instA hPA0 hA b
          (fun y ↦ ENNReal.ofReal ((polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by omega) instA hPA0 hA).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by omega) instL hPL0 hL).spinTamagawaNumberENNReal *
        ENNReal.ofReal (latticeShellDensity L a b.1) := by
  obtain ⟨x, hx⟩ := b.2.2
  obtain ⟨k, hk, z, hz⟩ := exists_nat_smul_integral x
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hw' : 0 < a * ((k : ℝ))⁻¹ ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  have hzb : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) =
      (RepresentedNonzeroRationalNorm.dilate _ b hkq).1 := by
    rw [hz, QuadraticMap.map_smul, hx, smul_eq_mul, RepresentedNonzeroRationalNorm.dilate_coe]
    ring
  obtain ⟨hz0, LW, eW, instL, PL, hPL0, hL, h⟩ :=
    exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_rankFour L hs instA hPA0 hA
      hw' (RepresentedNonzeroRationalNorm.dilate _ b hkq) z hzb
      (realGaussianCoreDilate L hk (polarGaussianLatticeCore L a))
      (fun y ↦ polarGaussianLatticeCore_nonneg L a _)
  refine ⟨fun i ↦ (z i : ℚ), by rw [hzb]; exact (RepresentedNonzeroRationalNorm.dilate _ b hkq).2.1,
    LW, eW, instL, PL, hPL0, hL, ?_⟩
  have htheta : L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      (by omega : 1 ≤ s + 1) instA hPA0 hA (RepresentedNonzeroRationalNorm.dilate _ b hkq)
      (fun y ↦ ENNReal.ofReal ((realGaussianCoreDilate L hk (polarGaussianLatticeCore L a)).val y))
      rationalIdeleClassUnitLogCutoff =
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
        (by omega : 1 ≤ s + 1) instA hPA0 hA b
        (fun y ↦ ENNReal.ofReal ((polarGaussianLatticeCore L a).val y)) rationalIdeleClassUnitLogCutoff := by
    unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    dsimp only
    rw [← L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_dilate
      b hkq (fun y ↦ ENNReal.ofReal ((polarGaussianLatticeCore L a).val y))]
    rfl
  have hbk : ((k : ℚ)) ^ 2 * b.1 = L.quadForm z := by
    rw [← L.nativeRationalQuadraticForm_intVector z, hzb, RepresentedNonzeroRationalNorm.dilate_coe]
  rw [htheta, rankFourDensityAt_dilatedLatticeTest L (by omega) ha hk z hz0 hbk] at h
  exact h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
