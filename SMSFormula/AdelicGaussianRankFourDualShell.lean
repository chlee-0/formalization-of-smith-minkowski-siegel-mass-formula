import SMSFormula.AdelicGaussianRankFourLatticeShell
import SMSFormula.RationalLatticeDualClassDecomposition

/-!
# The rank-four shell identity for the dual test at every shell

For the dual-carrier test `Ψ_α = G_α ⊗ 1_{L^#}` (`polarGaussianDualCore`) of a rank-four lattice and every
represented nonzero norm `b`:

`Θ_b(Ψ_α) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(ρ_Ψ(b))`,
`ρ_Ψ(b) = [d²b ∈ ℤ] Re Â_α(b) · d² · Re Σ_{a ∈ A} D_a(d² b)`

(`exists_complement_representedNormTheta_dualTest_mul_spinTamagawa_eq_rankFour`), where `d = |det S|`, `A` is the
discriminant group and `D_a(M)` the tube limit of the class `a` (`dualClassTubeLimit`), which is
`d²/d⁴ · ∏'_p δ^{cos}_p(u, λ)` at `M = q(adj(S)u) + d²λ` and `0` otherwise.  The proof dilates `b` by `k = k₀ d`
(`k₀` the integral multiple of the supplied representative), so that `1_{L^#}(·/k)` is the `k₀`-dilate of the
dilated dual indicator `1_{L^#}(·/d) = Σ_a 1_{U_a}`, and applies the rank-four shell identity.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix FourierTransform

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The dilated dual test, section by section. -/
theorem finiteSectionAverage_dilatedDualTest (L : PositiveDefiniteIntegralLattice n) [NeZero n] (α : ℝ) {k : ℕ}
    (hk : k ≠ 0) (x₀ : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    (finiteSectionAverage L x₀ (realGaussianCoreDilate L hk (polarGaussianDualCore L α)).val xf : ℂ) =
      ((Real.exp (-(2 * Real.pi * (α * ((k : ℝ))⁻¹ ^ 2)) *
        L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀) : ℝ) : ℂ) *
        ((realFinitePolarDualLatticeIndicator L
          (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • xf) : ℝ) : ℂ) := by
  have hsec : (fun xr ↦ (realGaussianCoreDilate L hk (polarGaussianDualCore L α)).val
      (rationalAdeleVectorJoin n xr xf)) =
      realFinitePolarDualLatticeIndicator L (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • xf) •
        realShiftedGaussian L (α * ((k : ℝ))⁻¹ ^ 2) 0 := by
    funext xr
    change realShiftedGaussian L α 0 (rationalAdeleVectorRealPart n
        (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ (rationalAdeleVectorJoin n xr xf))) *
      realFinitePolarDualLatticeIndicator L (rationalAdeleVectorFinitePart n
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
      (c := Real.exp (-(2 * Real.pi * (α * ((k : ℝ))⁻¹ ^ 2)) *
        L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀))
      (fun xr hxr ↦ by rw [realShiftedGaussian_zero_eq_exp, hxr])]
  rw [Complex.ofReal_mul, mul_comm]

/-- At the dilation `k₀ d`, the dual indicator is the `k₀`-dilate of the dilated dual indicator. -/
theorem realFinitePolarDualLatticeIndicator_mul_det (L : PositiveDefiniteIntegralLattice n) (k₀ : ℕ)
    (xf : Fin n → RationalFiniteAdele) :
    realFinitePolarDualLatticeIndicator L
        (algebraMap ℚ RationalFiniteAdele (((k₀ * L.polarGramMatrix.det.natAbs : ℕ) : ℚ))⁻¹ • xf) =
      realDilatedPolarDualIndicator L (rationalFiniteAdeleCoordinateScale ((k₀ : ℚ))⁻¹ xf) := by
  unfold realDilatedPolarDualIndicator
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, rationalFiniteAdeleCoordinateScale, ← mul_assoc, ← map_mul]
  congr 2
  push_cast
  rw [mul_inv, mul_comm]
  rfl

/-- The rank-four dual shell density `ρ_Ψ(b) = [d²b ∈ ℤ] Re Â_α(b) · d² · Re Σ_a D_a(d²b)`. -/
def dualShellDensity (L : PositiveDefiniteIntegralLattice 4) (α : ℝ) (b : ℚ) : ℝ :=
  if ((L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * b).den = 1 then
    (𝓕 (L.polarArchimedeanBruhatFactor α) (b : ℝ)).re *
      ((L.polarGramMatrix.det.natAbs : ℝ) ^ 2 *
        (∑ a, L.dualClassTubeLimit a ((L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * b).num).re)
  else 0

set_option maxHeartbeats 2000000 in
/-- `D⁴` of the dilated dual test: at an integral point `z` of norm `(k₀ d)² b`, `D⁴_z(Ψ_α(·/k₀d)) = ρ_Ψ(b)`. -/
theorem rankFourDensityAt_dilatedDualTest (L : PositiveDefiniteIntegralLattice 4) {α : ℝ} (hα : 0 < α) {k₀ : ℕ}
    (hk₀ : k₀ ≠ 0) (z : Fin 4 → ℤ) (hz : L.quadForm z ≠ 0) {b : ℚ}
    (hb : (((k₀ * L.polarGramMatrix.det.natAbs : ℕ) : ℚ)) ^ 2 * b = L.quadForm z) :
    (rankFourDensityAt L (n := 3) le_rfl
        (w := α * (((k₀ * L.polarGramMatrix.det.natAbs : ℕ) : ℝ))⁻¹ ^ 2)
        (by have : (0 : ℝ) < ((k₀ * L.polarGramMatrix.det.natAbs : ℕ) : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hk₀ L.natAbs_det_ne_zero)
            positivity) z hz).toLinearMap
      (realGaussianCoreDilate L (mul_ne_zero hk₀ L.natAbs_det_ne_zero) (polarGaussianDualCore L α)) =
      dualShellDensity L α b := by
  classical
  set d : ℕ := L.polarGramMatrix.det.natAbs with hddef
  have hd0 : d ≠ 0 := L.natAbs_det_ne_zero
  set k : ℕ := k₀ * d with hkdef
  have hk : k ≠ 0 := mul_ne_zero hk₀ hd0
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
  have hsec : (fun xf ↦ (finiteSectionAverage L (fun i ↦ (z i : ℝ))
      (realGaussianCoreDilate L hk (polarGaussianDualCore L α)).val xf : ℂ)) =
      fun xf ↦ ((Real.exp (-(2 * Real.pi * α) * (b : ℝ)) : ℝ) : ℂ) *
        ((realDilatedPolarDualIndicator L (rationalFiniteAdeleCoordinateScale ((k₀ : ℚ))⁻¹ xf) : ℝ) : ℂ) := by
    funext xf
    rw [finiteSectionAverage_dilatedDualTest, hQz, realFinitePolarDualLatticeIndicator_mul_det]
    congr 3
    field_simp
  rw [rankFourDensityAt_apply]
  unfold rankFourFiniteDensity
  simp_rw [hsec, finiteTubeMass_const_mul]
  have hscalar : rationalAdeleRealScalar (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)))) =
      (k : ℝ) ^ 2 * (b : ℝ) := by
    rw [← hQz, realQuadraticFormValue_intVector_eq_realScalar]
    rfl
  have hcInf := re_realLocalValueDensity_gaussianOrbitTestRealFactor L
    (b := α * ((k : ℝ))⁻¹ ^ 2) (by positivity) (by norm_num) (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ))))
    (by rw [hscalar]; positivity)
  rw [hcInf, hscalar]
  have hcar : IsStandardCarried 1 (fun x ↦ ((realDilatedPolarDualIndicator L x : ℝ) : ℂ)) :=
    isStandardCarried_realDilatedPolarDualIndicator L
  have hper : IsStandardPeriodic d (fun x ↦ ((realDilatedPolarDualIndicator L x : ℝ) : ℂ)) :=
    isStandardPeriodic_realDilatedPolarDualIndicator L
  unfold dualShellDensity
  by_cases hden : ((d : ℚ) ^ 2 * b).den = 1
  · rw [if_pos hden]
    set M₀ : ℤ := ((d : ℚ) ^ 2 * b).num with hM₀def
    have hM₀ : (M₀ : ℚ) = (d : ℚ) ^ 2 * b := by
      have := Rat.num_div_den ((d : ℚ) ^ 2 * b)
      rw [hden, Nat.cast_one, div_one] at this
      exact this
    have hMz : L.quadForm z = (k₀ : ℤ) ^ 2 * M₀ := by
      have h : ((L.quadForm z : ℤ) : ℚ) = (((k₀ : ℤ) ^ 2 * M₀ : ℤ) : ℚ) := by
        rw [← hb, hkdef]
        push_cast
        rw [hM₀]
        ring
      exact_mod_cast h
    have hM₀0 : M₀ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hMz; exact hz hMz
    have hlim := (L.tendsto_finiteTubeMass_comp_scale_of_tendsto (n := 3) le_rfl hd0 hcar hper hk₀ hM₀0
      (L.tendsto_finiteTubeMass_realDilatedPolarDualIndicator hM₀0)).const_mul
      ((Real.exp (-(2 * Real.pi * α) * (b : ℝ)) : ℝ) : ℂ)
    rw [← hMz] at hlim
    rw [hlim.limUnder_eq]
    rw [fourier_polarArchimedeanBruhatFactor_of_pos L hα (by norm_num) (by exact_mod_cast hbpos),
      Complex.ofReal_re]
    set S : ℂ := ∑ a, L.dualClassTubeLimit a M₀ with hS
    have hre : (((Real.exp (-(2 * Real.pi * α) * (b : ℝ)) : ℝ) : ℂ) *
        ((k₀ : ℂ) ^ 2 / (k₀ : ℂ) ^ (3 + 1) * S)).re =
        Real.exp (-(2 * Real.pi * α) * (b : ℝ)) * ((k₀ : ℝ) ^ 2 / (k₀ : ℝ) ^ (3 + 1)) * S.re := by
      rw [show (k₀ : ℂ) ^ 2 / (k₀ : ℂ) ^ (3 + 1) = (((k₀ : ℝ) ^ 2 / (k₀ : ℝ) ^ (3 + 1) : ℝ) : ℂ) by
        push_cast; ring, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    rw [hre]
    have hk₀R : (k₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk₀
    have hg1 : ((((3 + 1 : ℕ)) : ℝ) / 2) = 2 := by norm_num
    simp only [hg1, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [hkdef]
    push_cast
    field_simp
    ring
  · rw [if_neg hden]
    have hbint : (d : ℚ) ^ 2 * b ∉ (algebraMap ℤ ℚ).range := by
      rintro ⟨m, hm⟩
      apply hden
      rw [← hm]
      simp
    have hb' : ((k₀ : ℚ)) ^ 2 * ((d : ℚ) ^ 2 * b) = L.quadForm z := by
      rw [← hb, hkdef]
      push_cast
      ring
    have hlim := (L.tendsto_finiteTubeMass_comp_scale_of_not_int (n := 3) le_rfl hd0 hcar hper hk₀ hz hb'
      hbint).const_mul ((Real.exp (-(2 * Real.pi * α) * (b : ℝ)) : ℝ) : ℂ)
    rw [mul_zero] at hlim
    rw [hlim.limUnder_eq, Complex.zero_re, mul_zero]

/-- The rank-four shell identity for the dual test at every shell:
`Θ_b(Ψ_α) · τ(Spin_L) = τ(Spin_{L_W}) · ofReal(ρ_Ψ(b))`. -/
theorem exists_complement_representedNormTheta_dualTest_mul_spinTamagawa_eq_rankFour
    (L : PositiveDefiniteIntegralLattice 4) (instA : Fintype L.ConcreteProperRationalDoubleCosetSet) {PA : ℝ}
    (hPA0 : 0 < PA) (hA : massLocalInverseProductTendsTo L PA) {α : ℝ} (hα : 0 < α)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm) :
    ∃ (x : Fin 4 → ℚ) (_ : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
      (LW : PositiveDefiniteIntegralLattice 3)
      (_ : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x))
      (instL : Fintype LW.ConcreteProperRationalDoubleCosetSet)
      (PL : ℝ) (hPL0 : 0 < PL) (hL : massLocalInverseProductTendsTo LW PL),
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          (by norm_num : 1 ≤ 2) instA hPA0 hA b
          (fun y ↦ ENNReal.ofReal ((polarGaussianDualCore L α).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice L (by norm_num) instA hPA0 hA).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice LW (by norm_num) instL hPL0 hL).spinTamagawaNumberENNReal *
        ENNReal.ofReal (dualShellDensity L α b.1) := by
  obtain ⟨x, hx⟩ := b.2.2
  obtain ⟨k₀, hk₀, z₀, hz₀⟩ := exists_nat_smul_integral x
  set d : ℕ := L.polarGramMatrix.det.natAbs with hddef
  have hd0 : d ≠ 0 := L.natAbs_det_ne_zero
  set k : ℕ := k₀ * d with hkdef
  have hk : k ≠ 0 := mul_ne_zero hk₀ hd0
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hw' : 0 < α * ((k : ℝ))⁻¹ ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  set z : Fin 4 → ℤ := (d : ℤ) • z₀ with hzdef
  have hz : (fun i ↦ (z i : ℚ)) = (k : ℚ) • x := by
    funext i
    have := congrFun hz₀ i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [hzdef, hkdef, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [this]
    ring
  have hzb : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) =
      (RepresentedNonzeroRationalNorm.dilate _ b hkq).1 := by
    rw [hz, QuadraticMap.map_smul, hx, smul_eq_mul, RepresentedNonzeroRationalNorm.dilate_coe]
    ring
  obtain ⟨hz0, LW, eW, instL, PL, hPL0, hL, h⟩ :=
    exists_complement_representedNormTheta_mul_spinTamagawa_eq_of_integral_rankFour (s := 1) L le_rfl
      instA hPA0 hA hw' (RepresentedNonzeroRationalNorm.dilate _ b hkq) z hzb
      (realGaussianCoreDilate L hk (polarGaussianDualCore L α))
      (fun y ↦ polarGaussianDualCore_nonneg L α _)
  refine ⟨fun i ↦ (z i : ℚ), by rw [hzb]; exact (RepresentedNonzeroRationalNorm.dilate _ b hkq).2.1,
    LW, eW, instL, PL, hPL0, hL, ?_⟩
  have htheta : L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      (by norm_num : 1 ≤ 2) instA hPA0 hA (RepresentedNonzeroRationalNorm.dilate _ b hkq)
      (fun y ↦ ENNReal.ofReal ((realGaussianCoreDilate L hk (polarGaussianDualCore L α)).val y))
      rationalIdeleClassUnitLogCutoff =
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
        (by norm_num : 1 ≤ 2) instA hPA0 hA b
        (fun y ↦ ENNReal.ofReal ((polarGaussianDualCore L α).val y)) rationalIdeleClassUnitLogCutoff := by
    unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    dsimp only
    rw [← L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_dilate
      b hkq (fun y ↦ ENNReal.ofReal ((polarGaussianDualCore L α).val y))]
    rfl
  have hbk : (((k₀ * d : ℕ) : ℚ)) ^ 2 * b.1 = L.quadForm z := by
    rw [← L.nativeRationalQuadraticForm_intVector z, hzb, RepresentedNonzeroRationalNorm.dilate_coe]
  rw [htheta, rankFourDensityAt_dilatedDualTest L hα hk₀ z hz0 hbk] at h
  exact h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
