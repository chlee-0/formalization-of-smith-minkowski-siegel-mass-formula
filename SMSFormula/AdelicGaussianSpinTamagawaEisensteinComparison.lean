import SMSFormula.RationalAdeleRankOneEisensteinDualPoisson
import SMSFormula.RationalAdeleCutoffNormalizedDualFunctionalEquation
import SMSFormula.AdelicGaussianPolarShellDensity
import SMSFormula.AdelicGaussianTracePositivity
import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedThetaReal
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeCutoffFinite
import SMSFormula.RationalWeakApproximation
import SMSFormula.RationalPadicHighRankIsotropy
import SMSFormula.RationalDyadicHighRankIsotropy
import SMSFormula.RationalAdeleStandardThetaShellGap

/-!
# `τ(Spin_V) = 1` from the shell identities and the Eisenstein aggregates

Three identities meet here, for the standard test at width `a` and the dual test at width `a⁻¹`
(`C = detScale⁻¹ (1/√a)^n`):

* Theta covariance (cutoff-normalized): `τ_V + Σ_b Θ^c_b(Φ) = C (τ_V + Σ_b Θ^c_b(Ψ))`;
* the shell identities `Θ^p_b · τ_V = ofReal ρ(b)` for every represented nonzero rational norm
  `b` and both tests (the complement identity at an integral representative together with
  `τ(Spin_{W_b}) = 1`; supplied here as hypotheses),
  where `Θ^p = Θ^c / τ_V` is the probability normalization;
* the Eisenstein aggregate (proved in this library): `1 + Σ_{b∈ℚ} d_Φ(b) = C (1 + Σ_{b∈ℚ} d_Ψ(b))`.

Positive definiteness kills `d(b)` for `b ≤ 0` (archimedean factor), and Hasse--Minkowski (the
local-global representation theorem, `p`-adic isotropy in rank at least five) shows every positive
rational is a represented norm, so both sums run over the same index. Subtracting gives
`(τ_V - 1)(1 - C) = 0`, hence `τ_V = 1` whenever `C ≠ 1`. `τ_V` is finite (the cutoff-normalized
standard theta is finite and contains `τ_V · Φ(0)`); `τ(SO) = 2` is not used.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped FourierTransform ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Every positive rational is a represented norm (Hasse--Minkowski) -/

theorem nativeRationalQuadraticForm_eq_gramQuadraticValue (L : PositiveDefiniteIntegralLattice n)
    (x : Fin n → ℚ) :
    L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x =
      gramQuadraticValue L.rationalQuadraticSpaceMatrix.pairingMatrix x := by
  simp [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
    RationalQuadraticSpaceMatrix.quadraticForm, Matrix.toQuadraticMap', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', gramQuadraticValue, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_comm]

/-- Hasse--MINKOWSKI for positive norms: a positive definite integral lattice of rank at least
five represents every positive rational over `ℚ`. -/
theorem exists_nativeRationalQuadraticForm_eq_of_pos (L : PositiveDefiniteIntegralLattice n) (hn : 5 ≤ n)
    {b : ℚ} (hb : 0 < b) :
    ∃ x : Fin n → ℚ, L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = b := by
  set A := L.rationalQuadraticSpaceMatrix.pairingMatrix with hAdef
  have hA_symm : A.IsSymm := L.rationalQuadraticSpaceMatrix.form_symm
  have hA_det : A.det ≠ 0 := L.rationalQuadraticSpaceMatrix.form_det_ne_zero
  have hreal : ∃ v : Fin n → ℝ,
      gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v = (b : ℝ) := by
    haveI : NeZero n := ⟨by omega⟩
    have hmap : A.map (algebraMap ℚ ℝ) = L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
      ext i j
      simp [hAdef, rationalQuadraticSpaceMatrix_pairingMatrix, PositiveDefiniteIntegralLattice.rationalFormMatrix]
    set v₀ : Fin n → ℝ := Pi.single 0 1 with hv₀
    have hq₀ : 0 < gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀ := by
      have hval : gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀ = (A.map (algebraMap ℚ ℝ)) 0 0 := by
        simp [hv₀, gramQuadraticValue, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hval, hmap]
      exact L.form_posDef.diag_pos
    refine ⟨Real.sqrt ((b : ℝ) / gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v₀) • v₀, ?_⟩
    rw [gramQuadraticValue_smul_vector, Real.sq_sqrt (div_nonneg (by exact_mod_cast hb.le) hq₀.le), div_mul_cancel₀ _ hq₀.ne']
  have hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ v : Fin n → ℚ_[p],
      gramQuadraticValue (A.map (algebraMap ℚ ℚ_[p])) v = (b : ℚ_[p]) := by
    intro p hp
    have hiso : GramIsotropic (A.map (algebraMap ℚ ℚ_[p])) := by
      by_cases h2 : p = 2
      · subst h2
        exact gramIsotropic_dyadic_of_rat_of_five_le hn A hA_symm hA_det
      · exact gramIsotropic_padic_of_rat_of_five_le h2 hn A hA_symm hA_det
    have hdet : (A.map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hA_det
    have hchar : ringChar ℚ_[p] ≠ 2 := by
      rw [ringChar.eq_zero]
      norm_num
    exact exists_gramQuadraticValue_eq_of_gramIsotropic _ (hA_symm.map _) hdet hchar hiso _
  obtain ⟨x, hx⟩ := Rat.exists_gramQuadraticValue_eq_rat_of_real_and_padic (by omega) A hA_symm
    hA_det b hb.ne' hreal hpadic
  exact ⟨x, (L.nativeRationalQuadraticForm_eq_gramQuadraticValue x).trans hx⟩

/-- Every positive rational is a represented nonzero rational norm (rank at least five). -/
theorem mem_representedNonzeroRationalNorm_of_pos (L : PositiveDefiniteIntegralLattice n) (hn : 5 ≤ n) {b : ℚ}
    (hb : 0 < b) :
    b ≠ 0 ∧ ∃ x : Fin n → ℚ, L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = b :=
  ⟨hb.ne', L.exists_nativeRationalQuadraticForm_eq_of_pos hn hb⟩

/-! ## Vanishing of the value densities at nonpositive values -/

theorem archimedeanLocal_neg_eq_fourier (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (b : ℚ) :
    (∫ w : RationalInfiniteAdele,
        ((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele (-b) * w) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / ((c : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)
        ∂rationalInfiniteAdeleAddHaarMeasure) =
      𝓕 (L.polarArchimedeanBruhatFactor c) (b : ℝ) := by
  rw [integral_archimedeanLocal_eq_real, fourier_polarArchimedeanBruhatFactor_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  push_cast
  rfl

/-- The standard value density vanishes at every nonpositive rational value. -/
theorem complexValueFourierDensity_polarGaussianLattice_eq_zero_of_nonpos (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hn : 3 ≤ n) {b : ℚ} (hb : b ≤ 0) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ)) (algebraMap ℚ RationalAdele b) = 0 := by
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_eq_real_mul_finite (by simpa using hc) (-b),
    archimedeanLocal_neg_eq_fourier,
    L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn (by exact_mod_cast hb), zero_mul]

/-- The dual value density vanishes at every nonpositive rational value. -/
theorem complexValueFourierDensity_polarGaussianDual_eq_zero_of_nonpos (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hn : 3 ≤ n) {b : ℚ} (hb : b ≤ 0) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b) = 0 := by
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_polarGaussianDual_eq_real_mul_finite
      (by simpa using hc) (-b),
    archimedeanLocal_neg_eq_fourier,
    L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn (by exact_mod_cast hb), zero_mul]

/-! ## The comparison -/

theorem ENNReal.div_mul_mul_cancel_right_of_ne {x m τ : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ⊤)
    (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) : x / (m * τ) * τ = x / m := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hm0) (Or.inl hmtop), mul_assoc,
    mul_assoc, ENNReal.inv_mul_cancel hτ0 hτtop, mul_one]

/-- The two normalizations of one represented-norm shell differ exactly by `τ_V`. -/
theorem probabilityNormalizedRepresentedNormTheta_mul_spinTamagawa_eq_cutoffNormalized
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    (hτtop : (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal ≠ ⊤)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hf0 : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hftop : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
        Phi f *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b Phi f := by
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
    cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
  dsimp only
  exact ENNReal.div_mul_mul_cancel_right_of_ne hf0 hftop
    (RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal_ne_zero
      _) hτtop

/-- The finiteness of the intrinsic Spin quantity, without `τ(SO) = 2`: the
cutoff-normalized standard theta is finite and contains `τ_V · Φ(0) = τ_V`. -/
theorem spinTamagawaNumberENNReal_ne_top_of_standardTheta
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal ≠ ⊤ := by
  obtain ⟨h1, -⟩ := L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_terms_ne_top hr inst hP
    hconv (rationalAdeleVectorPolarGaussianLatticeTestENNReal L 1)
    (L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal 1)
    rationalIdeleClassUnitLogCutoff measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero rationalIdeleClassLogCutoffLIntegral_unit_ne_top
    (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top hr inst hP
      hconv one_pos)
  have h0 : rationalAdeleVectorPolarGaussianLatticeTestENNReal L 1 0 = 1 := by
    simp [rationalAdeleVectorPolarGaussianLatticeTestENNReal,
      rationalAdeleVectorPolarGaussianLatticeTest_zero]
  rwa [h0, mul_one] at h1

/-- The theta–Eisenstein comparison: `τ(Spin_V) = 1` from the shell identities.  For an integral
lattice of rank at least five, a width `a > 0` with `C = detScale⁻¹ (1/√a)^n ≠ 1`, and the
supplied shell identities `Θ^p_b · τ_V = ofReal ρ(b)` for every represented nonzero rational norm
and both tests (the standard test at width `a` and the dual-carrier test at width `a⁻¹`) -- i.e.
the complement identity at an integral representative together with `τ(Spin_{W_b}) = 1` -- the
intrinsic Spin quantity is one.  `τ(SO) = 2` is not used. -/
theorem spinTamagawaNumberENNReal_eq_one_of_shellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  have hn3 : 3 ≤ r + 2 := by omega
  set τ := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hP hconv).spinTamagawaNumberENNReal with hτdef
  set C : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) with hCdef
  have hCpos : 0 < C := by
    have hdet : 0 < (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_pos.2 L.polarRealDeterminantScale_pos
    have : 0 < a ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
    positivity
  have hτtop : τ ≠ ⊤ := L.spinTamagawaNumberENNReal_ne_top_of_standardTheta hr inst hP hconv
  -- the shell identities in cutoff normalization
  set ρΦ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ := fun b ↦
    L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val (algebraMap ℚ RationalAdele b.1)
    with hρΦdef
  set ρΨ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ := fun b ↦
    L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val (algebraMap ℚ RationalAdele b.1)
    with hρΨdef
  have hΦE : rationalAdeleVectorPolarGaussianLatticeTestENNReal L a =
      fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y) :=
    funext (IntegralFiniteAdelePhase.rationalAdeleVectorPolarGaussianLatticeTestENNReal_eq_ofReal L a)
  have hΨE : rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹ =
      fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y) :=
    funext (IntegralFiniteAdelePhase.rationalAdeleVectorPolarGaussianDualTestENNReal_eq_ofReal L a⁻¹)
  have hcutΦ : ∀ b, L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv b (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
      rationalIdeleClassUnitLogCutoff = ENNReal.ofReal (ρΦ b) := by
    intro b
    rw [hΦE, ← L.probabilityNormalizedRepresentedNormTheta_mul_spinTamagawa_eq_cutoffNormalized hr
      inst hP hconv hτtop b _ _ rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top, hΦ b]
  have hcutΨ : ∀ b, L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv b (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹)
      rationalIdeleClassUnitLogCutoff = ENNReal.ofReal (ρΨ b) := by
    intro b
    rw [hΨE, ← L.probabilityNormalizedRepresentedNormTheta_mul_spinTamagawa_eq_cutoffNormalized hr
      inst hP hconv hτtop b _ _ rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top, hΨ b]
  -- Theta covariance
  have hcov := L.spinTamagawaNumberENNReal_add_representedNorm_standard_eq_const_mul_dual hr inst
    hP hconv ha
  simp only [hcutΦ, hcutΨ] at hcov
  rw [← hτdef, ← hCdef] at hcov
  -- nonnegativity and summability of the shell densities
  have hρΦnn : ∀ b, 0 ≤ ρΦ b := fun b ↦
    IntegralFiniteAdelePhase.realValueDensity_nonneg_of_trace_nonneg L (by omega) ha
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).property _
      (fun x _ ↦ IntegralFiniteAdelePhase.polarGaussianLatticeCore_nonneg L a x)
  have hρΨnn : ∀ b, 0 ≤ ρΨ b := fun b ↦
    IntegralFiniteAdelePhase.realValueDensity_nonneg_of_trace_nonneg L (by omega) (inv_pos.2 ha)
      (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).property _
      (fun x _ ↦ IntegralFiniteAdelePhase.polarGaussianDualCore_nonneg L a⁻¹ x)
  have hdΦ := L.summable_norm_complexValueFourierDensity_polarGaussianLattice ha hrank
  have hdΨ := L.summable_norm_complexValueFourierDensity_polarGaussianDual (inv_pos.2 ha) hrank
  have hρΦeq : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      ρΦ b = (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
        (algebraMap ℚ RationalAdele b.1)).re := fun b ↦
    IntegralFiniteAdelePhase.realValueDensity_polarGaussianLatticeCore L a _
  have hρΨeq : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      ρΨ b = (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L ((a⁻¹ : ℝ) : ℂ))
        (algebraMap ℚ RationalAdele b.1)).re := fun b ↦
    IntegralFiniteAdelePhase.realValueDensity_polarGaussianDualCore L a⁻¹ _
  have hsumρΦ : Summable ρΦ := by
    refine Summable.of_nonneg_of_le hρΦnn (fun b ↦ ?_)
      (hdΦ.comp_injective Subtype.val_injective)
    rw [hρΦeq]
    exact Complex.re_le_norm _
  have hsumρΨ : Summable ρΨ := by
    refine Summable.of_nonneg_of_le hρΨnn (fun b ↦ ?_)
      (hdΨ.comp_injective Subtype.val_injective)
    rw [hρΨeq]
    exact Complex.re_le_norm _
  rw [← ENNReal.ofReal_tsum_of_nonneg hρΦnn hsumρΦ,
    ← ENNReal.ofReal_tsum_of_nonneg hρΨnn hsumρΨ] at hcov
  set X := ∑' b, ρΦ b with hXdef
  set Y := ∑' b, ρΨ b with hYdef
  have hX : 0 ≤ X := tsum_nonneg hρΦnn
  have hY : 0 ≤ Y := tsum_nonneg hρΨnn
  -- the Eisenstein side, over the represented norms
  have hsupp : ∀ {D : ℚ → ℂ}, (∀ b : ℚ, b ≤ 0 → D b = 0) →
      (∑' b : ℚ, (D b).re) =
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm, (D b.1).re := by
    intro D hD
    have hs : Function.support (fun b : ℚ ↦ (D b).re) ⊆
        {b : ℚ | b ≠ 0 ∧ ∃ x : Fin (r + 2) → ℚ,
          L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = b} := by
      intro b hb
      by_contra hnot
      have hpos : ¬ 0 < b := fun hpos ↦ hnot (L.mem_representedNonzeroRationalNorm_of_pos hrank hpos)
      exact hb (show (D b).re = 0 by rw [hD b (not_lt.1 hpos), Complex.zero_re])
    exact (tsum_subtype_eq_of_support_subset hs).symm
  have hE := L.polarGaussianLattice_aggregate_eq_const_mul_dual_aggregate (inv_pos.2 ha) hrank
  simp only [inv_inv, rationalAdeleVectorPolarGaussianLatticeTest_zero,
    rationalAdeleVectorPolarGaussianDualTest_zero] at hE
  have hC' : ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / (a : ℂ) ^ (1 / 2 : ℂ)) ^ (r + 2)) =
      ((C : ℝ) : ℂ) := by
    rw [hCdef]
    push_cast
    rw [Complex.ofReal_cpow ha.le]
    norm_num
  rw [hC'] at hE
  have hEre := congrArg Complex.re hE
  rw [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re,
    Complex.re_tsum hdΦ.of_norm, Complex.re_tsum hdΨ.of_norm,
    hsupp (fun b hb ↦ L.complexValueFourierDensity_polarGaussianLattice_eq_zero_of_nonpos ha hn3 hb),
    hsupp (fun b hb ↦ L.complexValueFourierDensity_polarGaussianDual_eq_zero_of_nonpos
      (inv_pos.2 ha) hn3 hb)] at hEre
  simp only [← hρΦeq, ← hρΨeq] at hEre
  rw [← hXdef, ← hYdef] at hEre
  -- the real comparison
  have ht := ENNReal.ofReal_toReal hτtop
  rw [← ht, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hX,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hY, ← ENNReal.ofReal_mul hCpos.le,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at hcov
  have hfinal : (τ.toReal - 1) * (1 - C) = 0 := by linarith
  rcases mul_eq_zero.1 hfinal with h | h
  · rw [← ht, show τ.toReal = 1 by linarith, ENNReal.ofReal_one]
  · exact absurd (by linarith : C = 1) hC

/-- Width-free form: if the shell identities hold at every width, then `τ(Spin_V) = 1` (one of the
widths `1, 4` has `C ≠ 1`, since `C(4) = C(1) · 2^{-n}`). -/
theorem spinTamagawaNumberENNReal_eq_one_of_forall_shellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    (hΦ : ∀ a : ℝ, 0 < a → ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ a : ℝ, 0 < a → ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  by_cases h1 : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / (1 : ℝ) ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1
  · exact L.spinTamagawaNumberENNReal_eq_one_of_shellIdentities hr hrank inst hP hconv one_pos h1
      (hΦ 1 one_pos) (hΨ 1 one_pos)
  · push_neg at h1
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    refine L.spinTamagawaNumberENNReal_eq_one_of_shellIdentities hr hrank inst hP hconv
      (by norm_num : (0 : ℝ) < 4) ?_ (hΦ 4 (by norm_num)) (hΨ 4 (by norm_num))
    rw [Real.one_rpow, div_one, one_pow, mul_one] at h1
    rw [h4, h1, one_mul]
    intro h
    have hlt : (1 / 2 : ℝ) ^ (r + 2) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith

/-! ## Non-integral shells of the standard test -/

/-- The standard-core shell theta vanishes identically at a non-integral norm: a nonzero test value
forces an integral finite part, hence an integral norm (GSpin acts through SO, so the norm is kept). -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormTheta_polarGaussianLatticeCore_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hb : b.1 ∉ (algebraMap ℤ ℚ).range)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormTheta b
      (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y)) g = 0 := by
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  refine ENNReal.tsum_eq_zero.2 fun x ↦ ?_
  unfold fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
  by_contra hne
  have htest : rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1) ≠ 0 := by
    intro h0
    apply hne
    rw [← IntegralFiniteAdelePhase.coe_polarGaussianLatticeCore, Complex.ofReal_eq_zero] at h0
    show ENNReal.ofReal _ = 0
    rw [h0, ENNReal.ofReal_zero]
  obtain ⟨k, hk⟩ := RationalQuadraticSpaceMatrix.rational_shell_integer_of_finitePart_integral L _ _
    (RationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue_generalSpinRationalAction _ g x.1)
    (RationalQuadraticSpaceMatrix.standardTest_ne_zero_finitePart_integral L _ _ htest)
  exact hb ⟨k, by rw [← x.2]; exact hk⟩

/-- At a non-integral norm the standard-core probability-normalized shell is zero. -/
theorem probabilityNormalizedRepresentedNormTheta_polarGaussianLatticeCore_eq_zero
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) (a : ℝ)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hb : b.1 ∉ (algebraMap ℤ ℚ).range) (f : ℝ → ℝ≥0∞) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
      (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y)) f = 0 := by
  have hquot : L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient b
      (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y)) = 0 := by
    funext Z
    induction Z using Quot.ind with
    | mk g =>
      exact L.fullAdelicCliffordGeneralSpinRepresentedNormTheta_polarGaussianLatticeCore_eq_zero a b hb g
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
    fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
  dsimp only
  rw [hquot, MeasureTheory.withDensity_zero, MeasureTheory.lintegral_zero_measure, mul_zero,
    ENNReal.zero_div]

/-- The standard-core shell identity holds trivially at every non-integral norm (both sides are
zero), so for the standard test only integral norms need the complement identity. -/
theorem shellIdentity_polarGaussianLatticeCore_of_not_int
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) {a : ℝ}
    (ha : 0 < a) (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hb : b.1 ∉ (algebraMap ℤ ℚ).range) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
        (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
        rationalIdeleClassUnitLogCutoff *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
    ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
      (algebraMap ℚ RationalAdele b.1)) := by
  rw [L.probabilityNormalizedRepresentedNormTheta_polarGaussianLatticeCore_eq_zero hr inst hP hconv a
      b hb, zero_mul, IntegralFiniteAdelePhase.realValueDensity_polarGaussianLatticeCore,
    L.complexValueFourierDensity_polarGaussianLattice_eq_zero_of_not_int ha hb, Complex.zero_re,
    ENNReal.ofReal_zero]

/-! ## Shells of the dual test off `N⁻¹ ℤ` -/

/-- The dual-core shell theta vanishes identically unless `N b ∈ ℤ` (`N = |polarDeterminant L|²`): a nonzero test
value forces a finite part in the polar dual lattice, where `D² Q ∈ Ẑ`. -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormTheta_polarGaussianDualCore_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hb : b.1 * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormTheta b
      (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a).val y)) g = 0 := by
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  refine ENNReal.tsum_eq_zero.2 fun x ↦ ?_
  unfold fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
  set y := L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1
    with hydef
  by_contra hne
  have htest : rationalAdeleVectorPolarGaussianDualTest L (a : ℂ) y ≠ 0 := by
    intro h0
    apply hne
    rw [← IntegralFiniteAdelePhase.coe_polarGaussianDualCore, Complex.ofReal_eq_zero] at h0
    show ENNReal.ofReal _ = 0
    rw [h0, ENNReal.ofReal_zero]
  have hmem : rationalAdeleVectorFinitePart n y ∈
      L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
    by_contra hnot
    apply htest
    rw [rationalAdeleVectorPolarGaussianDualTest,
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hnot, mul_zero]
  have hint := RationalQuadraticSpaceMatrix.polarDeterminant_sq_mul_finiteAdelicQuadraticFormValue_mem_integral L hmem
  have hvalue : L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (rationalAdeleVectorFinitePart n y) = algebraMap ℚ RationalFiniteAdele b.1 := by
    rw [← RationalQuadraticSpaceMatrix.rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue,
      hydef, RationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue_generalSpinRationalAction, x.2]
    rfl
  rw [hvalue, ← map_natCast (algebraMap ℚ RationalFiniteAdele), ← map_mul] at hint
  refine hb ?_
  rw [mul_comm]
  exact (rational_mem_integralFiniteAdeleSubring_iff _).1 hint

/-- The dual-core shell identity holds trivially unless `N b ∈ ℤ` (both sides are zero). -/
theorem shellIdentity_polarGaussianDualCore_of_not_int
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P) {a : ℝ}
    (ha : 0 < a) (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (hb : b.1 * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
        (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a).val y))
        rationalIdeleClassUnitLogCutoff *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
    ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianDualCore L a).val
      (algebraMap ℚ RationalAdele b.1)) := by
  have hquot : L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient b
      (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a).val y)) = 0 := by
    funext Z
    induction Z using Quot.ind with
    | mk g =>
      exact L.fullAdelicCliffordGeneralSpinRepresentedNormTheta_polarGaussianDualCore_eq_zero a b hb g
  have hzero : L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv b (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a).val y))
      rationalIdeleClassUnitLogCutoff = 0 := by
    unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    dsimp only
    rw [hquot, MeasureTheory.withDensity_zero, MeasureTheory.lintegral_zero_measure, mul_zero,
      ENNReal.zero_div]
  rw [hzero, zero_mul, IntegralFiniteAdelePhase.realValueDensity_polarGaussianDualCore,
    L.complexValueFourierDensity_polarGaussianDual_eq_zero_of_not_int ha hb, Complex.zero_re,
    ENNReal.ofReal_zero]

/-- The theta–Eisenstein comparison on the supported shells only: the shell identities are needed
only at integral norms for the standard test and at norms in `N⁻¹ ℤ` for the dual test; all other
shells vanish on both sides. -/
theorem spinTamagawaNumberENNReal_eq_one_of_supportedShellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 * (L.dualGaussPeriod : ℚ) ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  refine L.spinTamagawaNumberENNReal_eq_one_of_shellIdentities hr hrank inst hP hconv ha hC
    (fun b ↦ ?_) (fun b ↦ ?_)
  · by_cases hb : b.1 ∈ (algebraMap ℤ ℚ).range
    · exact hΦ b hb
    · exact L.shellIdentity_polarGaussianLatticeCore_of_not_int hr inst hP hconv ha b hb
  · by_cases hb : b.1 * (L.dualGaussPeriod : ℚ) ∈ (algebraMap ℤ ℚ).range
    · exact hΨ b hb
    · exact L.shellIdentity_polarGaussianDualCore_of_not_int hr inst hP hconv (inv_pos.2 ha) b hb

end PositiveDefiniteIntegralLattice
