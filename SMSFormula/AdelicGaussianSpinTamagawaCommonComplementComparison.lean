import SMSFormula.AdelicGaussianSpinTamagawaEisensteinComparison

/-!
# The theta–Eisenstein comparison with a common complement volume, in every rank `≥ 3`

The theta–Eisenstein assembly `spinTamagawaNumberENNReal_eq_one_of_shellIdentities` combines three
identities for the standard test at width `a` and the dual test at width `a⁻¹`
(`C = detScale⁻¹ (1/√a)^n`):

* Theta covariance: `τ_V + Σ_b Θ^c_b(Φ) = C (τ_V + Σ_b Θ^c_b(Ψ))` (every rank `≥ 3`);
* the shell identities `Θ^p_b · τ_V = ρ(b)`;
* the Eisenstein aggregate `1 + Σ_b ρ_Φ(b) = C (1 + Σ_b ρ_Ψ(b))`.

Only the last two use rank `≥ 5`: the Fourier densities are summable, every positive rational is
represented, and the aggregate is the rank-five Eisenstein identity. The subtraction itself does not
depend on the rank.

This file states the subtraction in every rank `≥ 3` with the shell densities `ρ_Φ, ρ_Ψ` supplied
(nonnegative, summable over the represented nonzero norms), the aggregate supplied, and a common
complement factor `t`:

`Θ^p_b · τ_V = t · ρ(b)` for every shell and both tests, with the aggregate, gives `τ_V = t`.

With `t = 1` this is the theta–Eisenstein comparison. For the quaternion norm space `U = (D, Nrd)`
of a positive definite ternary space `T` (`D = C⁺(T)`), every nonzero shell has Spin stabilizer
`SL₁(D) ≅ Spin(T)`, so `t = τ(Spin_T)`, while `τ(Spin_U) = t²`; then `t² = t` gives `t = 1`
(`eq_one_of_commonComplementShellIdentities_of_eq_mul_self`). Neither the quaternion bridge
`τ(Spin_U) = t²` nor any rank-four aggregate is asserted here: both are supplied hypotheses.

In rank `≥ 5` the supplied data are discharged by the Fourier densities and the Eisenstein
aggregate (`spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities_of_five_le`).
Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

/-- A finite nonzero extended real equal to its own square is one. -/
theorem ENNReal.eq_one_of_mul_self_eq_self {t : ℝ≥0∞} (h0 : t ≠ 0) (htop : t ≠ ⊤)
    (h : t * t = t) : t = 1 := by
  have h' : t * t = t * 1 := by rw [mul_one, h]
  exact (ENNReal.mul_right_inj h0 htop).1 h'

/-- The theta–Eisenstein comparison with a common complement volume, in every rank `≥ 3`.  Given
nonnegative summable shell densities `ρ_Φ, ρ_Ψ` on the represented nonzero rational norms, the
supplied shell identities `Θ^p_b · τ_V = t · ρ(b)` for the standard test at width `a` and the
dual test at width `a⁻¹`, and the supplied aggregate `1 + Σ ρ_Φ = C (1 + Σ ρ_Ψ)` with `C ≠ 1`,
the intrinsic Spin quantity equals `t`. -/
theorem spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (ρΦ ρΨ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ)
    (hρΦnn : ∀ b, 0 ≤ ρΦ b) (hρΨnn : ∀ b, 0 ≤ ρΨ b)
    (hsumρΦ : Summable ρΦ) (hsumρΨ : Summable ρΨ)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (ρΦ b))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (ρΨ b))
    (hE : 1 + ∑' b, ρΦ b =
      (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) *
        (1 + ∑' b, ρΨ b)) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = t := by
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
  have hΦE : rationalAdeleVectorPolarGaussianLatticeTestENNReal L a =
      fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y) :=
    funext (IntegralFiniteAdelePhase.rationalAdeleVectorPolarGaussianLatticeTestENNReal_eq_ofReal L a)
  have hΨE : rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹ =
      fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y) :=
    funext (IntegralFiniteAdelePhase.rationalAdeleVectorPolarGaussianDualTestENNReal_eq_ofReal L a⁻¹)
  have hcutΦ : ∀ b, L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv b (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
      rationalIdeleClassUnitLogCutoff = t * ENNReal.ofReal (ρΦ b) := by
    intro b
    rw [hΦE, ← L.probabilityNormalizedRepresentedNormTheta_mul_spinTamagawa_eq_cutoffNormalized hr
      inst hP hconv hτtop b _ _ rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top, hΦ b]
  have hcutΨ : ∀ b, L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv b (rationalAdeleVectorPolarGaussianDualTestENNReal L a⁻¹)
      rationalIdeleClassUnitLogCutoff = t * ENNReal.ofReal (ρΨ b) := by
    intro b
    rw [hΨE, ← L.probabilityNormalizedRepresentedNormTheta_mul_spinTamagawa_eq_cutoffNormalized hr
      inst hP hconv hτtop b _ _ rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top, hΨ b]
  -- Theta covariance
  have hcov := L.spinTamagawaNumberENNReal_add_representedNorm_standard_eq_const_mul_dual hr inst
    hP hconv ha
  simp only [hcutΦ, hcutΨ, ENNReal.tsum_mul_left] at hcov
  rw [← hτdef, ← hCdef] at hcov
  rw [← ENNReal.ofReal_tsum_of_nonneg hρΦnn hsumρΦ,
    ← ENNReal.ofReal_tsum_of_nonneg hρΨnn hsumρΨ] at hcov
  set X := ∑' b, ρΦ b with hXdef
  set Y := ∑' b, ρΨ b with hYdef
  have hX : 0 ≤ X := tsum_nonneg hρΦnn
  have hY : 0 ≤ Y := tsum_nonneg hρΨnn
  -- the real comparison
  have hτr := ENNReal.ofReal_toReal hτtop
  have htr := ENNReal.ofReal_toReal ht
  rw [← hτr, ← htr, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ← ENNReal.ofReal_mul hCpos.le,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at hcov
  have hEt : t.toReal * (1 + X) = t.toReal * (C * (1 + Y)) := by rw [hE]
  have hfinal : (τ.toReal - t.toReal) * (1 - C) = 0 := by linear_combination hcov - hEt
  rcases mul_eq_zero.1 hfinal with h | h
  · rw [← hτr, ← htr, show τ.toReal = t.toReal by linarith]
  · exact absurd (by linarith : C = 1) hC

/-- The quaternion bootstrap, algebraic form. If the shell identities of
`spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities` hold with a common nonzero finite
complement factor `t`, the aggregate holds, and `τ_V = t · t`, then `t = 1` (and hence `τ_V = 1`).

For the quaternion norm space of a positive definite ternary space `T`, `t = τ(Spin_T)` and
`τ_V = t²` are the supplied Clifford/measure bridge; nothing here proves them. -/
theorem eq_one_of_commonComplementShellIdentities_of_eq_mul_self
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    {t : ℝ≥0∞} (ht0 : t ≠ 0) (ht : t ≠ ⊤)
    (ρΦ ρΨ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ)
    (hρΦnn : ∀ b, 0 ≤ ρΦ b) (hρΨnn : ∀ b, 0 ≤ ρΨ b)
    (hsumρΦ : Summable ρΦ) (hsumρΨ : Summable ρΨ)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (ρΦ b))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (ρΨ b))
    (hE : 1 + ∑' b, ρΦ b =
      (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) *
        (1 + ∑' b, ρΨ b))
    (hsq : (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = t * t) :
    t = 1 := by
  have h := L.spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities hr inst hP hconv ha hC
    ht ρΦ ρΨ hρΦnn hρΨnn hsumρΦ hsumρΨ hΦ hΨ hE
  exact ENNReal.eq_one_of_mul_self_eq_self ht0 ht (hsq.symm.trans h)

/-! ## Rank `≥ 5`: the supplied data are proved -/

/-- In rank `≥ 5`, the Fourier value densities are nonnegative and summable over the represented
nonzero norms, and satisfy the aggregate over them (Eisenstein aggregate, Hasse--Minkowski
in rank `≥ 5`, archimedean vanishing at nonpositive values). -/
theorem realValueDensity_polarGaussianCore_aggregate_of_five_le
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) (hrank : 5 ≤ r + 2) {a : ℝ} (ha : 0 < a) :
    (∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        0 ≤ L.rationalQuadraticSpaceMatrix.realValueDensity
          (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
          (algebraMap ℚ RationalAdele b.1)) ∧
      (∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        0 ≤ L.rationalQuadraticSpaceMatrix.realValueDensity
          (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
          (algebraMap ℚ RationalAdele b.1)) ∧
      Summable (fun b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm ↦
        L.rationalQuadraticSpaceMatrix.realValueDensity
          (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
          (algebraMap ℚ RationalAdele b.1)) ∧
      Summable (fun b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm ↦
        L.rationalQuadraticSpaceMatrix.realValueDensity
          (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
          (algebraMap ℚ RationalAdele b.1)) ∧
      1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.rationalQuadraticSpaceMatrix.realValueDensity
            (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
            (algebraMap ℚ RationalAdele b.1) =
        (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) *
          (1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
            L.rationalQuadraticSpaceMatrix.realValueDensity
              (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
              (algebraMap ℚ RationalAdele b.1)) := by
  have hn3 : 3 ≤ r + 2 := by omega
  set ρΦ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ := fun b ↦
    L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val (algebraMap ℚ RationalAdele b.1)
    with hρΦdef
  set ρΨ : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℝ := fun b ↦
    L.rationalQuadraticSpaceMatrix.realValueDensity
      (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val (algebraMap ℚ RationalAdele b.1)
    with hρΨdef
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
  refine ⟨hρΦnn, hρΨnn, hsumρΦ, hsumρΨ, ?_⟩
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
  set C : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) with hCdef
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
  exact hEre

/-- The common-complement comparison in rank `≥ 5`: shell identities `Θ^p_b · τ_V = t · ρ(b)` with the
Fourier value densities give `τ_V = t`.  With `t = 1` this is
`spinTamagawaNumberENNReal_eq_one_of_shellIdentities`. -/
theorem spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities_of_five_le
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      t * ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = t := by
  obtain ⟨hΦnn, hΨnn, hsumΦ, hsumΨ, hE⟩ :=
    L.realValueDensity_polarGaussianCore_aggregate_of_five_le hrank ha
  exact L.spinTamagawaNumberENNReal_eq_of_commonComplementShellIdentities hr inst hP hconv ha hC ht
    _ _ hΦnn hΨnn hsumΦ hsumΨ hΦ hΨ hE

end PositiveDefiniteIntegralLattice
