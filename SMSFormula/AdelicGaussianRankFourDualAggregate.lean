import SMSFormula.AdelicGaussianRankFourDualShell
import SMSFormula.AdelicGaussianRankFourLatticeAggregate
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The dual-side aggregate of the rank-four shell densities and the aggregate identity `hE`

For the rank-four dual shell density `ρ_Ψ = dualShellDensity L (1/a)` of the dual-test shell identity
`exists_complement_representedNormTheta_dualTest_mul_spinTamagawa_eq_rankFour`:

* the class tube limits are real, nonnegative and at most the singular series (`dualClassTubeLimit_real_nonneg_le`:
  class tube masses are dominated by the standard ones), so `ρ_Ψ ≥ 0` and `ρ_Ψ` vanishes off the represented norms
  (rank-four `tprod_localResidueDensity_eq_zero_of_not_represented`);
* per discriminant class `[u]`, reindexing `b = (q(adj(S)u) + d²λ)/d²`, the class part of `ρ_Ψ` is the row
  `q`-expansion of the boundary row limit: `Σ_λ Â_{1/a}(λ + q(ν_u)) ∏'δ^{cos}_p(u, λ) = E_row(i/a)_{[u]} − e₀[u]`
  (`boundaryRowLimit_apply`, `gaussRowCoefficient_eq_cosetGRCoeff`, `hasSum_cosetGRCoeff`, `summable_rowMajorant`);
* hence `1 + Σ_b ρ_Ψ(b) = Σ_ν E_row(i/a)_ν` (`dualShellDensity_aggregate`), and with the lattice side
  `1 + Σ_b ρ_Φ(b) = E_std(a)` and the reciprocity (8.2) `E_std(a) = a⁻² κ Σ_ν E_row(i/a)_ν`:
  the aggregate identity `1 + Σρ_Φ = C(a)(1 + Σρ_Ψ)`, `C(a) = detScale⁻¹ (1/√a)⁴` (`rankFour_shellDensity_aggregate_identity`).
Nothing is chosen: every class statement is proved for the class itself.
-/

noncomputable section

open Filter Topology RationalQuadraticSpaceMatrix Complex
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

open IntegralFiniteAdelePhase

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## Reality, positivity and domination of the class limits -/

theorem dualClassTubeLimit_real_nonneg_le (a : L.PolarDiscriminantGroup) {M : ℤ} (hM : M ≠ 0) :
    (L.dualClassTubeLimit a M).im = 0 ∧ 0 ≤ (L.dualClassTubeLimit a M).re ∧
      (L.dualClassTubeLimit a M).re ≤ ∏' p : Nat.Primes, L.localResidueDensity M p := by
  have hT := L.tendsto_dualClassTubeLimit a hM
  have hS : Tendsto (fun j ↦ L.finiteTubeMass rationalFiniteAdeleVectorIntegralIndicator
      (Nat.factorial j) M) atTop (𝓝 ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ)) :=
    L.tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity (n := 3) le_rfl hM
  have hev : ∀ᶠ j in atTop, ∃ r s : ℝ, 0 ≤ r ∧ r ≤ s ∧
      L.finiteTubeMass (residueRestrictedIndicator 4 L.polarGramMatrix.det.natAbs {L.discriminantResidue a})
        (Nat.factorial j) M = r ∧
      L.finiteTubeMass rationalFiniteAdeleVectorIntegralIndicator (Nat.factorial j) M = s := by
    filter_upwards [eventually_ge_atTop L.polarGramMatrix.det.natAbs] with j hj
    exact L.finiteTubeMass_residueRestricted_eq_ofReal_le (Nat.factorial_ne_zero j)
      (Nat.dvd_factorial (Nat.pos_of_ne_zero L.natAbs_det_ne_zero) hj) _ M
  have hTre := (continuous_re.tendsto _).comp hT
  have hTim := (continuous_im.tendsto _).comp hT
  have hSre := (continuous_re.tendsto _).comp hS
  simp only [Function.comp_def, ofReal_re] at hSre
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_nhds_unique hTim (tendsto_const_nhds.congr' ?_)
    filter_upwards [hev] with j hj
    obtain ⟨r, s, -, -, hr, -⟩ := hj
    simp [hr]
  · refine ge_of_tendsto hTre ?_
    filter_upwards [hev] with j hj
    obtain ⟨r, s, hr0, -, hr, -⟩ := hj
    simp [hr, hr0]
  · refine le_of_tendsto_of_tendsto hTre hSre ?_
    filter_upwards [hev] with j hj
    obtain ⟨r, s, -, hrs, hr, hs⟩ := hj
    simp [hr, hs, hrs]

/-! ## The archimedean factor is real and nonnegative -/

theorem fourier_polarArchimedeanBruhatFactor_im_eq_zero {α : ℝ} (hα : 0 < α) (v : ℝ) :
    (𝓕 (L.polarArchimedeanBruhatFactor α) v).im = 0 := by
  rcases le_or_gt v 0 with hv | hv
  · rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num) hv, zero_im]
  · rw [L.fourier_polarArchimedeanBruhatFactor_of_pos hα (by norm_num) hv, ofReal_im]

theorem fourier_polarArchimedeanBruhatFactor_re_nonneg {α : ℝ} (hα : 0 < α) (v : ℝ) :
    0 ≤ (𝓕 (L.polarArchimedeanBruhatFactor α) v).re := by
  rcases le_or_gt v 0 with hv | hv
  · rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num) hv, zero_re]
  · rw [L.fourier_polarArchimedeanBruhatFactor_of_pos hα (by norm_num) hv, ofReal_re]
    have hdet : (0 : ℝ) < (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_pos.2 (by exact_mod_cast L.polarRealDeterminantScale_pos)
    have hΓ : 0 < Real.Gamma (((4 : ℕ) : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity

/-! ## Positivity and support of the dual shell density -/

theorem dualShellDensity_nonneg {α : ℝ} (hα : 0 < α) (b : ℚ) : 0 ≤ dualShellDensity L α b := by
  unfold dualShellDensity
  split_ifs with hden
  · rcases le_or_gt b 0 with hb | hb
    · rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num) (by exact_mod_cast hb),
        zero_re, zero_mul]
    · have hM : ((L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * b).num ≠ 0 := by
        rw [Rat.num_ne_zero]
        have : (0 : ℚ) < (L.polarGramMatrix.det.natAbs : ℚ) ^ 2 := by
          have := L.natAbs_det_ne_zero
          positivity
        positivity
      refine mul_nonneg (L.fourier_polarArchimedeanBruhatFactor_re_nonneg hα _)
        (mul_nonneg (by positivity) ?_)
      rw [re_sum]
      exact Finset.sum_nonneg fun a _ ↦ (L.dualClassTubeLimit_real_nonneg_le a hM).2.1
  · exact le_rfl

/-- The dual shell density vanishes off the represented nonzero norms. -/
theorem support_dualShellDensity_subset {α : ℝ} (hα : 0 < α) :
    Function.support (dualShellDensity L α) ⊆
      Set.range (Subtype.val : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℚ) := by
  intro b hb
  rw [Function.mem_support] at hb
  unfold dualShellDensity at hb
  split_ifs at hb with hden
  · set d : ℕ := L.polarGramMatrix.det.natAbs
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
    have hbpos : 0 < b := by
      by_contra hb0
      apply hb
      rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num)
        (by exact_mod_cast not_lt.1 hb0), zero_re, zero_mul]
    set M : ℤ := ((d : ℚ) ^ 2 * b).num with hMdef
    have hMq : (M : ℚ) = (d : ℚ) ^ 2 * b := by
      have := Rat.num_div_den ((d : ℚ) ^ 2 * b)
      rw [hden, Nat.cast_one, div_one] at this
      exact this
    have hMpos : 0 < M := by
      have : (0 : ℚ) < M := by rw [hMq]; positivity
      exact_mod_cast this
    -- a nonvanishing class limit forces a nonzero singular series, hence a representation
    have hΔ : ∏' p : Nat.Primes, L.localResidueDensity M p ≠ 0 := by
      intro h0
      apply hb
      have hzero : ∀ a, (L.dualClassTubeLimit a M).re = 0 := fun a ↦ by
        obtain ⟨-, h1, h2⟩ := L.dualClassTubeLimit_real_nonneg_le a hMpos.ne'
        rw [h0] at h2
        exact le_antisymm h2 h1
      rw [re_sum, Finset.sum_eq_zero fun a _ ↦ hzero a, mul_zero, mul_zero]
    obtain ⟨x, hx⟩ := L.exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero
      (n := 3) le_rfl hMpos hΔ
    refine ⟨⟨b, hbpos.ne', ((d : ℚ))⁻¹ • x, ?_⟩, rfl⟩
    rw [QuadraticMap.map_smul, hx, hMq, smul_eq_mul]
    field_simp
  · exact absurd rfl hb

/-! ## The row expansion of one discriminant class -/

theorem exp_two_pi_I_mul_I {m α : ℝ} :
    Complex.exp (2 * Real.pi * I * (m : ℂ) * ((α : ℂ) * I)) =
      ((Real.exp (-(2 * Real.pi * α) * m) : ℝ) : ℂ) := by
  rw [ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (m : ℂ) * α) * I_sq

/-- The row terms summed over the level `c`: `Σ_c rowLimitTerm u (iα) (c, λ) = Â_α(m) ∏'δ^{cos}_p(u, λ)`,
`m = λ + q(ν_u)`. -/
theorem hasSum_rowLimitTerm_level (u : Fin 4 → ℤ) {α : ℝ} (hα : 0 < α) (lam : ℤ) :
    HasSum (fun c : ℕ ↦ L.rowLimitTerm u ((α : ℂ) * I) (c, lam))
      (𝓕 (L.polarArchimedeanBruhatFactor α) ((lam : ℝ) + L.polarDualNorm u) *
        ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ)) := by
  set m : ℝ := (lam : ℝ) + L.polarDualNorm u with hmdef
  by_cases hm : 0 < m
  · have hM : L.cosetStandardTarget u lam ≠ 0 := L.cosetStandardTarget_ne_zero u lam hm.ne'
    have hS := L.hasSum_cosetGRCoeff u lam hM
    have hS1 : HasSum (fun c : ℕ ↦ L.cosetGRCoeff u lam (c + 1))
        (∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ)) := by
      have := (hasSum_nat_add_iff' 1).2 hS
      simpa [L.cosetGRCoeff_zero u lam] using this
    have hterm : ∀ c : ℕ, L.rowLimitTerm u ((α : ℂ) * I) (c, lam) =
        ((4 * Real.pi ^ 2 * L.polarKappa * m * Real.exp (-(2 * Real.pi * α) * m) : ℝ) : ℂ) *
          L.cosetGRCoeff u lam (c + 1) := by
      intro c
      simp only [rowLimitTerm]
      rw [← hmdef, if_pos hm, show m = (lam : ℝ) + L.polarDualNorm u from hmdef,
        L.gaussRowCoefficient_eq_cosetGRCoeff (c + 1) u lam, ← hmdef, exp_two_pi_I_mul_I]
      push_cast
      ring
    rw [L.fourier_polarArchimedeanBruhatFactor_of_pos hα (by norm_num) hm]
    have hconst : (((L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ (((4 : ℕ) : ℝ) / 2) / Real.Gamma (((4 : ℕ) : ℝ) / 2)) *
          m ^ (((4 : ℕ) : ℝ) / 2 - 1) * Real.exp (-(2 * Real.pi * α) * m) : ℝ) : ℂ) =
        ((4 * Real.pi ^ 2 * L.polarKappa * m * Real.exp (-(2 * Real.pi * α) * m) : ℝ) : ℂ) := by
      rw [L.polarKappa_eq_inv_polarRealDeterminantScale]
      have h2 : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
      rw [h2, Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      push_cast
      ring
    rw [hconst]
    exact (hS1.mul_left _).congr_fun fun c ↦ hterm c
  · have h0 : ∀ c : ℕ, L.rowLimitTerm u ((α : ℂ) * I) (c, lam) = 0 := fun c ↦ by
      simp only [rowLimitTerm]
      rw [if_neg hm]
    rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num) (not_lt.1 hm), zero_mul]
    simp_rw [h0]
    exact hasSum_zero

/-- The row expansion of a class: `Σ_λ Â_α(λ + q(ν_u)) ∏'δ^{cos}_p(u, λ) = E_row(iα)_{[u]} − e₀[u]`. -/
theorem hasSum_rowLevelSum (u : Fin 4 → ℤ) {α : ℝ} (hα : 0 < α) :
    HasSum (fun lam : ℤ ↦ 𝓕 (L.polarArchimedeanBruhatFactor α) ((lam : ℝ) + L.polarDualNorm u) *
        ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ))
      (L.boundaryRowLimit ((α : ℂ) * I) (u : L.PolarDiscriminantGroup) -
        L.gaussE0 (u : L.PolarDiscriminantGroup)) := by
  have hz := mem_upperHalfSet_mul_I hα
  rw [L.boundaryRowLimit_apply hz u, add_sub_cancel_left]
  have hα2 : 0 < α / 2 := by positivity
  have hK : 0 ≤ SMSFormula.RowKernel.rowKernelDecay (α / 2) / (4 * Real.pi ^ 2) :=
    div_nonneg (rowKernelDecay_nonneg hα2) (by positivity)
  have hsum : Summable (L.rowLimitTerm u ((α : ℂ) * I)) :=
    Summable.of_norm_bounded (L.summable_rowMajorant hK u) fun p ↦
      L.norm_rowLimitTerm_le hα2 u (by simp; linarith) p
  have hsum' : Summable fun q : ℤ × ℕ ↦ L.rowLimitTerm u ((α : ℂ) * I) (Equiv.prodComm ℤ ℕ q) :=
    (Equiv.prodComm ℤ ℕ).summable_iff.2 hsum
  rw [← (Equiv.prodComm ℤ ℕ).tsum_eq]
  exact hsum'.hasSum.prod_fiberwise fun lam ↦ L.hasSum_rowLimitTerm_level u hα lam

/-! ## The class parts of the dual shell density -/

/-- The class part `G_a(m) = Re Â_α(m/d²) · d² · Re D_a(m)` of the dual shell density. -/
def dualClassShellPart (α : ℝ) (a : L.PolarDiscriminantGroup) (m : ℤ) : ℝ :=
  (𝓕 (L.polarArchimedeanBruhatFactor α) ((m : ℝ) / (L.polarGramMatrix.det.natAbs : ℝ) ^ 2)).re *
    ((L.polarGramMatrix.det.natAbs : ℝ) ^ 2 * (L.dualClassTubeLimit a m).re)

theorem cosetStandardTarget_div_sq (u : Fin 4 → ℤ) (lam : ℤ) :
    ((L.cosetStandardTarget u lam : ℤ) : ℝ) / (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 =
      (lam : ℝ) + L.polarDualNorm u := by
  have hD : ((L.polarGramMatrix.det.natAbs : ℕ) : ℝ) = ((L.polarGramMatrix.det : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, L.natAbs_det_eq]
  have hD0 : ((L.polarGramMatrix.det : ℤ) : ℝ) ≠ 0 := by exact_mod_cast L.polarGramMatrix_det_ne_zero
  rw [L.cosetStandardTarget_cast u lam, hD]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- The class part of the dual shell density is the row expansion: `Σ_m G_a(m) = Re(E_row(iα)_a − e₀ a)`, and
`E_row(iα)_a − e₀ a` is real. -/
theorem hasSum_dualClassShellPart {α : ℝ} (hα : 0 < α) (a : L.PolarDiscriminantGroup) :
    HasSum (L.dualClassShellPart α a) (L.boundaryRowLimit ((α : ℂ) * I) a - L.gaussE0 a).re ∧
      (L.boundaryRowLimit ((α : ℂ) * I) a - L.gaussE0 a).im = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  have hd0 : (L.polarGramMatrix.det.natAbs : ℝ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
  set g : ℤ → ℤ := fun lam ↦ L.cosetStandardTarget u lam with hgdef
  have hginj : Function.Injective g := by
    intro l₁ l₂ h
    have h' : L.polarGramMatrix.det ^ 2 * l₁ = L.polarGramMatrix.det ^ 2 * l₂ := by
      simp only [hgdef, cosetStandardTarget] at h
      linarith
    exact mul_left_cancel₀ (pow_ne_zero 2 L.polarGramMatrix_det_ne_zero) h'
  have hsupp : ∀ m, m ∉ Set.range g → L.dualClassShellPart α (u : L.PolarDiscriminantGroup) m = 0 := by
    intro m hm
    have hne : ∀ lam : ℤ, m ≠ L.cosetStandardTarget u lam := fun lam h ↦ hm ⟨lam, h.symm⟩
    unfold dualClassShellPart
    rw [L.dualClassTubeLimit_of_ne u hne, zero_re, mul_zero, mul_zero]
  -- the row term is the real class part
  set T : ℤ → ℂ := fun lam ↦ 𝓕 (L.polarArchimedeanBruhatFactor α) ((lam : ℝ) + L.polarDualNorm u) *
    ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ) with hTdef
  have hT : ∀ lam, T lam = ((L.dualClassShellPart α (u : L.PolarDiscriminantGroup) (g lam) : ℝ) : ℂ) := by
    intro lam
    simp only [hTdef, hgdef, dualClassShellPart]
    rw [L.cosetStandardTarget_div_sq u lam]
    by_cases hM : L.cosetStandardTarget u lam = 0
    · have hm0 : (lam : ℝ) + L.polarDualNorm u = 0 := by
        rw [← L.cosetStandardTarget_div_sq u lam, hM, Int.cast_zero, zero_div]
      rw [hm0, L.fourier_polarArchimedeanBruhatFactor_of_nonpos hα (by norm_num) le_rfl, zero_mul,
        zero_re, zero_mul, ofReal_zero]
    · have hlim := L.dualClassTubeLimit_of_eq u lam hM
      have hreal := L.dualClassTubeLimit_real_nonneg_le (u : L.PolarDiscriminantGroup) hM
      have hprod : ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ) =
          (((L.polarGramMatrix.det.natAbs : ℝ) ^ 2 *
            (L.dualClassTubeLimit (u : L.PolarDiscriminantGroup) (L.cosetStandardTarget u lam)).re : ℝ) : ℂ) := by
        have hre : L.dualClassTubeLimit (u : L.PolarDiscriminantGroup) (L.cosetStandardTarget u lam) =
            (((L.dualClassTubeLimit (u : L.PolarDiscriminantGroup)
              (L.cosetStandardTarget u lam)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal.1])
        have hdC : (L.polarGramMatrix.det.natAbs : ℂ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
        rw [ofReal_mul, ← hre, hlim]
        push_cast
        field_simp
      have hF := L.fourier_polarArchimedeanBruhatFactor_im_eq_zero hα ((lam : ℝ) + L.polarDualNorm u)
      rw [hprod]
      apply Complex.ext
      · simp [hF]
      · simp [hF]
  have hrow := L.hasSum_rowLevelSum u hα
  have hrowT : HasSum T _ := hrow
  have hre := Complex.hasSum_re hrowT
  have him := Complex.hasSum_im hrowT
  simp only [hT, ofReal_re, ofReal_im] at hre him
  refine ⟨(hginj.hasSum_iff hsupp).1 hre, ?_⟩
  exact (hasSum_zero.unique him).symm

/-! ## The aggregate -/

theorem dualShellDensity_eq_sum (α : ℝ) (m : ℤ) :
    dualShellDensity L α ((m : ℚ) / (L.polarGramMatrix.det.natAbs : ℚ) ^ 2) =
      ∑ a, L.dualClassShellPart α a m := by
  have hd0 : (L.polarGramMatrix.det.natAbs : ℚ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
  have hq : (L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * ((m : ℚ) / (L.polarGramMatrix.det.natAbs : ℚ) ^ 2) = m := by
    field_simp
  unfold dualShellDensity dualClassShellPart
  rw [hq, if_pos (Rat.den_intCast m), Rat.num_intCast, re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  push_cast
  ring

theorem support_dualShellDensity_subset_div (α : ℝ) :
    Function.support (dualShellDensity L α) ⊆
      Set.range (fun m : ℤ ↦ (m : ℚ) / (L.polarGramMatrix.det.natAbs : ℚ) ^ 2) := by
  intro b hb
  rw [Function.mem_support] at hb
  unfold dualShellDensity at hb
  split_ifs at hb with hden
  · refine ⟨((L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * b).num, ?_⟩
    have hd0 : (L.polarGramMatrix.det.natAbs : ℚ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
    have := Rat.num_div_den ((L.polarGramMatrix.det.natAbs : ℚ) ^ 2 * b)
    rw [hden, Nat.cast_one, div_one] at this
    simp only
    rw [this]
    field_simp
  · exact absurd rfl hb

set_option maxHeartbeats 800000 in
/-- The dual-side aggregate (rank four): `ρ_Ψ ≥ 0`, `ρ_Ψ` summable over the represented norms, and
`1 + Σ_b ρ_Ψ(b) = Σ_ν E_row(i/a)_ν`. -/
theorem dualShellDensity_aggregate {a : ℝ} (ha : 0 < a) :
    (∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        0 ≤ dualShellDensity L a⁻¹ b.1) ∧
      Summable (fun b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm ↦
        dualShellDensity L a⁻¹ b.1) ∧
      (((1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          dualShellDensity L a⁻¹ b.1 : ℝ)) : ℂ) =
        ∑ ν, L.boundaryRowLimit (((a⁻¹ : ℝ) : ℂ) * I) ν := by
  classical
  have hα : 0 < a⁻¹ := inv_pos.2 ha
  have hd0 : (L.polarGramMatrix.det.natAbs : ℚ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
  -- the class parts
  have hclass := fun ν ↦ L.hasSum_dualClassShellPart hα ν
  have hZ : HasSum (fun m : ℤ ↦ ∑ ν, L.dualClassShellPart a⁻¹ ν m)
      (∑ ν, (L.boundaryRowLimit (((a⁻¹ : ℝ) : ℂ) * I) ν - L.gaussE0 ν).re) :=
    hasSum_sum fun ν _ ↦ (hclass ν).1
  -- reindex `ℤ → ℚ`, `m ↦ m / d²`
  have hdivinj : Function.Injective (fun m : ℤ ↦ (m : ℚ) / (L.polarGramMatrix.det.natAbs : ℚ) ^ 2) := by
    intro m₁ m₂ h
    have : (m₁ : ℚ) = m₂ := (div_left_inj' (pow_ne_zero 2 hd0)).1 h
    exact_mod_cast this
  have hQ : HasSum (dualShellDensity L a⁻¹)
      (∑ ν, (L.boundaryRowLimit (((a⁻¹ : ℝ) : ℂ) * I) ν - L.gaussE0 ν).re) := by
    refine (hdivinj.hasSum_iff fun b hb ↦ Function.notMem_support.1 fun h ↦
      hb (L.support_dualShellDensity_subset_div a⁻¹ h)).1 ?_
    refine hZ.congr_fun fun m ↦ ?_
    exact L.dualShellDensity_eq_sum a⁻¹ m
  -- reindex `Rep → ℚ`
  have hval : Function.Injective
      (Subtype.val : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℚ) :=
    Subtype.val_injective
  have hRep := (hval.hasSum_iff fun b hb ↦ Function.notMem_support.1 fun h ↦
    hb (L.support_dualShellDensity_subset hα h)).2 hQ
  refine ⟨fun b ↦ L.dualShellDensity_nonneg hα _, hRep.summable, ?_⟩
  change ((1 + ∑' b, (dualShellDensity L a⁻¹ ∘ Subtype.val) b : ℝ) : ℂ) = _
  rw [hRep.tsum_eq]
  -- assemble: `Σ_ν E_ν = Σ_ν e₀ ν + Σ_ν (E_ν − e₀ ν)`, and `Σ_ν e₀ ν = 1`
  have hE0 : ∑ ν, L.gaussE0 ν = 1 := by
    simp [gaussE0, Finset.sum_pi_single']
  have hsplit : ∑ ν, L.boundaryRowLimit (((a⁻¹ : ℝ) : ℂ) * I) ν =
      1 + ∑ ν, (L.boundaryRowLimit (((a⁻¹ : ℝ) : ℂ) * I) ν - L.gaussE0 ν) := by
    rw [Finset.sum_sub_distrib, hE0]
    ring
  rw [hsplit, ofReal_add, ofReal_one, ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  exact Complex.ext (by simp) (by rw [ofReal_im, (hclass ν).2])

/-! ## The aggregate identity `hE` -/

/-- The rank-four aggregate identity: `1 + Σ_b ρ_Φ(b) = C(a) (1 + Σ_b ρ_Ψ(b))`, `C(a) = detScale⁻¹ (1/√a)⁴`. -/
theorem rankFour_shellDensity_aggregate_identity {a : ℝ} (ha : 0 < a) :
    1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm, latticeShellDensity L a b.1 =
      (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ 4 *
        (1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          dualShellDensity L a⁻¹ b.1) := by
  obtain ⟨-, -, hΦ⟩ := L.latticeShellDensity_aggregate ha
  obtain ⟨-, -, hΨ⟩ := L.dualShellDensity_aggregate ha
  have h82 := L.standardAggregate_inv_eq (inv_pos.2 ha)
  rw [inv_inv] at h82
  rw [← hΨ, ← hΦ] at h82
  have hC : (1 / a ^ (1 / 2 : ℝ)) ^ 4 = (a⁻¹) ^ 2 := by
    rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  rw [hC, ← L.polarKappa_eq_inv_polarRealDeterminantScale]
  have h := congrArg Complex.re h82
  rw [ofReal_re, ← ofReal_mul, ofReal_re] at h
  rw [h]
  ring

end PositiveDefiniteIntegralLattice
