import SMSFormula.RationalAdeleRankOneEisensteinPoisson
import SMSFormula.RationalFiniteAdelePeriodCosetDecomposition
import SMSFormula.RationalAdeleRankOneWeylBruhatAnalyticReduction
import SMSFormula.AdelicGaussianDualCarrierCore
import SMSFormula.RationalAdeleDualTestGeometricCovariance
import SMSFormula.RationalAdeleRankOneEisensteinSiegelWeyl
import SMSFormula.RationalAdeleRealCuspGaussianFactorization
import Mathlib.Data.Rat.Star

/-!
# Rank-one adelic Poisson summation for the DUAL-carrier test

The dual-carrier test `Ψ` (`rationalAdeleVectorPolarGaussianDualTest`: the polar Gaussian at
the real place, the indicator of the polar dual lattice `L^#` at the finite places) has Bruhat
family `B_Ψ(t) = A(t) G^#(t)`, with `A` the archimedean factor and `G^#` the dual finite
Gauss integral.  Since `L^# ⊆ D⁻¹ Ẑ^n` (`D = |polarDeterminant L|`, inclusion), `D² Q(L^#) ⊆ Ẑ`, so `G^#`
is `D² Ẑ`-periodic, with the canonical period `N = D²`.  The period-`N` coset decomposition and
Mathlib's real Poisson summation for `x ↦ A(N x)` then give, exactly as for the standard test,

`E(Ψ) = Ψ(0) + ∑_{b ∈ ℚ} d_Ψ(b)`.

Summability of the dual Bruhat family is the Weyl-transported summability (the Weyl transform
of the standard test is a nonzero multiple of `Ψ`); absolute summability of `G^#` on the canonical
representatives follows from it and a positive lower bound of `|A|` on `[0, N]`.  Nothing is
chosen.
-/

noncomputable section

open MeasureTheory Filter Asymptotics PositiveDefiniteIntegralLattice
open scoped FourierTransform Real

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The dual finite Gauss integral at an arbitrary finite-adelic parameter. -/
noncomputable def rationalFiniteAdeleDualQuadraticGaussIntegralAt
    (V : RationalQuadraticSpaceMatrix n) (s : RationalFiniteAdele) : ℂ :=
  ∫ x : Fin n → RationalFiniteAdele,
    (V.rationalFiniteAdeleQuadraticPhaseAt s x : ℂ) * V.finitePolarDualLatticeIndicator x
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

@[simp]
theorem rationalFiniteAdeleDualQuadraticGaussIntegralAt_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) :
    V.rationalFiniteAdeleDualQuadraticGaussIntegralAt (algebraMap ℚ RationalFiniteAdele t) =
      V.rationalFiniteAdeleDualQuadraticGaussIntegral t :=
  rfl

/-- Exact real--finite factorization of the adelic Bruhat coefficient of the dual test. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianDual_eq_real_mul_finiteAt
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianDualTest L b) a =
      polarRealGaussianFourierProduct L
          (b - (rationalAdeleRealScalar a : ℂ) * Complex.I) 0 *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt a.2 := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  let V := L.rationalQuadraticSpaceMatrix
  let s := rationalAdeleRealScalar a
  let gr : (Fin n → ℝ) → ℂ := fun x ↦ polarRealGaussian L (b - (s : ℂ) * Complex.I) x
  let gf : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    (V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : ℂ) * V.finitePolarDualLatticeIndicator x
  let g : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) → ℂ := fun z ↦ gr z.1 * gf z.2
  have hparam : 0 < (b - (s : ℂ) * Complex.I).re := by
    norm_num [Complex.mul_re]
    exact hb
  have hintegrand :
      (fun x : Fin n → RationalAdele ↦
        (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) *
          PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianDualTest L b x) =
        fun x ↦ g (rationalAdeleVectorRealFiniteEquiv n x) := by
    funext x
    rw [V.rationalAdeleRankOneQuadraticPhase_eq_real_mul_finiteAt]
    simp only [PositiveDefiniteIntegralLattice.rationalAdeleVectorPolarGaussianDualTest]
    simp only [g, gr, gf, s, rationalAdeleVectorRealFiniteEquiv_apply]
    rw [← RationalQuadraticSpaceMatrix.realQuadraticPhase_mul_polarRealGaussian_real L]
    ring
  rw [rationalAdeleRankOneAdelicBruhatCoefficient,
    rationalAdeleRankOneWeylOperator, Fourier.fourierIntegral_def]
  simp only [Matrix.mulVec_zero, mul_zero, neg_zero, rationalAdeleRankOneUnipotentOperator]
  rw [AddChar.map_zero_eq_one]
  simp only [one_smul]
  rw [hintegrand]
  rw [(measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' g]
  rw [MeasureTheory.integral_prod_mul]
  change
    (∫ x : Fin n → ℝ, gr x ∂(volume : Measure (Fin n → ℝ))) *
      (∫ x : Fin n → RationalFiniteAdele, gf x
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) = _
  have hreal := polarReal_fourierIntegral_gaussian hparam L (0 : Fin n → ℝ)
  rw [Fourier.fourierIntegral_def] at hreal
  have hreal' :
      (∫ x : Fin n → ℝ, gr x ∂(volume : Measure (Fin n → ℝ))) =
        polarRealGaussianFourierProduct L (b - (s : ℂ) * Complex.I) 0 := by
    simpa only [gr, Matrix.mulVec_zero, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, one_smul] using hreal
  rw [hreal']
  rfl

/-- The dual carrier satisfies `D² Q(L^#) ⊆ Ẑ`, `D = |polarDeterminant L|`. -/
theorem polarDeterminant_sq_mul_finiteAdelicQuadraticFormValue_mem_integral (L : PositiveDefiniteIntegralLattice n)
    {x : Fin n → RationalFiniteAdele}
    (hx : x ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice) :
    ((L.polarDeterminant.natAbs ^ 2 : ℕ) : RationalFiniteAdele) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x ∈
      integralFiniteAdeleSubring := by
  have hD : L.polarDeterminant.natAbs • x ∈ integralFiniteAdeleVectors n :=
    PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase.finitePolarDualLattice_subset_standardDividedLattice L hx
  have hQ : L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (L.polarDeterminant.natAbs • x) ∈ integralFiniteAdeleSubring := by
    simpa [finiteAdelicQuadraticFormValue] using
      L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring _ _ hD hD
  have hhom : L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (L.polarDeterminant.natAbs • x) =
      ((L.polarDeterminant.natAbs ^ 2 : ℕ) : RationalFiniteAdele) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x := by
    rw [← Nat.cast_smul_eq_nsmul RationalFiniteAdele]
    simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, Nat.cast_pow]
    ring
  rw [← hhom]
  exact hQ

/-- The dual finite Gauss integral is `D² Ẑ`-PERIODIC. -/
theorem rationalFiniteAdeleDualQuadraticGaussIntegralAt_add_period (L : PositiveDefiniteIntegralLattice n)
    (s z : RationalFiniteAdele) (hz : z ∈ integralFiniteAdeleSubring) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt
        (s + algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs ^ 2 : ℕ) : ℚ) * z) =
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt s := by
  unfold rationalFiniteAdeleDualQuadraticGaussIntegralAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · have hint : z * (((L.polarDeterminant.natAbs ^ 2 : ℕ) : RationalFiniteAdele) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x) ∈
          integralFiniteAdeleSubring :=
      Subring.mul_mem _ hz (polarDeterminant_sq_mul_finiteAdelicQuadraticFormValue_mem_integral L hx)
    have hphase : L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
        (s + algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs ^ 2 : ℕ) : ℚ) * z) x =
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt s x := by
      unfold rationalFiniteAdeleQuadraticPhaseAt
      rw [add_mul, AddChar.map_add_eq_mul, map_natCast,
        show ((L.polarDeterminant.natAbs ^ 2 : ℕ) : RationalFiniteAdele) * z *
            L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x =
          z * (((L.polarDeterminant.natAbs ^ 2 : ℕ) : RationalFiniteAdele) *
            L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x) by ring,
        PositiveDefiniteIntegralLattice.rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hint, mul_one]
    dsimp only
    rw [hphase]
  · dsimp only
    rw [finitePolarDualLatticeIndicator_of_not_mem _ hx, mul_zero, mul_zero]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Real Poisson summation with period `M` -/

/-- The Fourier transform of the rescaled archimedean factor `x ↦ A(M x)`. -/
theorem fourier_polarArchimedeanBruhatFactor_comp_mul (L : PositiveDefiniteIntegralLattice n) (c : ℝ) {M : ℝ}
    (hM : 0 < M) (w : ℝ) :
    𝓕 (fun x ↦ L.polarArchimedeanBruhatFactor c (M * x)) w =
      (M⁻¹ : ℂ) * 𝓕 (L.polarArchimedeanBruhatFactor c) (w / M) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ ↦ Complex.exp (↑(-2 * π * y * (w / M)) * Complex.I) •
      L.polarArchimedeanBruhatFactor c y) M
  have hint : (fun x : ℝ ↦ Complex.exp (↑(-2 * π * x * w) * Complex.I) •
      L.polarArchimedeanBruhatFactor c (M * x)) =
      fun x : ℝ ↦ Complex.exp (↑(-2 * π * (M * x) * (w / M)) * Complex.I) •
        L.polarArchimedeanBruhatFactor c (M * x) := by
    funext x
    congr 3
    field_simp
  rw [hint, h, abs_of_pos (inv_pos.2 hM), Complex.real_smul]
  push_cast
  rfl

/-- The rescaled archimedean factor decays like `|x|^{-n/2}`. -/
theorem polarArchimedeanBruhatFactor_comp_mul_isBigO (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) {M : ℝ} (hM : 0 < M) :
    (fun x ↦ L.polarArchimedeanBruhatFactor c (M * x)) =O[cocompact ℝ]
      (|·| ^ (-((n : ℝ) / 2))) := by
  refine Asymptotics.IsBigO.of_bound
    ((L.polarRealDeterminantScale : ℝ)⁻¹ * (min c 1 / 2) ^ (-((n : ℝ) / 2)) *
      M ^ (-((n : ℝ) / 2))) ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := hx
  have hMx : 0 < |M * x| := abs_pos.2 (mul_ne_zero hM.ne' hx0)
  rw [polarArchimedeanBruhatFactor, norm_archimedeanBruhatFactor,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  have hbound := archimedeanBound_le (n := n) hc hn (M * x)
  have hmono : (1 + ‖M * x‖) ^ (-((n : ℝ) / 2)) ≤ |M * x| ^ (-((n : ℝ) / 2)) := by
    refine Real.rpow_le_rpow_of_nonpos hMx ?_ ?_
    · rw [Real.norm_eq_abs]; linarith
    · have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      linarith
  have hsplit : |M * x| ^ (-((n : ℝ) / 2)) = M ^ (-((n : ℝ) / 2)) * |x| ^ (-((n : ℝ) / 2)) := by
    rw [abs_mul, abs_of_pos hM, Real.mul_rpow hM.le (abs_nonneg x)]
  have hdet : 0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ :=
    inv_nonneg.2 L.polarRealDeterminantScale_pos.le
  have hK : 0 ≤ (min c 1 / 2) ^ (-((n : ℝ) / 2)) := by
    have : 0 < min c 1 / 2 := by
      have := lt_min hc zero_lt_one
      linarith
    positivity
  calc (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - ((M * x : ℝ) : ℂ) * Complex.I‖)⁻¹ ^ n
      ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ *
          ((min c 1 / 2) ^ (-((n : ℝ) / 2)) * (1 + ‖M * x‖) ^ (-((n : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hbound hdet
    _ ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ *
          ((min c 1 / 2) ^ (-((n : ℝ) / 2)) * |M * x| ^ (-((n : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hK) hdet
    _ = _ := by rw [hsplit]; ring

/-- The archimedean Fourier transform is absolutely summable along every positive arithmetic
progression `k M'`, `k ∈ ℤ`. -/
theorem summable_norm_fourier_polarArchimedeanBruhatFactor_mul (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hn : 3 ≤ n) {M' : ℝ} (hM' : 0 < M') :
    Summable fun k : ℤ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c) (k * M')‖ := by
  set K : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ *
    ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) with hKdef
  have hK : 0 ≤ K := by
    have hdet : 0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_nonneg.2 L.polarRealDeterminantScale_pos.le
    have hΓ : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have ha : 0 < 2 * Real.pi * c * M' := by positivity
  have hs : 0 ≤ (n : ℝ) / 2 - 1 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
      ((Real.summable_pow_mul_exp_neg_nat_mul n ha).mul_left (K * M' ^ ((n : ℝ) / 2 - 1)))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Int.cast_natCast, Nat.cast_zero, zero_mul,
        L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn le_rfl, norm_zero]
      positivity
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
      rw [Int.cast_natCast, L.fourier_polarArchimedeanBruhatFactor_of_pos hc hn (by positivity),
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hpow : (m : ℝ) ^ ((n : ℝ) / 2 - 1) ≤ (m : ℝ) ^ n := by
        rw [← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
        have : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      rw [Real.mul_rpow hmpos.le hM'.le]
      have hexp : Real.exp (-(2 * Real.pi * c) * ((m : ℝ) * M')) =
          Real.exp (-(2 * Real.pi * c * M') * m) := by ring_nf
      rw [hexp]
      calc K * ((m : ℝ) ^ ((n : ℝ) / 2 - 1) * M' ^ ((n : ℝ) / 2 - 1)) *
            Real.exp (-(2 * Real.pi * c * M') * m)
          ≤ K * ((m : ℝ) ^ n * M' ^ ((n : ℝ) / 2 - 1)) *
            Real.exp (-(2 * Real.pi * c * M') * m) := by
            gcongr
        _ = K * M' ^ ((n : ℝ) / 2 - 1) *
            ((m : ℝ) ^ n * Real.exp (-(2 * Real.pi * c * M') * m)) := by ring
  · have hzero : (fun m : ℕ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c)
        (((-(m : ℤ) : ℤ) : ℝ) * M')‖) = fun _ ↦ 0 := by
      funext m
      have hm : ((-(m : ℤ) : ℤ) : ℝ) * M' ≤ 0 := by
        push_cast
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (Nat.cast_nonneg m)) hM'.le
      rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn hm, norm_zero]
    rw [hzero]
    exact summable_zero

/-- Real Poisson summation with period `M` (Mathlib, applied to `x ↦ A(M x)`). -/
theorem tsum_polarArchimedeanBruhatFactor_add_mul_int (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) {M : ℝ} (hM : 0 < M) (x : ℝ) :
    ∑' m : ℤ, L.polarArchimedeanBruhatFactor c (x + M * m) =
      ∑' k : ℤ, ((M⁻¹ : ℂ) * 𝓕 (L.polarArchimedeanBruhatFactor c) (k / M)) *
        fourier k ((x / M : ℝ) : UnitAddCircle) := by
  have hb : 1 < (n : ℝ) / 2 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcont : Continuous fun y : ℝ ↦ L.polarArchimedeanBruhatFactor c (M * y) :=
    (L.continuous_polarArchimedeanBruhatFactor hc).comp (continuous_const.mul continuous_id)
  have hsum : Summable fun k : ℤ ↦ 𝓕 (fun y ↦ L.polarArchimedeanBruhatFactor c (M * y)) k := by
    refine Summable.of_norm (((L.summable_norm_fourier_polarArchimedeanBruhatFactor_mul hc hn
      (inv_pos.2 hM)).mul_left M⁻¹).congr fun k ↦ ?_)
    rw [fourier_polarArchimedeanBruhatFactor_comp_mul L c hM, norm_mul, div_eq_mul_inv]
    congr 1
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hM.le]
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont hb
    (L.polarArchimedeanBruhatFactor_comp_mul_isBigO hc hn hM) hsum (x / M)
  have hlhs : ∀ m : ℤ, L.polarArchimedeanBruhatFactor c (M * (x / M + m)) =
      L.polarArchimedeanBruhatFactor c (x + M * m) := by
    intro m
    congr 1
    field_simp
  simp_rw [hlhs, fourier_polarArchimedeanBruhatFactor_comp_mul L c hM] at hP
  exact hP

/-! ## The dual Bruhat family on `ℚ` -/

private theorem rationalAdele_algebraMap_fst_dualPoisson (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 = algebraMap ℚ RationalInfiniteAdele q :=
  DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

private theorem rationalAdele_algebraMap_snd_dualPoisson (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 = algebraMap ℚ RationalFiniteAdele q :=
  DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

theorem rationalAdeleRealScalar_algebraMap_rat (q : ℚ) :
    RationalQuadraticSpaceMatrix.rationalAdeleRealScalar (algebraMap ℚ RationalAdele q) =
      (q : ℝ) := by
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRealScalar,
    rationalAdele_algebraMap_fst_dualPoisson, rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  simp

/-- The dual Bruhat family factors as archimedean factor times dual finite Gauss integral. -/
theorem rationalAdeleRankOneBruhatCoefficient_polarGaussianDual_eq_archimedean_mul
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) t =
      L.polarArchimedeanBruhatFactor c (t : ℝ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t := by
  rw [← RationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient_rationalDiagonal,
    RationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianDual_eq_real_mul_finiteAt
      L (by simpa using hc),
    RationalQuadraticSpaceMatrix.polarRealGaussianFourierProduct_zero,
    rationalAdeleRealScalar_algebraMap_rat, rationalAdele_algebraMap_snd_dualPoisson]
  rfl

/-- The Weyl transform of the standard test at scale `c⁻¹` is a nonzero multiple of the dual test
at scale `c` (geometric covariance). -/
theorem rationalAdeleRankOneWeylOperator_polarGaussianLattice_inv_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L ((c⁻¹ : ℝ) : ℂ)) =
      fun y ↦ ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        rationalAdeleVectorPolarGaussianDualTest L (c : ℂ) y := by
  funext y
  rw [L.rationalAdeleRankOneWeylOperator_polarGaussianLattice_eq_const_mul_dual
    (by simpa using inv_pos.2 hc) y]
  congr 2
  push_cast
  exact inv_inv _

theorem weylDualConstant_ne_zero (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) :
    ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ n) ≠ 0 := by
  have hdet : ((L.polarRealDeterminantScale : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast L.polarRealDeterminantScale_pos.ne')
  have hcpow : ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact (inv_pos.2 hc).ne' (by exact_mod_cast h)
  exact mul_ne_zero hdet (pow_ne_zero _ (one_div_ne_zero hcpow))

/-- The dual Bruhat family is summable on `ℚ` (Weyl-transported summability). -/
theorem summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianDual (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    Summable (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
      (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))) := by
  have hW := L.summable_rationalAdeleRankOneBruhatCoefficient_weyl_polarGaussianLattice_of_rankAtLeastFive
    (inv_pos.2 hc) hrank
  rw [L.rationalAdeleRankOneWeylOperator_polarGaussianLattice_inv_eq_const_mul_dual hc] at hW
  set C : ℂ := (L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ n
    with hCdef
  have hC : C ≠ 0 := L.weylDualConstant_ne_zero hc
  refine (hW.mul_left C⁻¹).congr fun t ↦ ?_
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient_const_mul, ← mul_assoc,
    inv_mul_cancel₀ hC, one_mul]

/-- The canonical period of the dual finite Gauss integral, `N = |polarDeterminant L|²`. -/
abbrev dualGaussPeriod (L : PositiveDefiniteIntegralLattice n) : ℕ := L.polarDeterminant.natAbs ^ 2

theorem dualGaussPeriod_ne_zero (L : PositiveDefiniteIntegralLattice n) : L.dualGaussPeriod ≠ 0 :=
  pow_ne_zero _ (Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne')

/-- The dual finite Gauss integral is absolutely summable on the canonical period representatives:
`|B_Ψ| ≥ α |G^#|` on `[0, N]` with `α > 0`, and `B_Ψ` is summable. -/
theorem summable_norm_dualGaussIntegral_periodRep (L : PositiveDefiniteIntegralLattice n) (hrank : 5 ≤ n) :
    Summable fun r : RationalPeriodRep L.dualGaussPeriod ↦
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1‖ := by
  set N := L.dualGaussPeriod with hNdef
  have hB := L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianDual one_pos hrank
  have hBn := (summable_norm_iff.2 hB).comp_injective Subtype.val_injective
    (i := fun r : RationalPeriodRep N ↦ r.1)
  set α : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ * (Real.sqrt (1 + N))⁻¹ ^ n with hαdef
  have hα : 0 < α := by
    have hdet : 0 < (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_pos.2 L.polarRealDeterminantScale_pos
    have : 0 < Real.sqrt (1 + N) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hlow : ∀ r : RationalPeriodRep N,
      α * ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1‖ ≤
        ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
          (rationalAdeleVectorPolarGaussianDualTest L ((1 : ℝ) : ℂ)) r.1‖ := by
    intro r
    rw [L.rationalAdeleRankOneBruhatCoefficient_polarGaussianDual_eq_archimedean_mul one_pos,
      norm_mul, polarArchimedeanBruhatFactor, norm_archimedeanBruhatFactor]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 L.polarRealDeterminantScale_pos.le)
    have hre : ((1 : ℝ) : ℂ) - (((r.1 : ℝ)) : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have h1 : ‖((1 : ℝ) : ℂ) - (((r.1 : ℝ)) : ℂ) * Complex.I‖ ≤ 1 + N := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg zero_le_one, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast r.2.1)]
      have : ((r.1 : ℚ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast r.2.2.le
      linarith
    have h2 : 0 < Real.sqrt ‖((1 : ℝ) : ℂ) - (((r.1 : ℝ)) : ℂ) * Complex.I‖ :=
      Real.sqrt_pos.2 (norm_pos_iff.2 hre)
    have h3 := Real.sqrt_le_sqrt h1
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h2 h3) n
  refine ((hBn.mul_left α⁻¹)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun r ↦ ?_)
  rw [le_inv_mul_iff₀ hα]
  exact hlow r

/-! ## The dual finite local integral -/

/-- The dual finite Gauss integral is integrable on the finite adeles (rank at least five). -/
theorem integrable_dualGaussIntegralAt (L : PositiveDefiniteIntegralLattice n) (hrank : 5 ≤ n) :
    Integrable (fun y : RationalFiniteAdele ↦
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y)
      rationalFiniteAdeleAddHaarMeasure :=
  integrable_of_periodPeriodic L.dualGaussPeriod_ne_zero _
    (fun y z hz ↦
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt_add_period
        L y z hz)
    (L.summable_norm_dualGaussIntegral_periodRep hrank)

theorem integrable_dualFiniteLocalIntegrand (L : PositiveDefiniteIntegralLattice n) (hrank : 5 ≤ n) (t : ℚ) :
    Integrable (fun y : RationalFiniteAdele ↦
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y)
      rationalFiniteAdeleAddHaarMeasure := by
  refine (L.integrable_dualGaussIntegralAt hrank).bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_induced_dom.comp
      (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))
  · filter_upwards with y
    exact le_of_eq (Circle.norm_coe _)

/-- The dual finite local integral vanishes unless `t N ∈ ℤ`. -/
theorem integral_dualFiniteLocal_eq_zero_of_not_int (L : PositiveDefiniteIntegralLattice n) {t : ℚ}
    (ht : t * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range) :
    (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) = 0 := by
  set N := L.dualGaussPeriod
  set I := ∫ y : RationalFiniteAdele,
    ((rationalFiniteAdeleFourierChar (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y
    ∂rationalFiniteAdeleAddHaarMeasure with hIdef
  have hshift := integral_add_right_eq_self (μ := rationalFiniteAdeleAddHaarMeasure)
    (fun y : RationalFiniteAdele ↦
      ((rationalFiniteAdeleFourierChar (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y)
    (algebraMap ℚ RationalFiniteAdele (N : ℚ))
  have hper : ∀ y : RationalFiniteAdele,
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt
          (y + algebraMap ℚ RationalFiniteAdele (N : ℚ)) =
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y := by
    intro y
    have h := RationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt_add_period
      L y 1 (one_mem _)
    rwa [mul_one] at h
  have h : I = ((rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (t * N)) : Circle) : ℂ) * I := by
    conv_lhs => rw [hIdef, ← hshift]
    rw [hIdef, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [hper, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← map_mul]
    ring
  have hchar : rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (t * N)) ≠ 1 := by
    intro hc
    rw [rationalFiniteAdeleFourierChar_eq_one_iff,
      rational_mem_integralFiniteAdeleSubring_iff] at hc
    exact ht hc
  have hne : ((rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (t * N)) : Circle) : ℂ) ≠ 1 := by
    intro hc
    exact hchar (Circle.coe_inj.mp (by rw [hc]; simp))
  have hsub : (1 - ((rationalFiniteAdeleFourierChar
      (algebraMap ℚ RationalFiniteAdele (t * N)) : Circle) : ℂ)) * I = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp hsub with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm hne
  · exact h2

/-- The dual finite Fourier coefficient as a character sum: if `t N ∈ ℤ`,
`∫ ψ_f(t y) G^#(y) dy = N⁻¹ ∑_{r ∈ ℚ ∩ [0,N)} e(t r)⁻¹ G^#(r)`. -/
theorem integral_dualFiniteLocal_eq_tsum_of_int (L : PositiveDefiniteIntegralLattice n) (hrank : 5 ≤ n) {t : ℚ}
    (ht : t * (L.dualGaussPeriod : ℚ) ∈ (algebraMap ℤ ℚ).range) :
    (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure) =
      ((L.dualGaussPeriod : ℂ))⁻¹ * ∑' r : RationalPeriodRep L.dualGaussPeriod,
        (((Real.fourierChar ((t * r.1 : ℚ) : ℝ))⁻¹ : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1 := by
  have htN : algebraMap ℚ RationalFiniteAdele (t * (L.dualGaussPeriod : ℚ)) ∈
      integralFiniteAdeleSubring := (rational_mem_integralFiniteAdeleSubring_iff _).2 ht
  rw [integral_eq_tsum_of_periodPeriodic L.dualGaussPeriod_ne_zero _
    (L.integrable_dualFiniteLocalIntegrand hrank t)]
  · congr 1
    refine tsum_congr fun r ↦ ?_
    rw [← map_mul, rationalFiniteAdeleFourierChar_algebraMap,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt_rationalDiagonal]
  · intro y z hz
    have hmem : algebraMap ℚ RationalFiniteAdele (t * (L.dualGaussPeriod : ℚ)) * z ∈
        integralFiniteAdeleSubring := Subring.mul_mem _ htN hz
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt_add_period
        L y z hz, mul_add, AddChar.map_add_eq_mul,
      show algebraMap ℚ RationalFiniteAdele t *
          (algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs ^ 2 : ℕ) : ℚ) * z) =
        algebraMap ℚ RationalFiniteAdele (t * (L.dualGaussPeriod : ℚ)) * z by
          rw [map_mul]; ring,
      rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hmem, mul_one]

/-! ## The dual value density -/

/-- The scaled-character integral of the dual adelic Bruhat coefficient factors into the real and
dual finite local integrals. -/
theorem integral_scaledChar_mul_adelicBruhat_polarGaussianDual_eq_real_mul_finite
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (t : ℚ) :
    (∫ u, (rationalAdeleScaledFourierChar t u : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianDualTest L b) u
        ∂rationalAdeleAddHaarMeasure) =
      (∫ w : RationalInfiniteAdele,
          ((rationalInfiniteAdeleFourierChar
              (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
            ((L.polarRealDeterminantScale : ℂ)⁻¹ *
              (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
                Complex.I) ^ (1 / 2 : ℂ)) ^ n)
          ∂rationalInfiniteAdeleAddHaarMeasure) *
        (∫ y : RationalFiniteAdele,
          ((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y
          ∂rationalFiniteAdeleAddHaarMeasure) := by
  have hpoint : ∀ u : RationalAdele,
      (rationalAdeleScaledFourierChar t u : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
            (rationalAdeleVectorPolarGaussianDualTest L b) u =
        (((rationalInfiniteAdeleFourierChar
            (algebraMap ℚ RationalInfiniteAdele t * u.1) : Circle) : ℂ) *
          ((L.polarRealDeterminantScale : ℂ)⁻¹ *
            (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal u.1 : ℝ) : ℂ) *
              Complex.I) ^ (1 / 2 : ℂ)) ^ n)) *
          (((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele t * u.2) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt u.2) := by
    intro u
    rw [rationalAdeleScaledFourierChar_eq_real_mul_finite t u,
      RationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianDual_eq_real_mul_finiteAt
        L hb u,
      RationalQuadraticSpaceMatrix.polarRealGaussianFourierProduct_zero]
    simp only [RationalQuadraticSpaceMatrix.rationalAdeleRealScalar]
    ring
  rw [rationalAdeleAddHaarMeasure_eq_prod,
    integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact integral_prod_mul
    (fun w : RationalInfiniteAdele =>
      ((rationalInfiniteAdeleFourierChar
          (algebraMap ℚ RationalInfiniteAdele t * w) : Circle) : ℂ) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / (b - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
            Complex.I) ^ (1 / 2 : ℂ)) ^ n))
    (fun y : RationalFiniteAdele =>
      ((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele t * y) : Circle) : ℂ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt y)

/-- The Poisson exponential at `r / N`, as the finite character at a rational point. -/
theorem fourier_coe_div_eq_fourierChar_inv (k : ℤ) (r : ℚ) (N : ℕ) :
    fourier k ((((r : ℝ) / (N : ℝ) : ℝ)) : UnitAddCircle) =
      (((Real.fourierChar ((-((k : ℚ) / N) * r : ℚ) : ℝ))⁻¹ : Circle) : ℂ) := by
  rw [fourier_coe_apply, Circle.coe_inv, Real.fourierChar_apply, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The dual value density vanishes unless `b N ∈ ℤ`. -/
theorem complexValueFourierDensity_polarGaussianDual_eq_zero_of_not_int (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) {b : ℚ} (hb : b * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b) = 0 := by
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_polarGaussianDual_eq_real_mul_finite
      (by simpa using hc) (-b),
    L.integral_dualFiniteLocal_eq_zero_of_not_int, mul_zero]
  rintro ⟨j, hj⟩
  exact hb ⟨-j, by push_cast at hj ⊢; linarith⟩

/-- The dual value density at `k / N` is the archimedean Fourier transform times the dual finite
character sum. -/
theorem complexValueFourierDensity_polarGaussianDual_div_eq (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hrank : 5 ≤ n) (k : ℤ) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))
        (algebraMap ℚ RationalAdele ((k : ℚ) / L.dualGaussPeriod)) =
      𝓕 (L.polarArchimedeanBruhatFactor c) ((k : ℝ) / (L.dualGaussPeriod : ℝ)) *
        (((L.dualGaussPeriod : ℂ))⁻¹ * ∑' r : RationalPeriodRep L.dualGaussPeriod,
          fourier k ((((r.1 : ℝ) / (L.dualGaussPeriod : ℝ) : ℝ)) : UnitAddCircle) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1) := by
  have hN : (L.dualGaussPeriod : ℚ) ≠ 0 := by exact_mod_cast L.dualGaussPeriod_ne_zero
  have hint : (-((k : ℚ) / L.dualGaussPeriod)) * (L.dualGaussPeriod : ℚ) ∈
      (algebraMap ℤ ℚ).range := ⟨-k, by rw [neg_mul, div_mul_cancel₀ _ hN]; simp⟩
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_polarGaussianDual_eq_real_mul_finite
      (by simpa using hc) (-((k : ℚ) / L.dualGaussPeriod)),
    L.integral_dualFiniteLocal_eq_tsum_of_int hrank hint,
    integral_archimedeanLocal_eq_real, fourier_polarArchimedeanBruhatFactor_eq_integral]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    push_cast
    rfl
  · congr 1
    refine tsum_congr fun r ↦ ?_
    rw [fourier_coe_div_eq_fourierChar_inv]

/-! ## The canonical splitting `ℚ ≃ (ℚ ∩ [0,N)) × ℤ` and the assembly -/

/-- The canonical splitting `t = N fract(t/N) + N ⌊t/N⌋`. -/
def rationalPeriodFloorEquiv {N : ℕ} (hN : N ≠ 0) : ℚ ≃ RationalPeriodRep N × ℤ where
  toFun t := (⟨(N : ℚ) * Int.fract (t / N),
      mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg _),
      by
        have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
        calc (N : ℚ) * Int.fract (t / N) < (N : ℚ) * 1 :=
              mul_lt_mul_of_pos_left (Int.fract_lt_one _) hNpos
          _ = N := mul_one _⟩, ⌊t / N⌋)
  invFun p := p.1.1 + N * p.2
  left_inv t := by
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    change (N : ℚ) * Int.fract (t / N) + N * (⌊t / N⌋ : ℚ) = t
    rw [← mul_add, Int.fract_add_floor, mul_div_cancel₀ _ hNq]
  right_inv := by
    rintro ⟨⟨r, hr0, hrN⟩, m⟩
    have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hdiv : (r + N * m) / N = r / N + m := by field_simp
    have hmem : 0 ≤ r / N ∧ r / N < 1 :=
      ⟨div_nonneg hr0 hNpos.le, (div_lt_one hNpos).2 hrN⟩
    have hfr : Int.fract (r / N) = r / N := Int.fract_eq_self.2 hmem
    have hfl : ⌊r / N⌋ = 0 := Int.floor_eq_zero_iff.2 hmem
    refine Prod.ext (Subtype.ext ?_) ?_
    · change (N : ℚ) * Int.fract ((r + N * m) / N) = r
      rw [hdiv, Int.fract_add_intCast, hfr, mul_div_cancel₀ _ hNpos.ne']
    · change ⌊(r + N * m) / N⌋ = m
      rw [hdiv, Int.floor_add_intCast, hfl, zero_add]

set_option maxHeartbeats 1000000 in
/-- Rank-one adelic Poisson summation for the dual Bruhat family:
`∑_{t ∈ ℚ} B_Ψ(t) = ∑_{k ∈ ℤ} d_Ψ(k / N)`. -/
theorem tsum_bruhat_polarGaussianDual_eq_tsum_int_density (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hrank : 5 ≤ n) :
    (∑' t : ℚ, L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) t) =
      ∑' k : ℤ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))
        (algebraMap ℚ RationalAdele ((k : ℚ) / L.dualGaussPeriod)) := by
  have hn3 : 3 ≤ n := by omega
  set N := L.dualGaussPeriod with hNdef
  have hN : N ≠ 0 := L.dualGaussPeriod_ne_zero
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set A := L.polarArchimedeanBruhatFactor c with hAdef
  set G : ℚ → ℂ := fun t ↦
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t with hGdef
  set B : ℚ → ℂ := fun t ↦ L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
    (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) t with hBdef
  have hB : ∀ t, B t = A (t : ℝ) * G t := fun t ↦
    L.rationalAdeleRankOneBruhatCoefficient_polarGaussianDual_eq_archimedean_mul hc t
  have hsumB : Summable B := L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianDual hc hrank
  have hsumG := L.summable_norm_dualGaussIntegral_periodRep hrank
  have hsumF : Summable fun k : ℤ ↦ ‖((N : ℂ))⁻¹ * 𝓕 A ((k : ℝ) / (N : ℝ))‖ := by
    refine (((L.summable_norm_fourier_polarArchimedeanBruhatFactor_mul hc hn3
      (inv_pos.2 hNpos)).mul_left ‖((N : ℂ))⁻¹‖)).congr fun k ↦ ?_
    rw [norm_mul, div_eq_mul_inv]
  have hsplit : ∑' t : ℚ, B t =
      ∑' r : RationalPeriodRep N, ∑' m : ℤ, B (r.1 + N * m) := by
    rw [← (rationalPeriodFloorEquiv hN).symm.tsum_eq B]
    exact ((rationalPeriodFloorEquiv hN).symm.summable_iff.2 hsumB).tsum_prod
  have hinner : ∀ r : RationalPeriodRep N, ∑' m : ℤ, B (r.1 + N * m) =
      ∑' k : ℤ, (((N : ℂ))⁻¹ * 𝓕 A ((k : ℝ) / (N : ℝ))) *
        fourier k ((((r.1 : ℝ) / (N : ℝ) : ℝ)) : UnitAddCircle) * G r.1 := by
    intro r
    have hper : ∀ m : ℤ, B (r.1 + N * m) = A ((r.1 : ℝ) + (N : ℝ) * m) * G r.1 := by
      intro m
      rw [hB]
      congr 1
      · push_cast; rfl
      · change L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt
            (algebraMap ℚ RationalFiniteAdele (r.1 + N * m)) =
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt
            (algebraMap ℚ RationalFiniteAdele r.1)
        rw [map_add, map_mul]
        exact RationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegralAt_add_period
          L _ _ (algebraMap_intCast_mem_integralFiniteAdeleSubring m)
    simp_rw [hper]
    rw [tsum_mul_right, L.tsum_polarArchimedeanBruhatFactor_add_mul_int hc hn3 hNpos,
      tsum_mul_right]
    simp only [Complex.ofReal_natCast]
    rfl
  rw [hsplit, tsum_congr hinner]
  have hnorm : ∀ (r : RationalPeriodRep N) (k : ℤ),
      ‖(((N : ℂ))⁻¹ * 𝓕 A ((k : ℝ) / (N : ℝ))) *
          fourier k ((((r.1 : ℝ) / (N : ℝ) : ℝ)) : UnitAddCircle) * G r.1‖ =
        ‖G r.1‖ * ‖((N : ℂ))⁻¹ * 𝓕 A ((k : ℝ) / (N : ℝ))‖ := by
    intro r k
    rw [norm_mul, norm_mul, fourier_coe_div_eq_fourierChar_inv, Circle.norm_coe, mul_one, mul_comm]
  have hsum2 : Summable (Function.uncurry fun (r : RationalPeriodRep N) (k : ℤ) ↦
      (((N : ℂ))⁻¹ * 𝓕 A ((k : ℝ) / (N : ℝ))) *
        fourier k ((((r.1 : ℝ) / (N : ℝ) : ℝ)) : UnitAddCircle) * G r.1) := by
    refine Summable.of_norm_bounded
      (hsumG.mul_of_nonneg hsumF (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)) ?_
    rintro ⟨r, k⟩
    exact le_of_eq (hnorm r k)
  rw [← hsum2.tsum_comm]
  refine tsum_congr fun k ↦ ?_
  rw [L.complexValueFourierDensity_polarGaussianDual_div_eq hc hrank k, ← tsum_mul_left,
    ← tsum_mul_left]
  refine tsum_congr fun r ↦ ?_
  ring

/-- The dual value densities are supported on `N⁻¹ ℤ`: the integer sum is the full rational sum. -/
theorem tsum_int_density_polarGaussianDual_eq_tsum_rat (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) :
    (∑' k : ℤ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))
        (algebraMap ℚ RationalAdele ((k : ℚ) / L.dualGaussPeriod))) =
      ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b) := by
  have hN : (L.dualGaussPeriod : ℚ) ≠ 0 := by exact_mod_cast L.dualGaussPeriod_ne_zero
  set D : ℚ → ℂ := fun b ↦ L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
    (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b)
    with hDdef
  change ∑' k : ℤ, D ((k : ℚ) / L.dualGaussPeriod) = ∑' b : ℚ, D b
  refine Function.Injective.tsum_eq (g := fun k : ℤ ↦ (k : ℚ) / L.dualGaussPeriod) ?_ ?_
  · intro j k hjk
    have : (j : ℚ) = k := by
      have h := hjk
      simp only at h
      field_simp at h
      exact h
    exact_mod_cast this
  · intro b hb
    by_contra hnot
    have hb' : b * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range := by
      rintro ⟨j, hj⟩
      exact hnot ⟨j, by
        change (algebraMap ℤ ℚ j) = b * L.dualGaussPeriod at hj
        change (j : ℚ) / L.dualGaussPeriod = b
        rw [show (algebraMap ℤ ℚ j) = (j : ℚ) from rfl] at hj
        rw [hj]
        field_simp⟩
    exact hb (L.complexValueFourierDensity_polarGaussianDual_eq_zero_of_not_int hc hb')

/-- The dual Eisenstein aggregate at the identity: `E(Ψ) = Ψ(0) + ∑_{b ∈ ℚ} d_Ψ(b)`. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianDual_eq_zero_add_tsum_density
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelFunctional
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))
        (L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianDual hc hrank) =
      rationalAdeleVectorPolarGaussianDualTest L (c : ℂ) 0 +
        ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
          (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b) := by
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum,
    L.tsum_bruhat_polarGaussianDual_eq_tsum_int_density hc hrank,
    L.tsum_int_density_polarGaussianDual_eq_tsum_rat hc]

/-- The Weyl form: the standard Eisenstein functional at scale `c⁻¹` equals the explicit
nonzero constant times the dual aggregate at scale `c`. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_inv_eq_const_mul_dual
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice (inv_pos.2 hc) hrank =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ) 0 +
          ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
            (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b)) := by
  rw [← L.rationalAdeleRankOneEisensteinSiegelFunctional_weyl_polarGaussianLattice
      (inv_pos.2 hc) hrank,
    RationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum,
    L.rationalAdeleRankOneWeylOperator_polarGaussianLattice_inv_eq_const_mul_dual hc,
    ← L.tsum_int_density_polarGaussianDual_eq_tsum_rat hc,
    ← L.tsum_bruhat_polarGaussianDual_eq_tsum_int_density hc hrank]
  simp_rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient_const_mul]
  rw [tsum_mul_left, mul_add]

/-- The dual value densities are absolutely summable over `ℚ`. -/
theorem summable_norm_complexValueFourierDensity_polarGaussianDual (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    Summable fun b : ℚ ↦ ‖L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b)‖ := by
  have hn3 : 3 ≤ n := by omega
  have hNq : (L.dualGaussPeriod : ℚ) ≠ 0 := by exact_mod_cast L.dualGaussPeriod_ne_zero
  have hNpos : (0 : ℝ) < L.dualGaussPeriod := by
    exact_mod_cast Nat.pos_of_ne_zero L.dualGaussPeriod_ne_zero
  have hsumG := L.summable_norm_dualGaussIntegral_periodRep hrank
  have hsumF := L.summable_norm_fourier_polarArchimedeanBruhatFactor_mul hc hn3 (inv_pos.2 hNpos)
  set S : ℝ := ‖((L.dualGaussPeriod : ℂ))⁻¹‖ * ∑' r : RationalPeriodRep L.dualGaussPeriod,
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1‖ with hSdef
  have hint : Summable fun k : ℤ ↦ ‖L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
      (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ))
      (algebraMap ℚ RationalAdele ((k : ℚ) / L.dualGaussPeriod))‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) (hsumF.mul_right S)
    rw [L.complexValueFourierDensity_polarGaussianDual_div_eq hc hrank k, norm_mul,
      ← div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, hSdef]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hterm : ∀ r : RationalPeriodRep L.dualGaussPeriod,
        ‖fourier k ((((r.1 : ℝ) / (L.dualGaussPeriod : ℝ) : ℝ)) : UnitAddCircle) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1‖ =
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral r.1‖ := by
      intro r
      rw [norm_mul, fourier_coe_div_eq_fourierChar_inv, Circle.norm_coe, one_mul]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hterm))
    exact hsumG.congr fun r ↦ (hterm r).symm
  have hinj : Function.Injective fun k : ℤ ↦ (k : ℚ) / L.dualGaussPeriod := by
    intro j k hjk
    have : (j : ℚ) = k := by
      have h := hjk
      simp only at h
      field_simp at h
      exact h
    exact_mod_cast this
  refine (hinj.summable_iff ?_).1 hint
  intro b hb
  have hb' : b * (L.dualGaussPeriod : ℚ) ∉ (algebraMap ℤ ℚ).range := by
    rintro ⟨j, hj⟩
    refine hb ⟨j, ?_⟩
    change (j : ℚ) / L.dualGaussPeriod = b
    rw [show (algebraMap ℤ ℚ j) = (j : ℚ) from rfl] at hj
    rw [hj]
    field_simp
  rw [L.complexValueFourierDensity_polarGaussianDual_eq_zero_of_not_int hc hb', norm_zero]

/-- The Eisenstein-side aggregate relation `1 + S_Φ = C (1 + S_Ψ)`: for the standard test at scale
`c⁻¹` and the dual test at scale `c`,
`Φ(0) + ∑_b d_Φ(b) = C · (Ψ(0) + ∑_b d_Ψ(b))`, `C = detScale⁻¹ (1/√(c⁻¹))^n`. -/
theorem polarGaussianLattice_aggregate_eq_const_mul_dual_aggregate (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    rationalAdeleVectorPolarGaussianLatticeTest L ((c⁻¹ : ℝ) : ℂ) 0 +
        ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
          (rationalAdeleVectorPolarGaussianLatticeTest L ((c⁻¹ : ℝ) : ℂ))
          (algebraMap ℚ RationalAdele b) =
      ((L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / ((c⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ n) *
        (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ) 0 +
          ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
            (rationalAdeleVectorPolarGaussianDualTest L (c : ℂ)) (algebraMap ℚ RationalAdele b)) := by
  rw [← L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_eq_zero_add_tsum_density
      (inv_pos.2 hc) hrank,
    L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_inv_eq_const_mul_dual
      hc hrank]

end PositiveDefiniteIntegralLattice
