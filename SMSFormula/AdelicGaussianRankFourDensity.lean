import SMSFormula.RationalQuadraticRealOrbitAverage
import SMSFormula.RationalAdeleStandardFactorTubeLimit
import SMSFormula.AdelicGaussianCapstoneSimpleInputs

/-!
# The rank-four density D⁴ on the Gaussian core

For a supplied real point `x₀` (for the shell identity: the integral representative `z`), a
nonzero integer `M` and a scalar `c_∞`, every member `f` of the real Gaussian core has

* real sections `x_∞ ↦ f(x_∞, x_f)` that are continuous and bounded (`coreSectionRegular_of_mem`);
* a finite section average `φ_f(x_f) = A_{x₀}(x_∞ ↦ f(x_∞, x_f))` (measure real orbit average) that is
  a standard carried periodic finite factor (`exists_standard_finiteSectionAverage`), additive and
  homogeneous in `f`;
* hence, in lattice rank at least four, a convergent k!-tube mass `T_{k!}(φ_f)(M)`
  (`tendsto_rankFourFiniteDensity`, from `RationalAdeleStandardFactorTubeLimit`).

`rankFourDensityLinearMap` is `f ↦ c_∞ · Re lim_k T_{k!}(φ_f)(M)`, a linear map on the core. Its
trace positivity, invariance and unit laws are proved in `AdelicGaussianRankFourDensityPositivity`,
`AdelicGaussianRankFourDensityInvariance` and `AdelicGaussianRankFourDensityUnitLaws`. Nothing is
chosen: `x₀`, `M` and `c_∞` are supplied.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-! ## The real–finite join -/

/-- The adelic vector with real part `xr` and finite part `xf`. -/
def rationalAdeleVectorJoin (n : ℕ) (xr : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    Fin n → RationalAdele :=
  (rationalAdeleVectorRealFiniteEquiv n).symm (xr, xf)

theorem rationalAdeleVectorRealFiniteEquiv_join (xr : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    rationalAdeleVectorRealFiniteEquiv n (rationalAdeleVectorJoin n xr xf) = (xr, xf) :=
  (rationalAdeleVectorRealFiniteEquiv n).apply_symm_apply _

@[simp] theorem rationalAdeleVectorRealPart_join (xr : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    rationalAdeleVectorRealPart n (rationalAdeleVectorJoin n xr xf) = xr := by
  have h := rationalAdeleVectorRealFiniteEquiv_join xr xf
  rw [rationalAdeleVectorRealFiniteEquiv_apply] at h
  exact (Prod.ext_iff.1 h).1

@[simp] theorem rationalAdeleVectorFinitePart_join (xr : Fin n → ℝ)
    (xf : Fin n → RationalFiniteAdele) :
    rationalAdeleVectorFinitePart n (rationalAdeleVectorJoin n xr xf) = xf := by
  have h := rationalAdeleVectorRealFiniteEquiv_join xr xf
  rw [rationalAdeleVectorRealFiniteEquiv_apply] at h
  exact (Prod.ext_iff.1 h).2

/-! ## Sections of core tests -/

/-- The polar shifted Gaussian is at most one at a nonnegative width. -/
theorem realShiftedGaussian_le_one (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 ≤ b) (u x : Fin n → ℝ) :
    realShiftedGaussian L b u x ≤ 1 := by
  rw [realShiftedGaussian_eq, SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  refine Real.exp_le_one_iff.2 ?_
  have hQ : 0 ≤ L.polarQuadraticForm (ContinuousMap.id (Fin n → ℝ) x - u) := by
    rw [polarQuadraticForm_apply]
    exact L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.posSemidef.dotProduct_mulVec_nonneg _
  have hpb : 0 ≤ Real.pi * b := mul_nonneg Real.pi_pos.le hb
  nlinarith

/-- Continuity and boundedness of every real section. -/
def CoreSectionRegular (f : (Fin n → RationalAdele) → ℝ) : Prop :=
  ∀ xf : Fin n → RationalFiniteAdele,
    Continuous (fun xr ↦ f (rationalAdeleVectorJoin n xr xf)) ∧
      ∃ C : ℝ, ∀ xr, |f (rationalAdeleVectorJoin n xr xf)| ≤ C

theorem coreSectionRegular_of_mem (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 ≤ b)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) : CoreSectionRegular f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, c, d, g, -, -, -, -, rfl⟩ := hf
    intro xf
    simp only [rationalAdeleVectorRealPart_join, rationalAdeleVectorFinitePart_join]
    refine ⟨(continuous_realShiftedGaussian L b u).mul continuous_const, |g xf|, fun xr ↦ ?_⟩
    rw [abs_mul, abs_of_pos (realShiftedGaussian_pos L b u xr)]
    exact mul_le_of_le_one_left (abs_nonneg _) (realShiftedGaussian_le_one L hb u xr)
  | zero =>
    intro xf
    exact ⟨continuous_const, 0, fun _ ↦ by simp⟩
  | add f g _ _ hf hg =>
    intro xf
    obtain ⟨hfc, C, hC⟩ := hf xf
    obtain ⟨hgc, D, hD⟩ := hg xf
    refine ⟨hfc.add hgc, C + D, fun xr ↦ ?_⟩
    exact (abs_add_le _ _).trans (add_le_add (hC xr) (hD xr))
  | smul r f _ hf =>
    intro xf
    obtain ⟨hfc, C, hC⟩ := hf xf
    refine ⟨continuous_const.mul hfc, |r| * C, fun xr ↦ ?_⟩
    change |r * f _| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC xr) (abs_nonneg r)

/-! ## The finite section average -/

/-- The finite section average `φ_f(x_f) = A_{x₀}(x_∞ ↦ f(x_∞, x_f))`. -/
def finiteSectionAverage (L : PositiveDefiniteIntegralLattice n) (x₀ : Fin n → ℝ)
    (f : (Fin n → RationalAdele) → ℝ) (xf : Fin n → RationalFiniteAdele) : ℝ :=
  L.rationalQuadraticSpaceMatrix.realOrbitAverage x₀ (fun xr ↦ f (rationalAdeleVectorJoin n xr xf))

theorem finiteSectionAverage_add (L : PositiveDefiniteIntegralLattice n) [NeZero n] (x₀ : Fin n → ℝ)
    {f g : (Fin n → RationalAdele) → ℝ} (hf : CoreSectionRegular f) (hg : CoreSectionRegular g)
    (xf : Fin n → RationalFiniteAdele) :
    finiteSectionAverage L x₀ (f + g) xf =
      finiteSectionAverage L x₀ f xf + finiteSectionAverage L x₀ g xf := by
  obtain ⟨hfc, C, hC⟩ := hf xf
  obtain ⟨hgc, D, hD⟩ := hg xf
  exact L.rationalQuadraticSpaceMatrix.realOrbitAverage_add
    L.posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real x₀ hfc hgc hC hD

theorem finiteSectionAverage_smul (L : PositiveDefiniteIntegralLattice n) (x₀ : Fin n → ℝ) (r : ℝ)
    (f : (Fin n → RationalAdele) → ℝ) (xf : Fin n → RationalFiniteAdele) :
    finiteSectionAverage L x₀ (r • f) xf = r * finiteSectionAverage L x₀ f xf :=
  L.rationalQuadraticSpaceMatrix.realOrbitAverage_smul x₀ r _

theorem finiteSectionAverage_zero (L : PositiveDefiniteIntegralLattice n) (x₀ : Fin n → ℝ)
    (xf : Fin n → RationalFiniteAdele) :
    finiteSectionAverage L x₀ 0 xf = 0 := by
  have h := finiteSectionAverage_smul L x₀ 0 0 xf
  rwa [zero_smul, zero_mul] at h

/-- The finite section average of a core test is a standard carried periodic finite factor. -/
theorem exists_standard_finiteSectionAverage (L : PositiveDefiniteIntegralLattice n) [NeZero n] {b : ℝ}
    (hb : 0 ≤ b) (x₀ : Fin n → ℝ) {f : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ realGaussianCore L b) :
    ∃ c d : ℕ, c ≠ 0 ∧ d ≠ 0 ∧
      IsStandardCarried c (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ)) ∧
      IsStandardPeriodic d (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, c, d, g, hc, hd, hcar, hper, rfl⟩ := hf
    have hφ : ∀ xf, finiteSectionAverage L x₀ (fun x ↦ realShiftedGaussian L b u
        (rationalAdeleVectorRealPart n x) * g (rationalAdeleVectorFinitePart n x)) xf =
        g xf * L.rationalQuadraticSpaceMatrix.realOrbitAverage x₀ (realShiftedGaussian L b u) := by
      intro xf
      unfold finiteSectionAverage
      simp only [rationalAdeleVectorRealPart_join, rationalAdeleVectorFinitePart_join]
      rw [← L.rationalQuadraticSpaceMatrix.realOrbitAverage_smul x₀ (g xf)]
      congr 1
      funext xr
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨c, d, hc, hd, fun xf hxf ↦ ?_, fun xf v hv ↦ ?_⟩
    · have h0 := hcar xf hxf
      simp only [Complex.ofReal_eq_zero] at h0 ⊢
      rw [hφ, h0, zero_mul]
    · have h1 := hper xf v hv
      simp only [Complex.ofReal_inj] at h1 ⊢
      rw [hφ, hφ, h1]
  | zero =>
    refine ⟨1, 1, one_ne_zero, one_ne_zero, fun xf _ ↦ ?_, fun xf _ _ ↦ ?_⟩
    · simp [finiteSectionAverage_zero]
    · simp [finiteSectionAverage_zero]
  | add f g hfm hgm hf hg =>
    obtain ⟨c, d, hc, hd, hfc, hfp⟩ := hf
    obtain ⟨c', d', hc', hd', hgc, hgp⟩ := hg
    have hadd : ∀ xf, finiteSectionAverage L x₀ (f + g) xf =
        finiteSectionAverage L x₀ f xf + finiteSectionAverage L x₀ g xf :=
      finiteSectionAverage_add L x₀ (coreSectionRegular_of_mem L hb hfm)
        (coreSectionRegular_of_mem L hb hgm)
    refine ⟨c * c', d * d', mul_ne_zero hc hc', mul_ne_zero hd hd', fun xf hxf ↦ ?_,
      fun xf v hv ↦ ?_⟩
    · have h1 := (hfc.mono (dvd_mul_right c c')) xf hxf
      have h2 := (hgc.mono (dvd_mul_left c' c)) xf hxf
      simp only at h1 h2 ⊢
      rw [hadd, Complex.ofReal_add, h1, h2, add_zero]
    · have h1 := (hfp.mono (dvd_mul_right d d')) xf v hv
      have h2 := (hgp.mono (dvd_mul_left d' d)) xf v hv
      simp only at h1 h2 ⊢
      rw [hadd, hadd, Complex.ofReal_add, Complex.ofReal_add, h1, h2]
  | smul r f _ hf =>
    obtain ⟨c, d, hc, hd, hfc, hfp⟩ := hf
    refine ⟨c, d, hc, hd, fun xf hxf ↦ ?_, fun xf v hv ↦ ?_⟩
    · have h1 := hfc xf hxf
      simp only at h1 ⊢
      rw [finiteSectionAverage_smul, Complex.ofReal_mul, h1, mul_zero]
    · have h1 := hfp xf v hv
      simp only at h1 ⊢
      rw [finiteSectionAverage_smul, finiteSectionAverage_smul, Complex.ofReal_mul,
        Complex.ofReal_mul, h1]

/-! ## Additivity of tube masses -/

theorem integrable_mul_tubeIndicator {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hg : Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (V : RationalQuadraticSpaceMatrix n) (a c : RationalFiniteAdele) :
    Integrable (fun x ↦ g x * rationalFiniteAdeleIntegralIndicator
      (a * (V.finiteAdelicQuadraticFormValue x - c))) (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  refine hg.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (measurable_rationalFiniteAdeleIntegralIndicator.comp
      ((continuous_const.mul ((continuous_finiteAdelicQuadraticFormValue V).sub
        continuous_const)).measurable)).aestronglyMeasurable
  · unfold rationalFiniteAdeleIntegralIndicator
    by_cases h : a * (V.finiteAdelicQuadraticFormValue x - c) ∈
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp

theorem finiteTubeMass_add (L : PositiveDefiniteIntegralLattice n) {g h : (Fin n → RationalFiniteAdele) → ℂ}
    (hg : Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (hh : Integrable h (rationalFiniteAdeleCoordinateAddHaarMeasure n)) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass (fun x ↦ g x + h x) w M = L.finiteTubeMass g w M + L.finiteTubeMass h w M := by
  unfold finiteTubeMass
  simp_rw [add_mul]
  rw [integral_add (integrable_mul_tubeIndicator hg _ _ _) (integrable_mul_tubeIndicator hh _ _ _),
    mul_add]

theorem finiteTubeMass_const_mul (L : PositiveDefiniteIntegralLattice n) (r : ℂ)
    (g : (Fin n → RationalFiniteAdele) → ℂ) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass (fun x ↦ r * g x) w M = r * L.finiteTubeMass g w M := by
  unfold finiteTubeMass
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-! ## The rank-four density -/

/-- The finite limit `lim_k T_{k!}(φ_f)(M)`. -/
def rankFourFiniteDensity (L : PositiveDefiniteIntegralLattice n) (x₀ : Fin n → ℝ) (M : ℤ)
    (f : (Fin n → RationalAdele) → ℝ) : ℂ :=
  limUnder atTop fun k ↦
    L.finiteTubeMass (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ)) (Nat.factorial k) M

theorem integrable_finiteSectionAverage (L : PositiveDefiniteIntegralLattice n) [NeZero n] {b : ℝ} (hb : 0 ≤ b)
    (x₀ : Fin n → ℝ) {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    Integrable (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  obtain ⟨c, d, hc, hd, hcar, hper⟩ := exists_standard_finiteSectionAverage L hb x₀ hf
  exact integrable_of_isStandardCarried_isStandardPeriodic hc hd hcar hper

/-- The finite tube masses of every core test converge (rank at least four, `M ≠ 0`). -/
theorem tendsto_rankFourFiniteDensity (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ}
    (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ)
    {f : (Fin (n + 1) → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    Tendsto (fun k ↦ L.finiteTubeMass (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ))
      (Nat.factorial k) M) atTop (𝓝 (rankFourFiniteDensity L x₀ M f)) := by
  obtain ⟨c, d, hc, hd, hcar, hper⟩ := exists_standard_finiteSectionAverage L hb x₀ hf
  obtain ⟨D, hD⟩ := L.exists_tendsto_finiteTubeMass_factorial hn hM hc hd hcar hper
  exact tendsto_nhds_limUnder ⟨D, hD⟩

/-- The rank-four density as a linear map on the core: `f ↦ c_∞ · Re lim_k T_{k!}(φ_f)(M)`. -/
def rankFourDensityLinearMap (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0)
    {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ) (cInf : ℝ) :
    realGaussianCore L b →ₗ[ℝ] ℝ where
  toFun f := cInf * (rankFourFiniteDensity L x₀ M f.val).re
  map_add' f g := by
    have hsum := (tendsto_rankFourFiniteDensity L hn hM hb x₀ f.property).add
      (tendsto_rankFourFiniteDensity L hn hM hb x₀ g.property)
    have hfg : Tendsto (fun k ↦ L.finiteTubeMass
        (fun xf ↦ (finiteSectionAverage L x₀ (f.val + g.val) xf : ℂ)) (Nat.factorial k) M) atTop
        (𝓝 (rankFourFiniteDensity L x₀ M f.val + rankFourFiniteDensity L x₀ M g.val)) := by
      refine hsum.congr fun k ↦ ?_
      have hadd : (fun xf ↦ (finiteSectionAverage L x₀ (f.val + g.val) xf : ℂ)) =
          fun xf ↦ (finiteSectionAverage L x₀ f.val xf : ℂ) +
            (finiteSectionAverage L x₀ g.val xf : ℂ) := by
        funext xf
        rw [finiteSectionAverage_add L x₀ (coreSectionRegular_of_mem L hb f.property)
          (coreSectionRegular_of_mem L hb g.property), Complex.ofReal_add]
      rw [hadd, finiteTubeMass_add L (integrable_finiteSectionAverage L hb x₀ f.property)
        (integrable_finiteSectionAverage L hb x₀ g.property)]
    have heq := tendsto_nhds_unique
      (tendsto_rankFourFiniteDensity L hn hM hb x₀ (f + g).property) hfg
    rw [Submodule.coe_add] at heq
    change cInf * (rankFourFiniteDensity L x₀ M (f.val + g.val)).re = _
    rw [heq, Complex.add_re, mul_add]
  map_smul' r f := by
    have hsm : Tendsto (fun k ↦ L.finiteTubeMass
        (fun xf ↦ (finiteSectionAverage L x₀ (r • f.val) xf : ℂ)) (Nat.factorial k) M) atTop
        (𝓝 ((r : ℂ) * rankFourFiniteDensity L x₀ M f.val)) := by
      refine ((tendsto_rankFourFiniteDensity L hn hM hb x₀ f.property).const_mul (r : ℂ)).congr
        fun k ↦ ?_
      have hs : (fun xf ↦ (finiteSectionAverage L x₀ (r • f.val) xf : ℂ)) =
          fun xf ↦ (r : ℂ) * (finiteSectionAverage L x₀ f.val xf : ℂ) := by
        funext xf
        rw [finiteSectionAverage_smul, Complex.ofReal_mul]
      rw [hs, finiteTubeMass_const_mul L]
    have heq := tendsto_nhds_unique
      (tendsto_rankFourFiniteDensity L hn hM hb x₀ (r • f).property) hsm
    rw [Submodule.coe_smul] at heq
    change cInf * (rankFourFiniteDensity L x₀ M (r • f.val)).re = r • (cInf * _)
    rw [heq, Complex.re_ofReal_mul, smul_eq_mul]
    ring

theorem rankFourDensityLinearMap_apply (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ}
    (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ) (cInf : ℝ) (f : realGaussianCore L b) :
    rankFourDensityLinearMap L hn hM hb x₀ cInf f = cInf * (rankFourFiniteDensity L x₀ M f.val).re :=
  rfl

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
