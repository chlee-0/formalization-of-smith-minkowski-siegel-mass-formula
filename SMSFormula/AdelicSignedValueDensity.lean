import SMSFormula.ValueDensityTracePositivity
import SMSFormula.AdelicGeneratorL1
import SMSFormula.PolarGaussianQuadraticIdentification

/-!
# Signed value densities on the admissible Gaussian core

The positive pushforward identity does not directly supply the signed set-integral
identity needed for trace positivity. We keep the same Fourier density and Haar,
first read the positive measure identity as a real integral identity, and then use
linearity with integrability on both sides. This is an identity on the value line,
not a shell measure.
-/

noncomputable section
open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance
variable {n : ℕ}

/-- The real part of the existing density for a real test. -/
abbrev realValueDensity (V : RationalQuadraticSpaceMatrix n)
    (f : (Fin n → RationalAdele) → ℝ) : RationalAdele → ℝ :=
  fun a ↦ (V.complexValueFourierDensity (fun x ↦ (f x : ℂ)) a).re

theorem continuous_realValueDensity (V : RationalQuadraticSpaceMatrix n)
    {f : (Fin n → RationalAdele) → ℝ}
    (hf : V.IsAdelicBruhatL1 (fun x ↦ (f x : ℂ))) :
    Continuous (V.realValueDensity f) :=
  Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous
    continuous_rationalAdeleFourierChar
    (by change Continuous (fun p : RationalAdele × RationalAdele ↦ p.1 * p.2); fun_prop) hf.2)

/-- All the analytic data needed by the signed trace argument, for the actual
value map, actual Fourier density and unchanged coordinate/scalar Haars. -/
def HasSignedValueDensity (V : RationalQuadraticSpaceMatrix n)
    (f : (Fin n → RationalAdele) → ℝ) : Prop :=
  V.IsAdelicBruhatL1 (fun x ↦ (f x : ℂ)) ∧
  Integrable (V.realValueDensity f) rationalAdeleAddHaarMeasure ∧
  ∀ s : Set RationalAdele, MeasurableSet s →
    (∫ x in V.fullAdelicQuadraticFormValue ⁻¹' s, f x
      ∂rationalAdeleCoordinateAddHaarMeasure n) =
    ∫ a in s, V.realValueDensity f a ∂rationalAdeleAddHaarMeasure

/-- The positive measure identity supplies every measurable-set integral,
including sets of infinite scalar Haar measure. Finiteness comes from the test. -/
theorem hasSignedValueDensity_of_nonneg (V : RationalQuadraticSpaceMatrix n)
    {f : (Fin n → RationalAdele) → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hf : V.IsAdelicBruhatL1 (fun x ↦ (f x : ℂ))) : V.HasSignedValueDensity f := by
  let F := fun x ↦ ENNReal.ofReal (f x)
  have hF : toComplexTest F = fun x ↦ (f x : ℂ) := by
    funext x
    simp [F, toComplexTest, ENNReal.toReal_ofReal (hn x)]
  have hc : V.IsAdelicBruhatL1 (toComplexTest F) := hF.symm ▸ hf
  have hd : V.valueFourierDensity F = V.complexValueFourierDensity (fun x ↦ (f x : ℂ)) := by
    change V.complexValueFourierDensity (toComplexTest F) = _
    rw [hF]
  have hpos : ∀ a, 0 ≤ V.realValueDensity f a := by
    intro a
    simpa only [hd] using
      (V.valueFourierDensity_real_nonnegative (Phi := F) hm.ennreal_ofReal
        (fun _ ↦ ENNReal.ofReal_ne_top) hc a).2
  have hint : Integrable (V.realValueDensity f) rationalAdeleAddHaarMeasure := by
    simpa only [hd] using
      (V.integrable_valueFourierDensity (Phi := F) hm.ennreal_ofReal
        (fun _ ↦ ENNReal.ofReal_ne_top) hc).re
  refine ⟨hf, hint, ?_⟩
  intro s hs
  have heq := congrArg (fun m : Measure RationalAdele ↦ m s)
    (V.valuePushforward_eq_withDensity (Phi := F) hm.ennreal_ofReal
      (fun _ ↦ ENNReal.ofReal_ne_top) hc)
  dsimp only at heq
  rw [valuePushforward, Measure.map_apply V.continuous_fullAdelicQuadraticFormValue.measurable hs,
    withDensity_apply _ (hs.preimage V.continuous_fullAdelicQuadraticFormValue.measurable),
    withDensity_apply _ hs] at heq
  have hfint : Integrable f (rationalAdeleCoordinateAddHaarMeasure n) := by
    simpa using hf.1.re
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn)
      hfint.restrict.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
      hint.restrict.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (by simpa only [F, hd] using heq)

theorem realValueDensity_add (V : RationalQuadraticSpaceMatrix n)
    {f g : (Fin n → RationalAdele) → ℝ}
    (hf : V.IsAdelicBruhatL1 (fun x ↦ (f x : ℂ)))
    (hg : V.IsAdelicBruhatL1 (fun x ↦ (g x : ℂ))) :
    V.realValueDensity (f + g) = V.realValueDensity f + V.realValueDensity g := by
  have h : (fun x ↦ ((f + g) x : ℂ)) =
      (fun x ↦ (f x : ℂ)) + (fun x ↦ (g x : ℂ)) := by ext x; simp
  funext a
  change (V.complexValueFourierDensity (fun x ↦ ((f + g) x : ℂ)) a).re = _
  rw [h, V.re_complexValueFourierDensity_add hf hg]
  rfl

theorem realValueDensity_smul (V : RationalQuadraticSpaceMatrix n) (c : ℝ)
    (f : (Fin n → RationalAdele) → ℝ) :
    V.realValueDensity (c • f) = c • V.realValueDensity f := by
  have h : (fun x ↦ ((c • f) x : ℂ)) = (c : ℂ) • (fun x ↦ (f x : ℂ)) := by
    ext x; simp
  funext a
  change (V.complexValueFourierDensity (fun x ↦ ((c • f) x : ℂ)) a).re = _
  rw [h, V.re_complexValueFourierDensity_real_smul]
  rfl

theorem HasSignedValueDensity.add {V : RationalQuadraticSpaceMatrix n}
    {f g : (Fin n → RationalAdele) → ℝ}
    (hf : V.HasSignedValueDensity f) (hg : V.HasSignedValueDensity g) :
    V.HasSignedValueDensity (f + g) := by
  have hclass : V.IsAdelicBruhatL1 (fun x ↦ ((f + g) x : ℂ)) := by
    simpa using hf.1.add hg.1
  refine ⟨hclass, ?_, ?_⟩
  · rw [V.realValueDensity_add hf.1 hg.1]; exact hf.2.1.add hg.2.1
  · intro s hs
    have hfi : Integrable f (rationalAdeleCoordinateAddHaarMeasure n) := by simpa using hf.1.1.re
    have hgi : Integrable g (rationalAdeleCoordinateAddHaarMeasure n) := by simpa using hg.1.1.re
    rw [V.realValueDensity_add hf.1 hg.1]
    simp only [Pi.add_apply]
    rw [integral_add hfi.restrict hgi.restrict,
      integral_add hf.2.1.restrict hg.2.1.restrict, hf.2.2 s hs, hg.2.2 s hs]

theorem HasSignedValueDensity.smul {V : RationalQuadraticSpaceMatrix n}
    {f : (Fin n → RationalAdele) → ℝ} (hf : V.HasSignedValueDensity f) (c : ℝ) :
    V.HasSignedValueDensity (c • f) := by
  have hclass : V.IsAdelicBruhatL1 (fun x ↦ ((c • f) x : ℂ)) := by
    simpa using hf.1.const_smul (c : ℂ)
  refine ⟨hclass, ?_, ?_⟩
  · rw [V.realValueDensity_smul]; exact hf.2.1.smul c
  · intro s hs
    rw [V.realValueDensity_smul]
    change (∫ x in V.fullAdelicQuadraticFormValue ⁻¹' s, c * f x
      ∂rationalAdeleCoordinateAddHaarMeasure n) =
      ∫ a in s, c * V.realValueDensity f a ∂rationalAdeleAddHaarMeasure
    rw [integral_const_mul, integral_const_mul, hf.2.2 s hs]

/-- A nonnegative admissible majorant gives a signed test its density identity.
No positive-part admissibility is assumed or inferred from an L1 norm bound. -/
theorem hasSignedValueDensity_of_majorant (V : RationalQuadraticSpaceMatrix n)
    {f h : (Fin n → RationalAdele) → ℝ} (hfm : Measurable f) (hhm : Measurable h)
    (hf : V.IsAdelicBruhatL1 (fun x ↦ (f x : ℂ)))
    (hh : V.IsAdelicBruhatL1 (fun x ↦ (h x : ℂ)))
    (hhpos : ∀ x, 0 ≤ h x) (hdom : ∀ x, -h x ≤ f x) :
    V.HasSignedValueDensity f := by
  have hsum : V.IsAdelicBruhatL1 (fun x ↦ ((f + h) x : ℂ)) := by simpa using hf.add hh
  have hp := V.hasSignedValueDensity_of_nonneg (hfm.add hhm)
    (fun x ↦ by have := hdom x; change 0 ≤ f x + h x; linarith) hsum
  have hm := (V.hasSignedValueDensity_of_nonneg hhm hhpos hh).smul (-1)
  have heq : (f + h) + (-1 : ℝ) • h = f := by ext x; simp
  exact heq ▸ hp.add hm

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
open MeasureTheory RationalQuadraticSpaceMatrix
variable {n : ℕ}

/-- A signed finite factor needs no new frequency estimate: its absolute value
has exactly the same carrier and period, and hence the same admissibility theorem.
This supplies the positive decomposition for the actual shifted generator. -/
theorem hasSignedValueDensity_shiftedGaussian (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (u : Fin n → ℝ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℝ}
    (hcar : IsStandardCarried c (fun y ↦ (g y : ℂ)))
    (hper : IsStandardPeriodic d (fun y ↦ (g y : ℂ))) :
    L.rationalQuadraticSpaceMatrix.HasSignedValueDensity
      (fun x ↦ (polarRealGaussian L (b : ℂ) (rationalAdeleVectorRealPart n x - u)).re *
        g (rationalAdeleVectorFinitePart n x)) := by
  let G := fun x ↦ (polarRealGaussian L (b : ℂ) (rationalAdeleVectorRealPart n x - u)).re
  have hG : ∀ x, (G x : ℂ) =
      polarRealGaussian L (b : ℂ) (rationalAdeleVectorRealPart n x - u) := by
    intro x
    dsimp only [G]
    rw [polarRealGaussian_eq_quadraticShiftedGaussian]
    rfl
  have hGpos : ∀ x, 0 ≤ G x := by
    intro x
    dsimp only [G]
    rw [polarRealGaussian_eq_quadraticShiftedGaussian]
    exact (Real.exp_pos _).le
  have hGcont : Continuous G := by
    have hpol : Continuous (polarRealGaussian L (b : ℂ)) :=
      (continuous_realCoordinateGaussian n (b : ℂ)).comp
        (Matrix.toLin' L.polarRealSqrtMatrix).continuous_of_finiteDimensional
    apply Complex.continuous_re.comp (hpol.comp ?_)
    unfold rationalAdeleVectorRealPart
    fun_prop
  have hgcont : Continuous g := by simpa using Complex.continuous_re.comp (hper.continuous hd)
  have hgfin : Continuous (rationalAdeleVectorFinitePart n) := by
    unfold rationalAdeleVectorFinitePart
    fun_prop
  have hcarabs : IsStandardCarried c (fun y ↦ ((|g y| : ℝ) : ℂ)) := by
    intro y hy
    have hz : g y = 0 := Complex.ofReal_eq_zero.mp (hcar y hy)
    simp [hz]
  have hperabs : IsStandardPeriodic d (fun y ↦ ((|g y| : ℝ) : ℂ)) := by
    intro y z hz
    have heq : g (y + d • z) = g y := Complex.ofReal_injective (hper y z hz)
    exact congrArg (fun r : ℝ ↦ ((|r| : ℝ) : ℂ)) heq
  have hfclass := isAdelicBruhatL1_shiftedGaussianGenerator L hn hb u hc hd hcar hper
  have hhclass := isAdelicBruhatL1_shiftedGaussianGenerator L hn hb u hc hd hcarabs hperabs
  have hf : L.rationalQuadraticSpaceMatrix.IsAdelicBruhatL1
      (fun x ↦ ((G x * g (rationalAdeleVectorFinitePart n x) : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_mul, hG] using hfclass
  have hh : L.rationalQuadraticSpaceMatrix.IsAdelicBruhatL1
      (fun x ↦ ((G x * |g (rationalAdeleVectorFinitePart n x)| : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_mul, hG] using hhclass
  apply L.rationalQuadraticSpaceMatrix.hasSignedValueDensity_of_majorant
    (hGcont.mul (hgcont.comp hgfin)).measurable
    (hGcont.mul (hgcont.abs.comp hgfin)).measurable hf hh
  · intro x; exact mul_nonneg (hGpos x) (abs_nonneg _)
  · intro x
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (g (rationalAdeleVectorFinitePart n x))) (hGpos x)
    simpa only [mul_neg] using h

/-- Every finite real linear combination of the actual real generators has a
signed value density. This is the real coefficient core, not an assertion that
an arbitrary measurable modification has the same trace. -/
theorem hasSignedValueDensity_of_mem_real_span (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) {f : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ Submodule.span ℝ {f | ∃ (u : Fin n → ℝ) (c d : ℕ)
      (g : (Fin n → RationalFiniteAdele) → ℝ), c ≠ 0 ∧ d ≠ 0 ∧
      IsStandardCarried c (fun y ↦ (g y : ℂ)) ∧ IsStandardPeriodic d (fun y ↦ (g y : ℂ)) ∧
      f = fun x ↦ (polarRealGaussian L (b : ℂ) (rationalAdeleVectorRealPart n x - u)).re *
        g (rationalAdeleVectorFinitePart n x)}) :
    L.rationalQuadraticSpaceMatrix.HasSignedValueDensity f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u,c,d,g,hc,hd,hcar,hper,rfl⟩ := hf
    exact hasSignedValueDensity_shiftedGaussian L hn hb u hc hd hcar hper
  | zero =>
    have h := hasSignedValueDensity_shiftedGaussian L hn hb (0 : Fin n → ℝ)
      one_ne_zero one_ne_zero (g := 0) (fun _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    simpa using h
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.smul c

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace RationalQuadraticSpaceMatrix
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance
variable {n : ℕ}

/-- Positivity now follows from the signed set-integral law itself; no separate
ENNReal presentation of the auxiliary test is needed. -/
theorem HasSignedValueDensity.nonneg {V : RationalQuadraticSpaceMatrix n}
    {f : (Fin n → RationalAdele) → ℝ} (hf : V.HasSignedValueDensity f)
    (hpos : ∀ x, 0 ≤ f x) (a : RationalAdele) : 0 ≤ V.realValueDensity f a := by
  exact SMSFormula.TracePositivity.density_nonneg_on_open_of_nonneg_on_preimage
    V.continuous_fullAdelicQuadraticFormValue.measurable
    (V.continuous_realValueDensity hf.1) hf.2.2 isOpen_univ
    (fun x _ ↦ hpos x) (Set.mem_univ a)

/-- The trace-positivity mechanism on the actual adelic test and density.
The signed pushforward identity, density continuity and auxiliary density sign
are discharged here. The geometric compact-bad-set input remains explicit. -/
theorem realValueDensity_nonneg_of_compact_bad_sets (V : RationalQuadraticSpaceMatrix n)
    {f h : (Fin n → RationalAdele) → ℝ} (hf : V.HasSignedValueDensity f)
    (hh : V.HasSignedValueDensity h) (hhpos : ∀ x, 0 ≤ h x) (a : RationalAdele)
    (hbad : ∀ ε : ℝ, 0 < ε → ∃ C : Set (Fin n → RationalAdele),
      IsCompact C ∧ Disjoint C (V.fullAdelicQuadraticFormValue ⁻¹' {a}) ∧
      {x | f x + ε * h x < 0} ⊆ C) : 0 ≤ V.realValueDensity f a := by
  refine SMSFormula.TracePositivity.density_nonneg_of_trace_nonneg_of_compact_bad_set
    (μ := rationalAdeleCoordinateAddHaarMeasure n) (ν := rationalAdeleAddHaarMeasure)
    V.continuous_fullAdelicQuadraticFormValue
    V.continuous_fullAdelicQuadraticFormValue.measurable
    (V.continuous_realValueDensity hf.1) (V.continuous_realValueDensity hh.1)
    ?_ (hh.nonneg hhpos a) hbad
  intro c s hs
  have heq := (hf.add (hh.smul c)).2.2 s hs
  rw [V.realValueDensity_add hf.1 (hh.smul c).1, V.realValueDensity_smul] at heq
  exact heq

/-- Running the actual signed argument on both signs annihilates the density.
This removes the abstract pushforward hypotheses from the trace-zero bridge. -/
theorem realValueDensity_eq_zero_of_compact_bad_sets (V : RationalQuadraticSpaceMatrix n)
    {f h : (Fin n → RationalAdele) → ℝ} (hf : V.HasSignedValueDensity f)
    (hh : V.HasSignedValueDensity h) (hhpos : ∀ x, 0 ≤ h x) (a : RationalAdele)
    (hbad : ∀ ε : ℝ, 0 < ε → ∃ C : Set (Fin n → RationalAdele),
      IsCompact C ∧ Disjoint C (V.fullAdelicQuadraticFormValue ⁻¹' {a}) ∧
      {x | f x + ε * h x < 0} ⊆ C)
    (hbadneg : ∀ ε : ℝ, 0 < ε → ∃ C : Set (Fin n → RationalAdele),
      IsCompact C ∧ Disjoint C (V.fullAdelicQuadraticFormValue ⁻¹' {a}) ∧
      {x | -f x + ε * h x < 0} ⊆ C) : V.realValueDensity f a = 0 := by
  have hp := V.realValueDensity_nonneg_of_compact_bad_sets hf hh hhpos a hbad
  have hm := V.realValueDensity_nonneg_of_compact_bad_sets (hf.smul (-1)) hh hhpos a
    (by simpa using hbadneg)
  rw [V.realValueDensity_smul] at hm
  change 0 ≤ -1 * V.realValueDensity f a at hm
  linarith

end RationalQuadraticSpaceMatrix
