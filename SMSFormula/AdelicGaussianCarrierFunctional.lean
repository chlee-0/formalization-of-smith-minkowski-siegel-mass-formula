import SMSFormula.AdelicGaussianFiberCarrier
import SMSFormula.ShellLocalBoundExtension

/-!
# The bounded value-density functional on a literal compact fiber piece

A trace on one piece determines the density of the localized test, not that of
the original test on the whole fiber. The old carrier indicator supplies that
localization. Trace positivity then constructs the positive image functional,
and the explicit shell unit gives its bound. No native mass is evaluated.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- Restriction to the literal fiber intersected with the old finite carrier. -/
def gaussianCarrierTrace (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) (c : ℕ) :
    realGaussianCore L b →ₗ[ℝ] C(adelicFiberCarrier L a c, ℝ) where
  toFun f := ⟨fun x ↦ f.val x.val,
    (continuous_of_mem_realGaussianCore L b f.property).comp continuous_subtype_val⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- The density vanishes if the trace vanishes on the piece, after localization. -/
theorem ker_gaussianCarrierTrace_le_ker_localDensity (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) :
    (gaussianCarrierTrace L b a c).ker ≤
      ((realGaussianDensityLinearMap L hn hb a).comp (localizeGaussianCore L b c)).ker := by
  intro f hf
  apply LinearMap.mem_ker.mpr
  apply realValueDensity_eq_zero_of_trace_zero L hn hb
    (localizeGaussianCore L b c f).property a
  intro x hx
  by_cases hK : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · rw [localizeGaussianCore_on L b c f hK]
    exact congrArg (fun g ↦ g ⟨x, hx, hK⟩) (LinearMap.mem_ker.mp hf)
  · exact localizeGaussianCore_off L b c f hK

/-- The constructed image functional; no choice of ambient extensions. -/
def gaussianCarrierTraceDensity (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) :
    (gaussianCarrierTrace L b a c).range →ₗ[ℝ] ℝ :=
  ((gaussianCarrierTrace L b a c).ker.liftQ
    ((realGaussianDensityLinearMap L hn hb a).comp (localizeGaussianCore L b c))
    (ker_gaussianCarrierTrace_le_ker_localDensity L hn hb a c)).comp
    (gaussianCarrierTrace L b a c).quotKerEquivRange.symm.toLinearMap

/-- Evaluation formula: on the trace of `f`, the density is the real value density of the
localized core `localizeGaussianCore L b c f`. -/
@[simp] theorem gaussianCarrierTraceDensity_apply (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) (f : realGaussianCore L b) :
    gaussianCarrierTraceDensity L hn hb a c ((gaussianCarrierTrace L b a c).rangeRestrict f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity (localizeGaussianCore L b c f).val a := by
  unfold gaussianCarrierTraceDensity
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have heq : (gaussianCarrierTrace L b a c).rangeRestrict f =
      (gaussianCarrierTrace L b a c).quotKerEquivRange
        ((gaussianCarrierTrace L b a c).ker.mkQ f) := by
    apply Subtype.ext
    rfl
  rw [heq, LinearEquiv.symm_apply_apply]
  rfl

theorem gaussianCarrierTraceDensity_nonneg (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ)
    (g : (gaussianCarrierTrace L b a c).range) (hg : 0 ≤ g) :
    0 ≤ gaussianCarrierTraceDensity L hn hb a c g := by
  obtain ⟨f, hf⟩ := g.property
  have heq : g = (gaussianCarrierTrace L b a c).rangeRestrict f := Subtype.ext hf.symm
  rw [heq, gaussianCarrierTraceDensity_apply]
  apply realValueDensity_nonneg_of_trace_nonneg L hn hb
    (localizeGaussianCore L b c f).property a
  intro x hx
  by_cases hK : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · rw [localizeGaussianCore_on L b c f hK]
    have h := hg ⟨x, hx, hK⟩
    rw [heq] at h
    exact h
  · rw [localizeGaussianCore_off L b c f hK]

/-- Positivity on the local image is derived, not supplied as an extension hypothesis. -/
def gaussianCarrierPositiveFunctional (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) :
    (gaussianCarrierTrace L b a c).range →ₚ[ℝ] ℝ :=
  { gaussianCarrierTraceDensity L hn hb a c with
    monotone' := fun f g hfg ↦ by
      have h := gaussianCarrierTraceDensity_nonneg L hn hb a c (g - f) (sub_nonneg.mpr hfg)
      rw [map_sub] at h
      exact sub_nonneg.mp h }

/-- The unit in the actual restriction image. -/
def gaussianCarrierTraceUnit (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) : (gaussianCarrierTrace L b a c).range :=
  (gaussianCarrierTrace L b a c).rangeRestrict (gaussianCarrierUnit L b a hc)

@[simp] theorem gaussianCarrierTraceUnit_apply (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) (x : adelicFiberCarrier L a c) :
    (gaussianCarrierTraceUnit L b a hc).val x = 1 :=
  gaussianCarrierUnit_on L b a hc x.property

/-- The unit's value is its Fourier density, not a chosen probability mass. -/
theorem gaussianCarrierTraceDensity_unit (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    gaussianCarrierTraceDensity L hn hb a c (gaussianCarrierTraceUnit L b a hc) =
      L.rationalQuadraticSpaceMatrix.realValueDensity (gaussianCarrierUnit L b a hc).val a := by
  rw [gaussianCarrierTraceUnit, gaussianCarrierTraceDensity_apply, localizeGaussianCore_unit]

/-- The bound on the image, with the value at the explicit unit kept. -/
theorem abs_gaussianCarrierTraceDensity_le (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (f : (gaussianCarrierTrace L b a c).range) :
    |gaussianCarrierTraceDensity L hn hb a c f| ≤ ‖f‖ *
      L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianCarrierUnit L b a (NeZero.ne c)).val a := by
  rw [← gaussianCarrierTraceDensity_unit L hn hb a (NeZero.ne c)]
  exact SMSFormula.ShellLocalBound.abs_le_norm_mul _
    (fun g hg ↦ gaussianCarrierTraceDensity_nonneg L hn hb a c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm) f

/-- The concrete bounded functional on the local image. Density of that image
is needed separately before extending it to all continuous functions. -/
def gaussianCarrierContinuousFunctional (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c] :
    (gaussianCarrierTrace L b a c).range →L[ℝ] ℝ :=
  SMSFormula.ShellLocalBound.toContinuousLinearMap (gaussianCarrierTraceDensity L hn hb a c)
    (fun g hg ↦ gaussianCarrierTraceDensity_nonneg L hn hb a c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)

@[simp] theorem gaussianCarrierContinuousFunctional_apply (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (f : realGaussianCore L b) :
    gaussianCarrierContinuousFunctional L hn hb a c
        ((gaussianCarrierTrace L b a c).rangeRestrict f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity (localizeGaussianCore L b c f).val a :=
  gaussianCarrierTraceDensity_apply L hn hb a c f

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
