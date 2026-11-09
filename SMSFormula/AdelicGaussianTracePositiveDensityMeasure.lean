import SMSFormula.AdelicGaussianFiberDetermination
import SMSFormula.AdelicGaussianFiberOrbitalComparison
import SMSFormula.AdelicGaussianResidueRestrictedReplacement

/-!
# The Riesz fiber measure of any trace-positive core density (rank-free)

The Riesz fiber measure `gaussianFiberMeasure` (lattice rank at least five) uses the Fourier
value density only through
* the linear map `realGaussianDensityLinearMap` on the real Gaussian core, and
* trace positivity `realValueDensity_nonneg_of_trace_nonneg` on the literal value fiber `X_a`;
its invariance uses in addition only `realValueDensity_comp_specialOrthogonal`.

`TracePositiveCoreDensity L b a` records exactly the first two for an arbitrary linear functional
`D` on the core.  For every such `D` the construction goes through verbatim:
the positive extension on each literal compact carrier piece, the gluing over all supporting
carriers, the Riesz measure `D.fiberMeasure hb`, recovery `∫ ψ dσ_D = D(ψ)` on the core,
determination by core integrals, `SO(𝔸)`-invariance for an invariant `D`, and the carried-set
masses `σ_D(U_R) = ofReal(D(unit_R))`.  The Fourier density is the instance
`realValueTracePositiveDensity` (rank at least five).  No rank bound, carrier or normalization is
chosen.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix CompactlySupported MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance tpdT2Infinite : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance tpdT2Finite : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance tpdT2Adele : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

/-- A trace-positive core density at the adelic value `a`: a linear functional on the real
Gaussian core that is nonnegative on every test with nonnegative trace on the literal fiber. -/
structure TracePositiveCoreDensity (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) where
  /-- The density functional on the core. -/
  toLinearMap : realGaussianCore L b →ₗ[ℝ] ℝ
  /-- Trace positivity on the literal value fiber. -/
  nonneg_of_trace_nonneg : ∀ f : realGaussianCore L b,
    (∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → 0 ≤ f.val x) →
      0 ≤ toLinearMap f

/-- The instance (lattice rank at least five): the Fourier value density. -/
def realValueTracePositiveDensity (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) : TracePositiveCoreDensity L b a where
  toLinearMap := realGaussianDensityLinearMap L hn hb a
  nonneg_of_trace_nonneg f hf := realValueDensity_nonneg_of_trace_nonneg L hn hb f.property a hf

@[simp] theorem realValueTracePositiveDensity_apply (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ}
    (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    (realValueTracePositiveDensity L hn hb a).toLinearMap f =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a := rfl

namespace TracePositiveCoreDensity

variable {L : PositiveDefiniteIntegralLattice n} {b : ℝ} {a : RationalAdele} (D : TracePositiveCoreDensity L b a)

/-- The trace kernel: a test vanishing on the fiber has density zero. -/
theorem eq_zero_of_trace_zero (f : realGaussianCore L b)
    (hf : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a → f.val x = 0) :
    D.toLinearMap f = 0 := by
  have hp := D.nonneg_of_trace_nonneg f (fun x hx ↦ (hf x hx).ge)
  have hm := D.nonneg_of_trace_nonneg (-f) (fun x hx ↦ by
    change 0 ≤ -f.val x
    rw [hf x hx, neg_zero])
  rw [map_neg] at hm
  linarith

/-! ## The positive functional on one literal compact carrier piece -/

theorem ker_carrierTrace_le (c : ℕ) :
    (gaussianCarrierTrace L b a c).ker ≤ (D.toLinearMap.comp (localizeGaussianCore L b c)).ker := by
  intro f hf
  apply LinearMap.mem_ker.mpr
  refine D.eq_zero_of_trace_zero (localizeGaussianCore L b c f) fun x hx ↦ ?_
  by_cases hK : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · rw [localizeGaussianCore_on L b c f hK]
    exact congrArg (fun g ↦ g ⟨x, hx, hK⟩) (LinearMap.mem_ker.mp hf)
  · exact localizeGaussianCore_off L b c f hK

/-- The image functional on the trace image, through the trace kernel. -/
def carrierTraceDensity (c : ℕ) : (gaussianCarrierTrace L b a c).range →ₗ[ℝ] ℝ :=
  ((gaussianCarrierTrace L b a c).ker.liftQ (D.toLinearMap.comp (localizeGaussianCore L b c))
    (D.ker_carrierTrace_le c)).comp
    (gaussianCarrierTrace L b a c).quotKerEquivRange.symm.toLinearMap

theorem carrierTraceDensity_apply (c : ℕ) (f : realGaussianCore L b) :
    D.carrierTraceDensity c ((gaussianCarrierTrace L b a c).rangeRestrict f) =
      D.toLinearMap (localizeGaussianCore L b c f) := by
  unfold carrierTraceDensity
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have heq : (gaussianCarrierTrace L b a c).rangeRestrict f =
      (gaussianCarrierTrace L b a c).quotKerEquivRange
        ((gaussianCarrierTrace L b a c).ker.mkQ f) := by
    apply Subtype.ext
    rfl
  rw [heq, LinearEquiv.symm_apply_apply]
  rfl

theorem carrierTraceDensity_nonneg (c : ℕ) (g : (gaussianCarrierTrace L b a c).range)
    (hg : 0 ≤ g) : 0 ≤ D.carrierTraceDensity c g := by
  obtain ⟨f, hf⟩ := g.property
  have heq : g = (gaussianCarrierTrace L b a c).rangeRestrict f := Subtype.ext hf.symm
  rw [heq, carrierTraceDensity_apply]
  refine D.nonneg_of_trace_nonneg _ fun x hx ↦ ?_
  by_cases hK : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · rw [localizeGaussianCore_on L b c f hK]
    have h := hg ⟨x, hx, hK⟩
    rw [heq] at h
    exact h
  · rw [localizeGaussianCore_off L b c f hK]

theorem carrierTraceDensity_unit {c : ℕ} (hc : c ≠ 0) :
    D.carrierTraceDensity c (gaussianCarrierTraceUnit L b a hc) =
      D.toLinearMap (gaussianCarrierUnit L b a hc) := by
  rw [gaussianCarrierTraceUnit, carrierTraceDensity_apply, localizeGaussianCore_unit]

/-- The positive continuous extension to all continuous functions on the compact piece. -/
def carrierExtension (c : ℕ) [NeZero c] : C(adelicFiberCarrier L a c, ℝ) →L[ℝ] ℝ :=
  SMSFormula.ShellLocalBound.extendToAll (D.carrierTraceDensity c)
    (fun g hg ↦ D.carrierTraceDensity_nonneg c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)

theorem carrierExtension_trace (hb : 0 < b) (c : ℕ) [NeZero c] (f : realGaussianCore L b) :
    D.carrierExtension c (gaussianCarrierTrace L b a c f) =
      D.toLinearMap (localizeGaussianCore L b c f) := by
  have h := SMSFormula.ShellLocalBound.extendToAll_apply
    (V := (gaussianCarrierTrace L b a c).range) (D.carrierTraceDensity c)
    (fun g hg ↦ D.carrierTraceDensity_nonneg c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)
    (dense_gaussianCarrierTrace L hb a c) ((gaussianCarrierTrace L b a c).rangeRestrict f)
  change D.carrierExtension c (gaussianCarrierTrace L b a c f) =
    D.carrierTraceDensity c ((gaussianCarrierTrace L b a c).rangeRestrict f) at h
  rw [carrierTraceDensity_apply] at h
  exact h

theorem carrierExtension_nonneg (hb : 0 < b) (c : ℕ) [NeZero c]
    (f : C(adelicFiberCarrier L a c, ℝ)) (hf : 0 ≤ f) : 0 ≤ D.carrierExtension c f :=
  SMSFormula.ShellLocalBound.extendToAll_nonneg
    (V := (gaussianCarrierTrace L b a c).range) (D.carrierTraceDensity c)
    (fun g hg ↦ D.carrierTraceDensity_nonneg c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)
    (dense_gaussianCarrierTrace L hb a c) f hf

theorem carrierExtension_unique (hb : 0 < b) (c : ℕ) [NeZero c]
    (Λ : C(adelicFiberCarrier L a c, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ f : realGaussianCore L b,
      Λ (gaussianCarrierTrace L b a c f) = D.toLinearMap (localizeGaussianCore L b c f)) :
    Λ = D.carrierExtension c := by
  have hdense : DenseRange (gaussianCarrierTrace L b a c) := dense_gaussianCarrierTrace L hb a c
  ext f
  exact hdense.induction_on f
    (isClosed_eq Λ.continuous (D.carrierExtension c).continuous)
    (fun g ↦ (hΛ g).trans (D.carrierExtension_trace hb c g).symm)

theorem carrierExtension_compatible (hb : 0 < b) {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (f : C(adelicFiberCarrier L a d, ℝ)) :
    D.carrierExtension d (f * gaussianCarrierIndicator L a (NeZero.ne c) d) =
      D.carrierExtension c (f.comp (gaussianCarrierInclusion L a hcd)) := by
  have hdense : DenseRange (gaussianCarrierTrace L b a d) := dense_gaussianCarrierTrace L hb a d
  refine hdense.induction_on f (isClosed_eq
    ((D.carrierExtension d).continuous.comp (continuous_id.mul continuous_const))
    ((D.carrierExtension c).continuous.comp
      (ContinuousMap.continuous_precomp (gaussianCarrierInclusion L a hcd)))) ?_
  intro g
  rw [gaussianCarrierTrace_localize, gaussianCarrierTrace_restrict,
    D.carrierExtension_trace hb, D.carrierExtension_trace hb, localizeGaussianCore_absorb L b hcd]

/-! ## Gluing over all supporting carriers -/

theorem carrierExtension_of_fiberCarried (hb : 0 < b) {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (f : C(adelicValueFiber L a, ℝ)) (hf : FiberCarried L a c f) :
    D.carrierExtension d (fiberCarrierRestriction L a d f) =
      D.carrierExtension c (fiberCarrierRestriction L a c f) := by
  have h := D.carrierExtension_compatible hb hcd (fiberCarrierRestriction L a d f)
  rw [fiberCarrierRestriction_mul_indicator L a (NeZero.ne c) d f hf,
    fiberCarrierRestriction_restrict] at h
  exact h

theorem carrierExtension_independent (hb : 0 < b) {c d : ℕ} [NeZero c] [NeZero d]
    (f : C(adelicValueFiber L a, ℝ)) (hc : FiberCarried L a c f) (hd : FiberCarried L a d f) :
    D.carrierExtension c (fiberCarrierRestriction L a c f) =
      D.carrierExtension d (fiberCarrierRestriction L a d f) :=
  (D.carrierExtension_of_fiberCarried hb (dvd_mul_right c d) f hc).symm.trans
    (D.carrierExtension_of_fiberCarried hb (dvd_mul_left d c) f hd)

private theorem existsUnique_fiberValue (hb : 0 < b) (f : C_c(adelicValueFiber L a, ℝ)) :
    ∃! r : ℝ, ∀ (c : ℕ) (hc : c ≠ 0), FiberCarried L a c f →
      r = @carrierExtension n L b a D c ⟨hc⟩ (fiberCarrierRestriction L a c f.toContinuousMap) := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  letI : NeZero c := ⟨hc⟩
  refine ⟨D.carrierExtension c (fiberCarrierRestriction L a c f.toContinuousMap), ?_, ?_⟩
  · intro d hd hfd
    letI : NeZero d := ⟨hd⟩
    exact D.carrierExtension_independent hb f.toContinuousMap hf hfd
  · intro r hr
    exact hr c hc hf

/-- The unique scalar specified by all supporting carriers. -/
def fiberValue (hb : 0 < b) (f : C_c(adelicValueFiber L a, ℝ)) : ℝ :=
  (D.existsUnique_fiberValue hb f).exists.choose

theorem fiberValue_eq (hb : 0 < b) (f : C_c(adelicValueFiber L a, ℝ)) (c : ℕ) [NeZero c]
    (hf : FiberCarried L a c f) :
    D.fiberValue hb f = D.carrierExtension c (fiberCarrierRestriction L a c f.toContinuousMap) :=
  (D.existsUnique_fiberValue hb f).exists.choose_spec c (NeZero.ne c) hf

theorem fiberValue_add (hb : 0 < b) (f g : C_c(adelicValueFiber L a, ℝ)) :
    D.fiberValue hb (f + g) = D.fiberValue hb f + D.fiberValue hb g := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  obtain ⟨d, hd, hg⟩ := exists_fiberCarried L a g
  letI : NeZero (c*d) := ⟨mul_ne_zero hc hd⟩
  have hf' := hf.mono (dvd_mul_right c d)
  have hg' := hg.mono (dvd_mul_left d c)
  have hsum : FiberCarried L a (c*d) (f+g) := fun x hx ↦ by
    change f x + g x = 0
    rw [hf' x hx, hg' x hx, add_zero]
  rw [D.fiberValue_eq hb (f+g) (c*d) hsum, D.fiberValue_eq hb f (c*d) hf',
    D.fiberValue_eq hb g (c*d) hg']
  change D.carrierExtension (c*d)
    (fiberCarrierRestriction L a (c*d) (f.toContinuousMap + g.toContinuousMap)) = _
  rw [map_add, map_add]

theorem fiberValue_smul (hb : 0 < b) (r : ℝ) (f : C_c(adelicValueFiber L a, ℝ)) :
    D.fiberValue hb (r • f) = r * D.fiberValue hb f := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  letI : NeZero c := ⟨hc⟩
  have hsmul : FiberCarried L a c (r • f) := fun x hx ↦ by
    change r * f x = 0
    rw [hf x hx, mul_zero]
  rw [D.fiberValue_eq hb (r • f) c hsmul, D.fiberValue_eq hb f c hf]
  change D.carrierExtension c (fiberCarrierRestriction L a c (r • f.toContinuousMap)) = _
  rw [map_smul, map_smul, smul_eq_mul]

/-- The glued positive functional on all compactly supported continuous fiber tests. -/
def fiberFunctional (hb : 0 < b) : C_c(adelicValueFiber L a, ℝ) →ₚ[ℝ] ℝ where
  toFun := D.fiberValue hb
  map_add' := D.fiberValue_add hb
  map_smul' := D.fiberValue_smul hb
  monotone' := by
    intro f g hfg
    obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
    obtain ⟨d, hd, hg⟩ := exists_fiberCarried L a g
    letI : NeZero (c*d) := ⟨mul_ne_zero hc hd⟩
    change D.fiberValue hb f ≤ D.fiberValue hb g
    rw [D.fiberValue_eq hb f (c*d) (hf.mono (dvd_mul_right c d)),
      D.fiberValue_eq hb g (c*d) (hg.mono (dvd_mul_left d c))]
    have h := D.carrierExtension_nonneg hb (c*d)
      (fiberCarrierRestriction L a (c*d) g.toContinuousMap -
        fiberCarrierRestriction L a (c*d) f.toContinuousMap)
      (fun x ↦ sub_nonneg.mpr (hfg (gaussianCarrierToFiber L a (c*d) x)))
    rw [map_sub] at h
    exact sub_nonneg.mp h

theorem fiberFunctional_eq (hb : 0 < b) (f : C_c(adelicValueFiber L a, ℝ)) (c : ℕ) [NeZero c]
    (hf : FiberCarried L a c f) :
    D.fiberFunctional hb f = D.carrierExtension c (fiberCarrierRestriction L a c f.toContinuousMap) :=
  D.fiberValue_eq hb f c hf

/-- Recovery of `D` on every core trace. -/
theorem fiberFunctional_trace (hb : 0 < b) (f : realGaussianCore L b) :
    D.fiberFunctional hb (realGaussianTraceCc L b a f) = D.toLinearMap f := by
  obtain ⟨c, hc, hf⟩ := exists_carrier_realGaussianCore L b f.property
  letI : NeZero c := ⟨hc⟩
  have hloc : localizeGaussianCore L b c f = f := by
    ext x
    by_cases hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
    · exact localizeGaussianCore_on L b c f hx
    · rw [localizeGaussianCore_off L b c f hx, hf x hx]
  rw [D.fiberFunctional_eq hb _ c (fun x hx ↦ hf x.val hx), fiberCarrierRestriction_trace,
    D.carrierExtension_trace hb, hloc]

/-! ## The Riesz fiber measure of `D` -/

/-- The Riesz fiber measure of the trace-positive density `D` on the literal fiber `X_a`. -/
def fiberMeasure (hb : 0 < b) : Measure (adelicValueFiber L a) :=
  RealRMK.rieszMeasure (D.fiberFunctional hb)

instance fiberMeasure_regular (hb : 0 < b) : (D.fiberMeasure hb).Regular :=
  RealRMK.regular_rieszMeasure _

theorem integral_fiberMeasure (hb : 0 < b) (f : C_c(adelicValueFiber L a, ℝ)) :
    ∫ x, f x ∂D.fiberMeasure hb = D.fiberFunctional hb f :=
  RealRMK.integral_rieszMeasure _ f

/-- Recovery on the core: `∫_{X_a} ψ dσ_D = D(ψ)`. -/
theorem integral_fiberMeasure_core (hb : 0 < b) (f : realGaussianCore L b) :
    ∫ x, f.val x.val ∂D.fiberMeasure hb = D.toLinearMap f := by
  change (∫ x, realGaussianTraceCc L b a f x ∂D.fiberMeasure hb) = _
  rw [integral_fiberMeasure, fiberFunctional_trace]

theorem integrable_fiberMeasure_core (hb : 0 < b) (f : realGaussianCore L b) :
    Integrable (fun x : adelicValueFiber L a ↦ f.val x.val) (D.fiberMeasure hb) :=
  (realGaussianTraceCc L b a f).continuous.integrable_of_hasCompactSupport
    (realGaussianTraceCc L b a f).hasCompactSupport

/-- Recovery in `ℝ≥0∞` for a nonnegative core test: `∫⁻ ofReal ψ dσ_D = ofReal (D ψ)`. -/
theorem lintegral_fiberMeasure_core (hb : 0 < b) (f : realGaussianCore L b)
    (hf : ∀ y, 0 ≤ f.val y) :
    ∫⁻ x, ENNReal.ofReal (f.val x.val) ∂D.fiberMeasure hb = ENNReal.ofReal (D.toLinearMap f) := by
  rw [← D.integral_fiberMeasure_core hb f, ofReal_integral_eq_lintegral_ofReal
    (D.integrable_fiberMeasure_core hb f) (Filter.Eventually.of_forall fun y ↦ hf y.val)]

/-! ## Determination by core integrals -/

private def carrierIntegral (a : RationalAdele) (c : ℕ) [NeZero c]
    (μ : Measure (adelicValueFiber L a)) [μ.Regular] : C(adelicFiberCarrier L a c, ℝ) →L[ℝ] ℝ := by
  let ν := μ.comap (gaussianCarrierToFiber L a c)
  have hi (f : C(adelicFiberCarrier L a c, ℝ)) : Integrable f ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  let I : C(adelicFiberCarrier L a c, ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun f ↦ ∫ x, f x ∂ν
    map_add' := fun f g ↦ integral_add (hi f) (hi g)
    map_smul' := fun r f ↦ integral_smul r f }
  exact I.mkContinuous (ν.real Set.univ) fun f ↦ by
    simpa only [mul_comm] using
      (norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall f.norm_coe_le_norm))

private theorem carrierIntegral_apply (a : RationalAdele) (c : ℕ) [NeZero c]
    (μ : Measure (adelicValueFiber L a)) [μ.Regular] (f : C(adelicFiberCarrier L a c, ℝ)) :
    carrierIntegral (L := L) a c μ f = ∫ x, f x ∂μ.comap (gaussianCarrierToFiber L a c) := rfl

private theorem carrierIntegral_trace (c : ℕ) [NeZero c] (μ : Measure (adelicValueFiber L a))
    [μ.Regular] (f : realGaussianCore L b) :
    carrierIntegral (L := L) a c μ (gaussianCarrierTrace L b a c f) =
      ∫ x, (localizeGaussianCore L b c f).val x.val ∂μ := by
  rw [carrierIntegral_apply, ← fiberCarrierRestriction_trace,
    integral_comap_gaussianCarrierToFiber, ← integral_indicator
      (isCompact_fiberDividedCarrier L a (NeZero.ne c)).isClosed.measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : x ∈ fiberDividedCarrier L a c
  · rw [Set.indicator_of_mem hx, localizeGaussianCore_on L b c f hx]
    rfl
  · rw [Set.indicator_of_notMem hx, localizeGaussianCore_off L b c f hx]

/-- Recovery of `D` on the core by a regular measure implies recovery on all `C_c` tests. -/
theorem integral_eq_fiberFunctional_of_core (hb : 0 < b) (μ : Measure (adelicValueFiber L a))
    [μ.Regular] (hμ : ∀ f : realGaussianCore L b, (∫ x, f.val x.val ∂μ) = D.toLinearMap f)
    (f : C_c(adelicValueFiber L a, ℝ)) :
    ∫ x, f x ∂μ = D.fiberFunctional hb f := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  letI : NeZero c := ⟨hc⟩
  have hind : (fiberDividedCarrier L a c).indicator f = f := by
    funext x
    by_cases hx : x ∈ fiberDividedCarrier L a c
    · exact Set.indicator_of_mem hx f
    · rw [Set.indicator_of_notMem hx, hf x hx]
  have h := integral_comap_gaussianCarrierToFiber L a c μ f.toContinuousMap
  rw [← integral_indicator (isCompact_fiberDividedCarrier L a hc).isClosed.measurableSet] at h
  change (∫ x, fiberCarrierRestriction L a c f.toContinuousMap x
    ∂μ.comap (gaussianCarrierToFiber L a c)) = ∫ x, (fiberDividedCarrier L a c).indicator f x ∂μ at h
  rw [hind] at h
  have hext : carrierIntegral (L := L) a c μ = D.carrierExtension c := by
    apply D.carrierExtension_unique hb
    intro g
    rw [carrierIntegral_trace, hμ]
  rw [← h, ← carrierIntegral_apply, hext, D.fiberFunctional_eq hb f c hf]

/-- The Riesz fiber measure is the unique regular measure recovering `D` on the core. -/
theorem eq_fiberMeasure_of_core_integrals (hb : 0 < b) {μ : Measure (adelicValueFiber L a)}
    [μ.Regular] (hμ : ∀ f : realGaussianCore L b, (∫ x, f.val x.val ∂μ) = D.toLinearMap f) :
    μ = D.fiberMeasure hb :=
  SMSFormula.Coarea.eq_rieszMeasure_of_integral_eq _ (D.integral_eq_fiberFunctional_of_core hb μ hμ)

/-! ## Invariance -/

/-- `D` is `SO(𝔸)`-invariant: `D(ψ ∘ h) = D(ψ)` for every full-adelic special orthogonal `h`. -/
def IsSpecialOrthogonalInvariant : Prop :=
  ∀ (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) (f : realGaussianCore L b),
    D.toLinearMap ⟨fun x ↦ f.val (h.1.1.1.mulVec x),
      mem_realGaussianCore_comp_specialOrthogonal L b h f.property⟩ = D.toLinearMap f

theorem map_fiberMeasure_specialOrthogonal (hb : 0 < b) (hD : D.IsSpecialOrthogonalInvariant)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure.map (specialOrthogonalFiberHomeomorph L a h) (D.fiberMeasure hb) = D.fiberMeasure hb := by
  let e := specialOrthogonalFiberHomeomorph L a h
  haveI : (Measure.map e (D.fiberMeasure hb)).Regular := Measure.Regular.map e
  apply D.eq_fiberMeasure_of_core_integrals hb
  intro f
  change (∫ x, realGaussianTrace L b a f x ∂Measure.map e (D.fiberMeasure hb)) = _
  rw [integral_map e.continuous.aemeasurable (realGaussianTrace L b a f).continuous.aestronglyMeasurable]
  change (∫ x, f.val (e x).val ∂D.fiberMeasure hb) = _
  simp only [e, specialOrthogonalFiberHomeomorph_val]
  let F : realGaussianCore L b := ⟨fun x ↦ f.val (h.1.1.1.mulVec x),
    mem_realGaussianCore_comp_specialOrthogonal L b h f.property⟩
  exact (D.integral_fiberMeasure_core hb F).trans (hD h f)

/-- Invariance in the instance form consumed by the orbital comparison. -/
theorem smulInvariantMeasure_fiberMeasure (hb : 0 < b) (hD : D.IsSpecialOrthogonalInvariant) :
    SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) (D.fiberMeasure hb) := by
  constructor
  intro h s hs
  have hm := D.map_fiberMeasure_specialOrthogonal hb hD h
  have he := Measure.map_apply (μ := D.fiberMeasure hb)
    (specialOrthogonalFiberHomeomorph L a h).continuous.measurable hs
  exact he.symm.trans (congrArg (fun μ ↦ μ s) hm)

/-! ## Carried-set masses -/

theorem fiberMeasure_carrier_lt_top (hb : 0 < b) {c : ℕ} (hc : c ≠ 0) :
    D.fiberMeasure hb (fiberDividedCarrier L a c) < ⊤ :=
  (isCompact_fiberDividedCarrier L a hc).measure_lt_top

/-- The mass of a carried fiber set is the density of its orbit test:
`σ_D({x ∈ X_a : x_f ∈ U_R}) = ofReal(D(unit_R))`. -/
theorem fiberMeasure_fiberResidueRestrictedSet (hb : 0 < b) (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) :
    D.fiberMeasure hb (fiberResidueRestrictedSet L a N₀ R) =
      ENNReal.ofReal (D.toLinearMap (gaussianResidueRestrictedUnit L b a N₀ R)) := by
  have hclosed : IsClosed (fiberResidueRestrictedSet L a N₀ R) := by
    have hcont := (realGaussianTraceCc L b a (gaussianResidueRestrictedUnit L b a N₀ R)).continuous
    have hset : fiberResidueRestrictedSet L a N₀ R =
        {x : adelicValueFiber L a |
          realGaussianTraceCc L b a (gaussianResidueRestrictedUnit L b a N₀ R) x = 1} := by
      ext x
      simp only [fiberResidueRestrictedSet, Set.mem_setOf_eq, realGaussianTraceCc_apply,
        gaussianResidueRestrictedUnit_apply_of_value L b a N₀ R x.property]
    rw [hset]
    exact isClosed_eq hcont continuous_const
  have hsub : fiberResidueRestrictedSet L a N₀ R ⊆ fiberDividedCarrier L a 1 := fun x hx ↦
    mem_integral_of_realResidueRestrictedIndicator_ne_zero N₀ R
      (by rw [show realResidueRestrictedIndicator n N₀ R _ = 1 from hx]; exact one_ne_zero)
  have hfin : D.fiberMeasure hb (fiberResidueRestrictedSet L a N₀ R) ≠ ⊤ :=
    ((measure_mono hsub).trans_lt (D.fiberMeasure_carrier_lt_top hb one_ne_zero)).ne
  have h := D.integral_fiberMeasure_core hb (gaussianResidueRestrictedUnit L b a N₀ R)
  rw [gaussianResidueRestrictedUnit_trace_indicator, integral_indicator_const (1 : ℝ)
    hclosed.measurableSet, smul_eq_mul, mul_one] at h
  rw [← h, measureReal_def, ENNReal.ofReal_toReal hfin]

/-- The integral carrier: `σ_D(X_a ∩ {x_f integral}) = ofReal(D(unit_univ))` at any level. -/
theorem fiberMeasure_fiberDividedCarrier_one (hb : 0 < b) (N₀ : ℕ) [NeZero N₀] :
    D.fiberMeasure hb (fiberDividedCarrier L a 1) =
      ENNReal.ofReal (D.toLinearMap (gaussianResidueRestrictedUnit L b a N₀ Set.univ)) := by
  rw [← fiberResidueRestrictedSet_univ L a N₀, D.fiberMeasure_fiberResidueRestrictedSet hb]

end TracePositiveCoreDensity

/-- The Riesz measure is the Riesz fiber measure of the Fourier density. -/
theorem gaussianFiberMeasure_eq_fiberMeasure_realValueTracePositiveDensity (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    gaussianFiberMeasure L hn hb a = (realValueTracePositiveDensity L hn hb a).fiberMeasure hb :=
  (realValueTracePositiveDensity L hn hb a).eq_fiberMeasure_of_core_integrals hb
    (integral_gaussianFiberMeasure_core L hn hb a)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
