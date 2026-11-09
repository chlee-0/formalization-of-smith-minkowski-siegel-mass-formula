import SMSFormula.AdelicGaussianFiberMeasure

/-!
# Determination on the literal adelic fiber

Recovery on the real core determines a regular measure on the literal
fiber. On each compact piece, pullback of a supplied measure is finite and
integration is continuous in the sup norm. The already proved density of the
actual trace image therefore applies. Compact supports then recover all C_c
integrals. No product-model identification or global finiteness is used.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix CompactlySupported MeasureTheory

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

theorem measurableEmbedding_gaussianCarrierToFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (c : ℕ) [NeZero c] : MeasurableEmbedding (gaussianCarrierToFiber L a c) := by
  have hinj : Function.Injective (gaussianCarrierToFiber L a c) := by
    intro x y h
    apply Subtype.ext
    have hval := congrArg Subtype.val h
    simpa only [gaussianCarrierToFiber_val] using hval
  exact ((gaussianCarrierToFiber L a c).continuous.isClosedEmbedding hinj).measurableEmbedding

/-- A supplied regular measure pulls back to a finite measure on every compact
piece. This is only restriction through the literal inclusion. -/
instance isFiniteMeasure_comap_gaussianCarrierToFiber (L : PositiveDefiniteIntegralLattice n)
    (a : RationalAdele) (c : ℕ) [NeZero c] (μ : Measure (adelicValueFiber L a)) [μ.Regular] :
    IsFiniteMeasure (μ.comap (gaussianCarrierToFiber L a c)) := by
  constructor
  rw [(measurableEmbedding_gaussianCarrierToFiber L a c).comap_apply,
    Set.image_univ, range_gaussianCarrierToFiber]
  exact (isCompact_fiberDividedCarrier L a (NeZero.ne c)).measure_lt_top

private def carrierIntegral (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) [NeZero c]
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

private theorem carrierIntegral_apply (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (c : ℕ) [NeZero c] (μ : Measure (adelicValueFiber L a)) [μ.Regular]
    (f : C(adelicFiberCarrier L a c, ℝ)) :
    carrierIntegral L a c μ f = ∫ x, f x ∂μ.comap (gaussianCarrierToFiber L a c) := rfl

theorem integral_comap_gaussianCarrierToFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (c : ℕ) [NeZero c] (μ : Measure (adelicValueFiber L a))
    (f : C(adelicValueFiber L a, ℝ)) :
    (∫ x, fiberCarrierRestriction L a c f x ∂μ.comap (gaussianCarrierToFiber L a c)) =
      ∫ x in fiberDividedCarrier L a c, f x ∂μ := by
  have he := measurableEmbedding_gaussianCarrierToFiber L a c
  have h := integral_map (μ := μ.comap (gaussianCarrierToFiber L a c))
    he.measurable.aemeasurable f.continuous.aestronglyMeasurable
  rw [he.map_comap, range_gaussianCarrierToFiber] at h
  exact h.symm

private theorem carrierIntegral_trace (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    (c : ℕ) [NeZero c] (μ : Measure (adelicValueFiber L a)) [μ.Regular]
    (f : realGaussianCore L b) :
    carrierIntegral L a c μ (gaussianCarrierTrace L b a c f) =
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

private theorem carrierIntegral_eq_extension (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (μ : Measure (adelicValueFiber L a)) [μ.Regular]
    (hμ : ∀ f : realGaussianCore L b, (∫ x, f.val x.val ∂μ) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a) :
    carrierIntegral L a c μ = gaussianCarrierExtension L hn hb a c := by
  apply gaussianCarrierExtension_unique
  intro f
  rw [carrierIntegral_trace, hμ]

/-- Recovery on the actual core implies recovery on all C_c tests. The local
compact trace algebra supplies determination on the literal fiber. -/
theorem integral_eq_gaussianFiberFunctional_of_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (μ : Measure (adelicValueFiber L a)) [μ.Regular]
    (hμ : ∀ f : realGaussianCore L b, (∫ x, f.val x.val ∂μ) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a)
    (f : C_c(adelicValueFiber L a, ℝ)) :
    ∫ x, f x ∂μ = gaussianFiberFunctional L hn hb a f := by
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
  rw [← h, ← carrierIntegral_apply, carrierIntegral_eq_extension L hn hb a c μ hμ,
    gaussianFiberFunctional_eq L hn hb a f c hf]

/-- The constructed measure is the unique regular measure recovering the old
Fourier density on the continuous real core. No native agreement is assumed. -/
theorem eq_gaussianFiberMeasure_of_core_integrals (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {μ : Measure (adelicValueFiber L a)} [μ.Regular]
    (hμ : ∀ f : realGaussianCore L b, (∫ x, f.val x.val ∂μ) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a) :
    μ = gaussianFiberMeasure L hn hb a :=
  eq_gaussianFiberMeasure_of_integral_eq L hn hb a
    (integral_eq_gaussianFiberFunctional_of_core L hn hb a μ hμ)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
