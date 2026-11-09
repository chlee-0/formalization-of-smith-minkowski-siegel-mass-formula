import SMSFormula.AdelicGaussianFiberFunctional
import SMSFormula.CoareaRieszInvariance

/-!
# The Riesz measure of the actual adelic value density

The whole literal fiber carries the Riesz measure of the glued positive
functional. Every test in the real Gaussian core has a compactly supported
trace, and integration of that trace is its original Fourier value density at
the specified adelic value. This is pointwise recovery, not an a.e. disintegration
or an identification with the native orbital measure. No mass is evaluated.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix CompactlySupported MeasureTheory

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

/-- Closedness of the literal level set supplies local compactness. -/
instance locallyCompactSpace_adelicValueFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) :
    LocallyCompactSpace (adelicValueFiber L a) :=
  (isClosed_eq L.rationalQuadraticSpaceMatrix.continuous_fullAdelicQuadraticFormValue
    continuous_const).locallyCompactSpace

/-- A finite core expression has one old finite carrier; the real directions
need not have compact support in the ambient vector space. -/
theorem exists_carrier_realGaussianCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ x,
      rationalAdeleVectorFinitePart n x ∉ standardDividedLattice n c → f x = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, c, d, g, hc, _, hcar, _, rfl⟩ := hf
    refine ⟨c, hc, fun x hx ↦ ?_⟩
    have hz := Complex.ofReal_eq_zero.mp (hcar _ hx)
    simp only [hz, mul_zero]
  | zero => exact ⟨1, one_ne_zero, fun _ _ ↦ rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨c, hc, hf⟩ := hf
    obtain ⟨d, hd, hg⟩ := hg
    refine ⟨c*d, mul_ne_zero hc hd, fun x hx ↦ ?_⟩
    have hfc := hf x (fun h ↦ hx (dividedCarrier_subset_of_dvd (dvd_mul_right c d) h))
    have hgd := hg x (fun h ↦ hx (dividedCarrier_subset_of_dvd (dvd_mul_left d c) h))
    simp only [Pi.add_apply, hfc, hgd, add_zero]
  | smul r f _ hf =>
    obtain ⟨c, hc, hf⟩ := hf
    exact ⟨c, hc, fun x hx ↦ by simp only [Pi.smul_apply, smul_eq_mul, hf x hx, mul_zero]⟩

/-- On the literal fiber, finite-carrier support is compact support, by the
positive-definite real bound already proved for the compact pieces. -/
theorem hasCompactSupport_of_fiberCarried (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) {f : adelicValueFiber L a → ℝ} (hf : FiberCarried L a c f) :
    HasCompactSupport f := by
  letI : NeZero c := ⟨hc⟩
  apply HasCompactSupport.intro (isCompact_range (gaussianCarrierToFiber L a c).continuous)
  intro x hx
  apply hf x
  intro hmem
  apply hx
  refine ⟨⟨x.val, x.property, hmem⟩, ?_⟩
  apply Subtype.ext
  exact gaussianCarrierToFiber_val L a c _

/-- The old continuous trace, with its compact support proved. -/
def realGaussianTraceCc (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    (f : realGaussianCore L b) : C_c(adelicValueFiber L a, ℝ) :=
  ⟨realGaussianTrace L b a f, by
    obtain ⟨c, hc, hf⟩ := exists_carrier_realGaussianCore L b f.property
    exact hasCompactSupport_of_fiberCarried L a hc (fun x hx ↦ hf x.val hx)⟩

@[simp] theorem realGaussianTraceCc_apply (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    (f : realGaussianCore L b) (x : adelicValueFiber L a) :
    realGaussianTraceCc L b a f x = f.val x.val := rfl

theorem fiberCarrierRestriction_trace (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    (c : ℕ) (f : realGaussianCore L b) :
    fiberCarrierRestriction L a c (realGaussianTraceCc L b a f).toContinuousMap =
      gaussianCarrierTrace L b a c f := by
  apply ContinuousMap.ext
  intro x
  change f.val (gaussianCarrierToFiber L a c x).val = f.val x.val
  rw [gaussianCarrierToFiber_val]

/-- Recovery of the original unlocalized Fourier density, for every core test.
The carrier is supplied by the test and disappears from the conclusion. -/
@[simp] theorem gaussianFiberFunctional_trace (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    gaussianFiberFunctional L hn hb a (realGaussianTraceCc L b a f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a := by
  obtain ⟨c, hc, hf⟩ := exists_carrier_realGaussianCore L b f.property
  letI : NeZero c := ⟨hc⟩
  have hloc : localizeGaussianCore L b c f = f := by
    ext x
    by_cases hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
    · exact localizeGaussianCore_on L b c f hx
    · rw [localizeGaussianCore_off L b c f hx, hf x hx]
  rw [gaussianFiberFunctional_eq L hn hb a _ c (fun x hx ↦ hf x.val hx),
    fiberCarrierRestriction_trace, gaussianCarrierExtension_trace, hloc]

/-- The actual value-density fiber measure. Its domain is the literal fiber,
and its normalization is the old Fourier density, not a probability convention. -/
def gaussianFiberMeasure (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) : Measure (adelicValueFiber L a) :=
  RealRMK.rieszMeasure (gaussianFiberFunctional L hn hb a)

instance gaussianFiberMeasure_regular (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) : (gaussianFiberMeasure L hn hb a).Regular :=
  RealRMK.regular_rieszMeasure _

/-- Core traces are genuinely integrable against the constructed measure;
recovery never uses the zero convention for a nonintegrable Bochner integral. -/
theorem integrable_gaussianFiberMeasure_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    Integrable (fun x : adelicValueFiber L a ↦ f.val x.val) (gaussianFiberMeasure L hn hb a) :=
  (realGaussianTraceCc L b a f).continuous.integrable_of_hasCompactSupport
    (realGaussianTraceCc L b a f).hasCompactSupport

/-- Representation on all compactly supported continuous fiber tests. -/
theorem integral_gaussianFiberMeasure (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : C_c(adelicValueFiber L a, ℝ)) :
    ∫ x, f x ∂gaussianFiberMeasure L hn hb a = gaussianFiberFunctional L hn hb a f :=
  RealRMK.integral_rieszMeasure _ f

/-- Pointwise coarea recovery on the continuous core, at every adelic value.
No a.e. representative of a density or conditional measure is selected. -/
theorem integral_gaussianFiberMeasure_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    ∫ x, f.val x.val ∂gaussianFiberMeasure L hn hb a =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a := by
  change (∫ x, realGaussianTraceCc L b a f x ∂gaussianFiberMeasure L hn hb a) = _
  rw [integral_gaussianFiberMeasure, gaussianFiberFunctional_trace]

/-- Fiber integrals of a core test vary continuously in the adelic value.
This is testwise continuity, not a measurable-kernel assertion for all Borel sets. -/
theorem continuous_integral_gaussianFiberMeasure_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (f : realGaussianCore L b) :
    Continuous (fun a ↦ ∫ x, f.val x.val ∂gaussianFiberMeasure L hn hb a) := by
  simp_rw [integral_gaussianFiberMeasure_core]
  exact L.rationalQuadraticSpaceMatrix.continuous_realValueDensity
    (hasSignedValueDensity_of_mem_real_span L hn hb f.property).1

/-- Testwise absolute integrability in the value variable. -/
theorem integrable_integral_gaussianFiberMeasure_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (f : realGaussianCore L b) :
    Integrable (fun a ↦ ∫ x, f.val x.val ∂gaussianFiberMeasure L hn hb a)
      rationalAdeleAddHaarMeasure := by
  simp_rw [integral_gaussianFiberMeasure_core]
  exact (hasSignedValueDensity_of_mem_real_span L hn hb f.property).2.1

/-- The actual signed coarea identity on the continuous core, for every
measurable value set and the unchanged coordinate and scalar Haars. No general
disintegration kernel or native orbital comparison is asserted. -/
theorem setIntegral_gaussianFiberMeasure_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (f : realGaussianCore L b)
    {s : Set RationalAdele} (hs : MeasurableSet s) :
    (∫ x in L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue ⁻¹' s, f.val x
      ∂rationalAdeleCoordinateAddHaarMeasure n) =
    ∫ a in s, (∫ x, f.val x.val ∂gaussianFiberMeasure L hn hb a) ∂rationalAdeleAddHaarMeasure := by
  simp_rw [integral_gaussianFiberMeasure_core]
  exact (hasSignedValueDensity_of_mem_real_span L hn hb f.property).2.2 s hs

/-- Regular uniqueness identifies measures representing this functional. It
does not assert that the independently normalized native measure represents it. -/
theorem eq_gaussianFiberMeasure_of_integral_eq (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {μ : Measure (adelicValueFiber L a)} [μ.Regular]
    (hμ : ∀ f : C_c(adelicValueFiber L a, ℝ), ∫ x, f x ∂μ = gaussianFiberFunctional L hn hb a f) :
    μ = gaussianFiberMeasure L hn hb a :=
  SMSFormula.Coarea.eq_rieszMeasure_of_integral_eq _ hμ

/-- The divided carrier, merely restricted to the literal fiber. -/
def fiberDividedCarrier (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) :
    Set (adelicValueFiber L a) :=
  {x | rationalAdeleVectorFinitePart n x.val ∈ standardDividedLattice n c}

theorem range_gaussianCarrierToFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) :
    Set.range (gaussianCarrierToFiber L a c) = fiberDividedCarrier L a c := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change rationalAdeleVectorFinitePart n (gaussianCarrierToFiber L a c y).val ∈
      standardDividedLattice n c
    rw [gaussianCarrierToFiber_val]
    exact y.property.2
  · intro hx
    refine ⟨⟨x.val, x.property, hx⟩, ?_⟩
    apply Subtype.ext
    exact gaussianCarrierToFiber_val L a c _

theorem isCompact_fiberDividedCarrier (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) : IsCompact (fiberDividedCarrier L a c) := by
  letI : NeZero c := ⟨hc⟩
  rw [← range_gaussianCarrierToFiber]
  exact isCompact_range (gaussianCarrierToFiber L a c).continuous

/-- The actual shell unit is the carrier indicator on the whole fiber. -/
theorem gaussianCarrierUnit_trace_indicator (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) :
    (fun x : adelicValueFiber L a ↦ (gaussianCarrierUnit L b a hc).val x.val) =
      (fiberDividedCarrier L a c).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext x
  by_cases hx : x ∈ fiberDividedCarrier L a c
  · rw [Set.indicator_of_mem hx]
    exact gaussianCarrierUnit_on L b a hc ⟨x.property, hx⟩
  · rw [Set.indicator_of_notMem hx]
    have hloc := congrArg (fun f : realGaussianCore L b ↦ f.val x.val)
      (localizeGaussianCore_unit L b a hc)
    dsimp only at hloc
    rw [localizeGaussianCore_off L b c _ hx] at hloc
    exact hloc.symm

/-- Every old compact carrier has finite mass. Global finiteness is not asserted. -/
theorem gaussianFiberMeasure_carrier_lt_top (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    gaussianFiberMeasure L hn hb a (fiberDividedCarrier L a c) < ⊤ :=
  (isCompact_fiberDividedCarrier L a hc).measure_lt_top

/-- The carrier mass in real scalars is the density of the explicit unit.
This identifies the normalization source; it does not evaluate that density. -/
theorem gaussianFiberMeasure_real_carrier (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    (gaussianFiberMeasure L hn hb a).real (fiberDividedCarrier L a c) =
      L.rationalQuadraticSpaceMatrix.realValueDensity (gaussianCarrierUnit L b a hc).val a := by
  have h := integral_gaussianFiberMeasure_core L hn hb a (gaussianCarrierUnit L b a hc)
  rw [gaussianCarrierUnit_trace_indicator, integral_indicator_const (1 : ℝ)
    (isCompact_fiberDividedCarrier L a hc).isClosed.measurableSet, smul_eq_mul, mul_one] at h
  exact h

/-- The ENNReal mass formula retains finiteness before undoing `toReal`. -/
theorem gaussianFiberMeasure_carrier (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    gaussianFiberMeasure L hn hb a (fiberDividedCarrier L a c) =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianCarrierUnit L b a hc).val a) := by
  rw [← gaussianFiberMeasure_real_carrier L hn hb a hc, measureReal_def,
    ENNReal.ofReal_toReal (gaussianFiberMeasure_carrier_lt_top L hn hb a hc).ne]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
