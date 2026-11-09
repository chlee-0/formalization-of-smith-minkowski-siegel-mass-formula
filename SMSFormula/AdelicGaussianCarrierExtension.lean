import SMSFormula.AdelicGaussianCarrierAlgebra

/-!
# Positive extension on each compact fiber piece

All hypotheses of the positive extension theorem are proved here: compactness,
positivity on the image, its explicit unit, and density of that image.
Recovery gives the Fourier density of the localized test. The value at one
is kept; no probability or orbital normalization is imposed.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- The positive continuous extension on all continuous functions on the
literal compact piece. This uses the existing bounded-map extension. -/
def gaussianCarrierExtension (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c] :
    C(adelicFiberCarrier L a c, ℝ) →L[ℝ] ℝ :=
  SMSFormula.ShellLocalBound.extendToAll (gaussianCarrierTraceDensity L hn hb a c)
    (fun g hg ↦ gaussianCarrierTraceDensity_nonneg L hn hb a c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)

/-- Exact recovery for every old core test, after localization to this carrier. -/
@[simp] theorem gaussianCarrierExtension_trace (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (f : realGaussianCore L b) :
    gaussianCarrierExtension L hn hb a c (gaussianCarrierTrace L b a c f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity (localizeGaussianCore L b c f).val a := by
  have h := SMSFormula.ShellLocalBound.extendToAll_apply
    (V := (gaussianCarrierTrace L b a c).range) (gaussianCarrierTraceDensity L hn hb a c)
    (fun g hg ↦ gaussianCarrierTraceDensity_nonneg L hn hb a c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)
    (dense_gaussianCarrierTrace L hb a c) ((gaussianCarrierTrace L b a c).rangeRestrict f)
  change gaussianCarrierExtension L hn hb a c (gaussianCarrierTrace L b a c f) =
    gaussianCarrierTraceDensity L hn hb a c ((gaussianCarrierTrace L b a c).rangeRestrict f) at h
  rw [gaussianCarrierTraceDensity_apply] at h
  exact h

theorem gaussianCarrierExtension_nonneg (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (f : C(adelicFiberCarrier L a c, ℝ)) (hf : 0 ≤ f) :
    0 ≤ gaussianCarrierExtension L hn hb a c f :=
  SMSFormula.ShellLocalBound.extendToAll_nonneg
    (V := (gaussianCarrierTrace L b a c).range) (gaussianCarrierTraceDensity L hn hb a c)
    (fun g hg ↦ gaussianCarrierTraceDensity_nonneg L hn hb a c g hg)
    (gaussianCarrierTraceUnit L b a (NeZero.ne c))
    (fun x ↦ le_of_eq (gaussianCarrierTraceUnit_apply L b a (NeZero.ne c) x).symm)
    (dense_gaussianCarrierTrace L hb a c) f hf

/-- The extension still has the old density as its unit value; this is not
an evaluation of that number and does not identify it with any native mass. -/
theorem gaussianCarrierExtension_one (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c] :
    gaussianCarrierExtension L hn hb a c 1 =
      L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianCarrierUnit L b a (NeZero.ne c)).val a := by
  have hu : gaussianCarrierTrace L b a c (gaussianCarrierUnit L b a (NeZero.ne c)) = 1 := by
    ext x
    exact gaussianCarrierUnit_on L b a (NeZero.ne c) x.property
  rw [← hu, gaussianCarrierExtension_trace, localizeGaussianCore_unit]

/-- Positivity supplies the order bound on all continuous tests, with the
same explicit unit value as on the core. -/
theorem abs_gaussianCarrierExtension_le (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (f : C(adelicFiberCarrier L a c, ℝ)) :
    |gaussianCarrierExtension L hn hb a c f| ≤ ‖f‖ *
      L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianCarrierUnit L b a (NeZero.ne c)).val a := by
  let Λ := gaussianCarrierExtension L hn hb a c
  have hplus : 0 ≤ Λ ((‖f‖ : ℝ) • (1 : C(adelicFiberCarrier L a c, ℝ)) + f) := by
    apply gaussianCarrierExtension_nonneg
    intro x
    have hx := f.norm_coe_le_norm x
    change 0 ≤ ‖f‖ * 1 + f x
    rw [mul_one]
    rw [Real.norm_eq_abs] at hx
    linarith [(abs_le.mp hx).1]
  have hminus : 0 ≤ Λ ((‖f‖ : ℝ) • (1 : C(adelicFiberCarrier L a c, ℝ)) - f) := by
    apply gaussianCarrierExtension_nonneg
    intro x
    have hx := f.norm_coe_le_norm x
    change 0 ≤ ‖f‖ * 1 - f x
    rw [mul_one]
    rw [Real.norm_eq_abs] at hx
    linarith [(abs_le.mp hx).2]
  rw [map_add, map_smul, smul_eq_mul] at hplus
  rw [map_sub, map_smul, smul_eq_mul] at hminus
  change 0 ≤ ‖f‖ * gaussianCarrierExtension L hn hb a c 1 + Λ f at hplus
  change 0 ≤ ‖f‖ * gaussianCarrierExtension L hn hb a c 1 - Λ f at hminus
  rw [gaussianCarrierExtension_one] at hplus hminus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The extension is unique from continuity and its proved recovery on the core. -/
theorem gaussianCarrierExtension_unique (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (c : ℕ) [NeZero c]
    (Λ : C(adelicFiberCarrier L a c, ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ f : realGaussianCore L b,
      Λ (gaussianCarrierTrace L b a c f) =
        L.rationalQuadraticSpaceMatrix.realValueDensity (localizeGaussianCore L b c f).val a) :
    Λ = gaussianCarrierExtension L hn hb a c := by
  have hdense : DenseRange (gaussianCarrierTrace L b a c) := dense_gaussianCarrierTrace L hb a c
  ext f
  exact hdense.induction_on f
    (isClosed_eq Λ.continuous (gaussianCarrierExtension L hn hb a c).continuous)
    (fun g ↦ (hΛ g).trans (gaussianCarrierExtension_trace L hn hb a c g).symm)

theorem dividedCarrier_subset_of_dvd {c d : ℕ} (hcd : c ∣ d) :
    standardDividedLattice n c ⊆ standardDividedLattice n d := by
  obtain ⟨k, rfl⟩ := hcd
  intro x hx
  change (c * k) • x ∈ integralFiniteAdeleVectors n
  rw [mul_nsmul]
  exact nsmul_mem_integralFiniteAdeleVectors hx

/-- A larger old carrier does not change a test already localized to the smaller one. -/
theorem localizeGaussianCore_absorb (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    {c d : ℕ} (hcd : c ∣ d) (f : realGaussianCore L b) :
    localizeGaussianCore L b d (localizeGaussianCore L b c f) = localizeGaussianCore L b c f := by
  ext x
  by_cases hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · exact localizeGaussianCore_on L b d _ (dividedCarrier_subset_of_dvd hcd hx)
  · rw [localizeGaussianCore_apply, localizeGaussianCore_off L b c f hx, zero_mul]

/-- Continuous inclusion of supplied subsets; shared by compact pieces and the full fiber. -/
def subsetInclusionMap {X : Type*} [TopologicalSpace X]
    (S T : Set X) (h : S ⊆ T) : C(S, T) :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

theorem subsetInclusionMap_val {X : Type*} [TopologicalSpace X]
    (S T : Set X) (h : S ⊆ T) (x : S) :
    (subsetInclusionMap S T h x).val = x.val := rfl

/-- The literal inclusion of nested carrier pieces. Bundling the subset inclusion
abstractly avoids unfolding the whole adelic value equation in its evaluation. -/
def gaussianCarrierInclusion (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c d : ℕ} (hcd : c ∣ d) : C(adelicFiberCarrier L a c, adelicFiberCarrier L a d) :=
  subsetInclusionMap _ _ (fun _ hx ↦ ⟨hx.1, dividedCarrier_subset_of_dvd hcd hx.2⟩)

theorem gaussianCarrierInclusion_val (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c d : ℕ} (hcd : c ∣ d) (x : adelicFiberCarrier L a c) :
    (gaussianCarrierInclusion L a hcd x).val = x.val :=
  subsetInclusionMap_val _ _ _ x

/-- The old smaller-carrier indicator, restricted to a literal larger piece. -/
def gaussianCarrierIndicator (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) (d : ℕ) : C(adelicFiberCarrier L a d, ℝ) :=
  ⟨fun x ↦ (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ))
      (rationalAdeleVectorFinitePart n x.val),
    ((isClopen_standardDividedLattice hc).continuous_indicator continuous_const).comp
      ((show Continuous (rationalAdeleVectorFinitePart n) by
        unfold rationalAdeleVectorFinitePart; fun_prop).comp continuous_subtype_val)⟩

theorem gaussianCarrierTrace_localize (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) (d : ℕ) (g : realGaussianCore L b) :
    gaussianCarrierTrace L b a d g * gaussianCarrierIndicator L a hc d =
      gaussianCarrierTrace L b a d (localizeGaussianCore L b c g) := by
  ext x
  rfl

theorem gaussianCarrierTrace_restrict (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) {c d : ℕ} (hcd : c ∣ d) (g : realGaussianCore L b) :
    (gaussianCarrierTrace L b a d g).comp (gaussianCarrierInclusion L a hcd) =
      gaussianCarrierTrace L b a c g := by
  apply ContinuousMap.ext
  intro x
  change g.val (gaussianCarrierInclusion L a hcd x).val = g.val x.val
  rw [gaussianCarrierInclusion_val]

private theorem extension_compatible_core (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (g : realGaussianCore L b) :
    gaussianCarrierExtension L hn hb a d
        (gaussianCarrierTrace L b a d g * gaussianCarrierIndicator L a (NeZero.ne c) d) =
      gaussianCarrierExtension L hn hb a c
        ((gaussianCarrierTrace L b a d g).comp (gaussianCarrierInclusion L a hcd)) := by
  rw [gaussianCarrierTrace_localize, gaussianCarrierTrace_restrict,
    gaussianCarrierExtension_trace, gaussianCarrierExtension_trace,
    localizeGaussianCore_absorb L b hcd]

/-- Compatibility for every continuous test on the larger piece: localization
there equals restriction to the smaller piece. The two unit masses are not equated. -/
theorem gaussianCarrierExtension_compatible (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (f : C(adelicFiberCarrier L a d, ℝ)) :
    gaussianCarrierExtension L hn hb a d
        (f * gaussianCarrierIndicator L a (NeZero.ne c) d) =
      gaussianCarrierExtension L hn hb a c (f.comp (gaussianCarrierInclusion L a hcd)) := by
  have hdense : DenseRange (gaussianCarrierTrace L b a d) := dense_gaussianCarrierTrace L hb a d
  refine hdense.induction_on f (isClosed_eq
    ((gaussianCarrierExtension L hn hb a d).continuous.comp (continuous_id.mul continuous_const))
    ((gaussianCarrierExtension L hn hb a c).continuous.comp
      (ContinuousMap.continuous_precomp (gaussianCarrierInclusion L a hcd)))) ?_
  exact extension_compatible_core L hn hb a hcd

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
