import SMSFormula.AdelicGaussianTraceFunctional
import SMSFormula.RealShellCompactness

/-!
# Compact carrier pieces of the literal adelic fiber

The real component of the actual value equation is a polar ellipsoid with value
twice the real value. Intersecting the actual fiber with a divided finite
carrier is therefore compact. Localization multiplies by that old indicator
and preserves the actual Gaussian core; no replacement model of the fiber is used.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

/-- The value equation keeps the polar factor two. -/
theorem polarQuadraticForm_realPart_of_value (L : PositiveDefiniteIntegralLattice n)
    {x : Fin n → RationalAdele} {a : RationalAdele}
    (hx : L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a) :
    L.polarQuadraticForm (rationalAdeleVectorRealPart n x) =
      2 * rationalInfiniteAdeleContinuousAddEquivReal a.1 := by
  have hpolar : L.rationalQuadraticSpaceMatrix.realPolarMatrix =
      (2 : ℝ) • L.rationalQuadraticSpaceMatrix.realFormMatrix := by
    ext i j
    simp [realPolarMatrix, realFormMatrix, polarMatrix]
  rw [polarQuadraticForm_apply, hpolar, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hr := L.rationalQuadraticSpaceMatrix.rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue x
  rw [hx] at hr
  exact congrArg (fun r : ℝ ↦ 2 * r) hr.symm

/-- The old carrier intersected with the literal adelic value fiber. -/
def adelicFiberCarrier (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) :
    Set (Fin n → RationalAdele) :=
  {x | L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a ∧
    rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c}

theorem isCompact_adelicFiberCarrier (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) : IsCompact (adelicFiberCarrier L a c) := by
  have hS : Continuous (rationalAdeleVectorFinitePart n) := by
    unfold rationalAdeleVectorFinitePart; fun_prop
  have hclosed : IsClosed (adelicFiberCarrier L a c) :=
    (isClosed_eq L.rationalQuadraticSpaceMatrix.continuous_fullAdelicQuadraticFormValue
      continuous_const).inter ((isCompact_standardDividedLattice hc).isClosed.preimage hS)
  apply IsCompact.of_isClosed_subset
    (((L.isCompact_polarShell (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)).prod
      (isCompact_standardDividedLattice hc)).image continuous_realFiniteEquiv_symm) hclosed
  intro x hx
  refine ⟨(rationalAdeleVectorRealPart n x, rationalAdeleVectorFinitePart n x),
    ⟨polarQuadraticForm_realPart_of_value L hx.1, hx.2⟩, ?_⟩
  exact (rationalAdeleVectorRealFiniteEquiv n).symm_apply_apply x

instance compactSpace_adelicFiberCarrier (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (c : ℕ) [NeZero c] : CompactSpace (adelicFiberCarrier L a c) :=
  isCompact_iff_compactSpace.mp (isCompact_adelicFiberCarrier L a (NeZero.ne c))

/-- Localization by the finite carrier keeps the entire fixed-width core. On a
generator it only multiplies the finite factor; its period is unchanged. -/
theorem localize_mem_realGaussianCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    (fun x ↦ f x * (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ))
      (rationalAdeleVectorFinitePart n x)) ∈ realGaussianCore L b := by
  classical
  let I : (Fin n → RationalFiniteAdele) → ℝ :=
    (standardDividedLattice n c).indicator (fun _ ↦ 1)
  have hI : IsStandardPeriodic 1 (fun y ↦ (I y : ℂ)) := (dividedIndicator_standard c).2
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, e, d, g, he, hd, hcar, hper, rfl⟩ := hf
    have hgcar : IsStandardCarried e (fun y ↦ ((g y * I y : ℝ) : ℂ)) := by
      intro y hy
      have hz := Complex.ofReal_eq_zero.mp (hcar y hy)
      simp [hz]
    have hgper : IsStandardPeriodic d (fun y ↦ ((g y * I y : ℝ) : ℂ)) := by
      intro y z hz
      have hg := Complex.ofReal_injective (hper y z hz)
      have hi := Complex.ofReal_injective ((hI.mono (one_dvd d)) y z hz)
      dsimp only
      rw [hg, hi]
    apply Submodule.subset_span
    refine ⟨u, e, d, fun y ↦ g y * I y, he, hd, hgcar, hgper, ?_⟩
    funext x
    exact mul_assoc _ _ _
  | zero =>
    simpa only [Pi.zero_apply, zero_mul] using (realGaussianCore L b).zero_mem
  | add f g _ _ hf hg =>
    simpa only [Pi.add_apply, add_mul] using (realGaussianCore L b).add_mem hf hg
  | smul r f _ hf =>
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using (realGaussianCore L b).smul_mem r hf

/-- Multiplication by a carrier indicator as an endomorphism of the core. -/
def localizeGaussianCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ) :
    realGaussianCore L b →ₗ[ℝ] realGaussianCore L b where
  toFun f := ⟨fun x ↦ f.val x * (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ))
    (rationalAdeleVectorFinitePart n x), localize_mem_realGaussianCore L b c f.property⟩
  map_add' f g := by ext x; exact add_mul _ _ _
  map_smul' r f := by ext x; exact mul_assoc _ _ _

@[simp] theorem localizeGaussianCore_apply (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ)
    (f : realGaussianCore L b) (x : Fin n → RationalAdele) :
    (localizeGaussianCore L b c f).val x =
      f.val x * (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ))
        (rationalAdeleVectorFinitePart n x) := rfl

/-- On its carrier localization is the identity. -/
theorem localizeGaussianCore_on (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ)
    (f : realGaussianCore L b) {x : Fin n → RationalAdele}
    (hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c) :
    (localizeGaussianCore L b c f).val x = f.val x := by
  classical
  rw [localizeGaussianCore_apply, Set.indicator_of_mem hx, mul_one]

/-- Off its carrier localization is zero, including on the rest of the fiber. -/
theorem localizeGaussianCore_off (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ)
    (f : realGaussianCore L b) {x : Fin n → RationalAdele}
    (hx : rationalAdeleVectorFinitePart n x ∉ standardDividedLattice n c) :
    (localizeGaussianCore L b c f).val x = 0 := by
  classical
  rw [localizeGaussianCore_apply, Set.indicator_of_notMem hx, mul_zero]

/-- Multiplication by an indicator is a projection, not a normalization. -/
theorem localizeGaussianCore_idempotent (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (c : ℕ)
    (f : realGaussianCore L b) :
    localizeGaussianCore L b c (localizeGaussianCore L b c f) = localizeGaussianCore L b c f := by
  classical
  ext x
  by_cases hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · rw [localizeGaussianCore_on L b c _ hx]
  · rw [localizeGaussianCore_off L b c _ hx, localizeGaussianCore_off L b c _ hx]

/-- The centered test, scaled by the reciprocal of its nonzero shell value,
is a unit on the literal compact piece. The width stays fixed and positive. -/
def gaussianCarrierUnit (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) : realGaussianCore L b :=
  Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) •
    ⟨fun x ↦ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ)) (rationalAdeleVectorFinitePart n x),
      Submodule.subset_span ⟨0, c, 1, _, hc, one_ne_zero,
        (dividedIndicator_standard c).1, (dividedIndicator_standard c).2, rfl⟩⟩

theorem gaussianCarrierUnit_on (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) {x : Fin n → RationalAdele} (hx : x ∈ adelicFiberCarrier L a c) :
    (gaussianCarrierUnit L b a hc).val x = 1 := by
  classical
  change Real.exp _ * (realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
    (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ)) (rationalAdeleVectorFinitePart n x)) = 1
  rw [Set.indicator_of_mem hx.2, mul_one, realShiftedGaussian_eq,
    SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  simp only [ContinuousMap.id_apply, sub_zero]
  rw [polarQuadraticForm_realPart_of_value L hx.1, ← Real.exp_add]
  simp

theorem localizeGaussianCore_unit (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) :
    localizeGaussianCore L b c (gaussianCarrierUnit L b a hc) = gaussianCarrierUnit L b a hc := by
  classical
  ext x
  by_cases hx : rationalAdeleVectorFinitePart n x ∈ standardDividedLattice n c
  · exact localizeGaussianCore_on L b c _ hx
  · rw [localizeGaussianCore_off L b c _ hx]
    simp [gaussianCarrierUnit, hx]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
