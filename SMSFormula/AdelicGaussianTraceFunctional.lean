import SMSFormula.AdelicGaussianTracePositivity
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.Submodule.Order

/-!
# The value-density functional on the actual restriction image

Trace-zero annihilation lets the existing Fourier value density factor through
the kernel quotient of restriction, then the first isomorphism theorem identifies
that quotient with the restriction image. No map choosing ambient extensions is
introduced. Positivity is proved on the actual image, not assumed of an operator.
This does not extend the functional to all compactly supported shell tests.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- Every member of the real core is continuous; the trace therefore belongs
to continuous functions on the literal adelic fiber. -/
theorem continuous_of_mem_realGaussianCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, c, d, g, _, hd, _, hper, rfl⟩ := hf
    have hg : Continuous g := by simpa using Complex.continuous_re.comp (hper.continuous hd)
    have hR : Continuous (rationalAdeleVectorRealPart n) := by
      unfold rationalAdeleVectorRealPart; fun_prop
    have hS : Continuous (rationalAdeleVectorFinitePart n) := by
      unfold rationalAdeleVectorFinitePart; fun_prop
    exact ((continuous_realShiftedGaussian L b u).comp hR).mul (hg.comp hS)
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf =>
    simpa only [Pi.smul_apply, smul_eq_mul] using (continuous_const.mul hf : Continuous (fun x ↦ c * f x))

/-- Restriction to the literal value fiber. This uses no shell point, rational
representative, quotient section or extension of a shell function. -/
def realGaussianTrace (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) :
    realGaussianCore L b →ₗ[ℝ]
      C({x : Fin n → RationalAdele // L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a}, ℝ) where
  toFun f := ⟨fun x ↦ f.val x.val, (continuous_of_mem_realGaussianCore L b f.property).comp continuous_subtype_val⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- The existing real Fourier density, as a linear map on its verified domain. -/
def realGaussianDensityLinearMap (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) : realGaussianCore L b →ₗ[ℝ] ℝ where
  toFun f := L.rationalQuadraticSpaceMatrix.realValueDensity f.val a
  map_add' f g := by
    change L.rationalQuadraticSpaceMatrix.realValueDensity (f.val + g.val) a = _
    rw [L.rationalQuadraticSpaceMatrix.realValueDensity_add
      (hasSignedValueDensity_of_mem_real_span L hn hb f.property).1
      (hasSignedValueDensity_of_mem_real_span L hn hb g.property).1]
    rfl
  map_smul' c f := by
    change L.rationalQuadraticSpaceMatrix.realValueDensity (c • f.val) a = _
    rw [L.rationalQuadraticSpaceMatrix.realValueDensity_smul]
    rfl

/-- The proved trace-zero theorem is exactly the kernel inclusion needed to
descend the functional. This is not supplied as an extra hypothesis. -/
theorem ker_realGaussianTrace_le_ker_density (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    (realGaussianTrace L b a).ker ≤ (realGaussianDensityLinearMap L hn hb a).ker := by
  intro f hf
  apply LinearMap.mem_ker.mpr
  apply realValueDensity_eq_zero_of_trace_zero L hn hb f.property a
  intro x hx
  have h := congrArg (fun g ↦ g ⟨x, hx⟩) (LinearMap.mem_ker.mp hf)
  exact h

/-- The actual functional on the image of restriction. It factors through the
kernel quotient, not a choice of an ambient extension for each trace. -/
def realGaussianTraceDensity (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    (realGaussianTrace L b a).range →ₗ[ℝ] ℝ :=
  ((realGaussianTrace L b a).ker.liftQ (realGaussianDensityLinearMap L hn hb a)
    (ker_realGaussianTrace_le_ker_density L hn hb a)).comp
    (realGaussianTrace L b a).quotKerEquivRange.symm.toLinearMap

/-- Recovery at every supplied core test: the functional is exactly its old
Fourier value density, with no unknown proportionality constant. -/
@[simp] theorem realGaussianTraceDensity_apply (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    realGaussianTraceDensity L hn hb a ((realGaussianTrace L b a).rangeRestrict f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a := by
  unfold realGaussianTraceDensity
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have heq : (realGaussianTrace L b a).rangeRestrict f =
      (realGaussianTrace L b a).quotKerEquivRange ((realGaussianTrace L b a).ker.mkQ f) := by
    apply Subtype.ext
    rfl
  rw [heq, LinearEquiv.symm_apply_apply]
  rfl

/-- Positivity on the actual image follows from trace positivity, even if the
ambient test changes sign off the fiber. -/
theorem realGaussianTraceDensity_nonneg (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (g : (realGaussianTrace L b a).range) (hg : 0 ≤ g) :
    0 ≤ realGaussianTraceDensity L hn hb a g := by
  obtain ⟨f, hf⟩ := g.property
  have heq : g = (realGaussianTrace L b a).rangeRestrict f := Subtype.ext hf.symm
  rw [heq, realGaussianTraceDensity_apply]
  apply realValueDensity_nonneg_of_trace_nonneg L hn hb f.property a
  intro x hx
  have h := hg ⟨x, hx⟩
  rw [heq] at h
  exact h

/-- The positive linear map is constructed on the restriction image. Extension
to `C_c` and calibration against the native orbital measure remain separate. -/
def realGaussianTracePositiveFunctional (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    (realGaussianTrace L b a).range →ₚ[ℝ] ℝ :=
  { realGaussianTraceDensity L hn hb a with
    monotone' := fun f g hfg ↦ by
      have h := realGaussianTraceDensity_nonneg L hn hb a (g - f) (sub_nonneg.mpr hfg)
      rw [map_sub] at h
      exact sub_nonneg.mp h }

@[simp] theorem realGaussianTracePositiveFunctional_apply (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : realGaussianCore L b) :
    realGaussianTracePositiveFunctional L hn hb a ((realGaussianTrace L b a).rangeRestrict f) =
      L.rationalQuadraticSpaceMatrix.realValueDensity f.val a :=
  realGaussianTraceDensity_apply L hn hb a f

/-- Recovery on all supplied core tests uniquely specifies the map on the
restriction image. The arbitrary-functional ambiguity of the retired extension
package is absent here. This still says nothing about native normalization. -/
theorem realGaussianTraceDensity_unique (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (F : (realGaussianTrace L b a).range →ₗ[ℝ] ℝ)
    (hF : ∀ f : realGaussianCore L b,
      F ((realGaussianTrace L b a).rangeRestrict f) =
        L.rationalQuadraticSpaceMatrix.realValueDensity f.val a) :
    F = realGaussianTraceDensity L hn hb a := by
  ext g
  obtain ⟨f, hf⟩ := g.property
  have heq : g = (realGaussianTrace L b a).rangeRestrict f := Subtype.ext hf.symm
  rw [heq, hF, realGaussianTraceDensity_apply]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
