import SMSFormula.AdelicGaussianRankFourDensity
import SMSFormula.RationalAdeleStandardFactorTubePositivity
import SMSFormula.AdelicGaussianTracePositiveDensityMeasure

/-!
# Trace positivity of the rank-four density

If a core test `f` is nonnegative on the literal adelic fiber `X_M = {Q = M}`, then for every `x_f`
on the finite fiber `{Q_f = M}` its real section is nonnegative on the real sphere `{Q_ℝ = M}`, so
the real orbit average through a supplied point `x₀` of the sphere is nonnegative; by
`RationalAdeleStandardFactorTubePositivity` the finite tube limit of these averages has nonnegative
real part. Hence the rank-four density `rankFourDensityLinearMap` (with `c_∞ ≥ 0`) is
trace-positive, and packages as a `TracePositiveCoreDensity` (`rankFourTracePositiveDensity`): its
Riesz fiber measure exists (`AdelicGaussianTracePositiveDensityMeasure`). Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The real quadratic value of an integer vector is its integer value. -/
theorem realQuadraticFormValue_intVector (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.realQuadraticFormValue (fun i ↦ (z i : ℝ)) =
      ((L.quadForm z : ℤ) : ℝ) := by
  have h : L.rationalQuadraticSpaceMatrix.realFormMatrix = L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp [RationalQuadraticSpaceMatrix.realFormMatrix, rationalQuadraticSpaceMatrix_pairingMatrix,
      PositiveDefiniteIntegralLattice.rationalFormMatrix]
  rw [RationalQuadraticSpaceMatrix.realQuadraticFormValue, h, L.quadForm_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  push_cast
  rfl

/-- The adelic join lies on the fiber when its real part lies on the real sphere and its finite part
on the finite fiber. -/
theorem fullAdelicQuadraticFormValue_join_eq (V : RationalQuadraticSpaceMatrix n) (q : ℚ)
    {xr : Fin n → ℝ} {xf : Fin n → RationalFiniteAdele}
    (hr : V.realQuadraticFormValue xr = (q : ℝ))
    (hf : V.finiteAdelicQuadraticFormValue xf = algebraMap ℚ RationalFiniteAdele q) :
    V.fullAdelicQuadraticFormValue (rationalAdeleVectorJoin n xr xf) = algebraMap ℚ RationalAdele q := by
  refine Prod.ext ?_ ?_
  · apply rationalInfiniteAdeleContinuousAddEquivReal.injective
    rw [rationalAdeleVectorRealPart_fullAdelicQuadraticFormValue, rationalAdeleVectorRealPart_join, hr]
    change _ = rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele q)
    rw [rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
    rfl
  · rw [rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue, rationalAdeleVectorFinitePart_join,
      hf]
    rfl

/-- Trace positivity of the rank-four density. -/
theorem rankFourDensityLinearMap_nonneg_of_trace_nonneg (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ)
    (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ = ((M : ℤ) : ℝ))
    {cInf : ℝ} (hc : 0 ≤ cInf) (f : realGaussianCore L b)
    (hf : ∀ x, L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x =
      algebraMap ℚ RationalAdele ((M : ℤ) : ℚ) → 0 ≤ f.val x) :
    0 ≤ rankFourDensityLinearMap L hn hM hb x₀ cInf f := by
  rw [rankFourDensityLinearMap_apply]
  refine mul_nonneg hc ?_
  obtain ⟨c, d, hc0, hd0, hcar, hper⟩ := exists_standard_finiteSectionAverage L hb x₀ f.property
  refine L.re_nonneg_of_tendsto_finiteTubeMass_of_fiber_nonneg hn hM hc0 hd0 hcar hper ?_
    (tendsto_rankFourFiniteDensity L hn hM hb x₀ f.property)
  intro xf hxf
  refine L.rationalQuadraticSpaceMatrix.realOrbitAverage_nonneg_of_sphere x₀ fun xr hxr ↦ ?_
  refine hf _ (fullAdelicQuadraticFormValue_join_eq _ ((M : ℤ) : ℚ) ?_ hxf)
  rw [hxr, hx₀]
  push_cast
  rfl

/-- The rank-four density as a trace-positive core density at the adelic value `a = M`. -/
def rankFourTracePositiveDensity (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0)
    {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ)
    (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ = ((M : ℤ) : ℝ))
    {cInf : ℝ} (hc : 0 ≤ cInf) (a : RationalAdele) (ha : a = algebraMap ℚ RationalAdele ((M : ℤ) : ℚ)) :
    TracePositiveCoreDensity L b a where
  toLinearMap := rankFourDensityLinearMap L hn hM hb x₀ cInf
  nonneg_of_trace_nonneg f hf :=
    rankFourDensityLinearMap_nonneg_of_trace_nonneg L hn hM hb x₀ hx₀ hc f fun x hx ↦ hf x (hx.trans ha.symm)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
