import SMSFormula.AdelicGaussianFiberMeasure
import SMSFormula.RationalAdeleFiniteLocalRestrictedResidueCount

/-!
# The residue-restricted Gaussian unit: the orbit test

For supplied residue data `(N₀, R)` the normalized test

`Φ(x) = exp(2πb a_∞) · e^{-πb Q(x_∞)} · 1_{U_R}(x_f)`

is a member of the real Gaussian core (a shifted Gaussian at centre `0` times the
standard-carried periodic residue indicator).  On the value fiber `{Q = a}` its trace is exactly
the indicator of `{x_f ∈ U_R}`: the Gaussian factor is `1` on the integral part of the fiber
(carrier unit), and the residue indicator vanishes off it.  Hence, by the Riesz
characterization,

`σ({x ∈ X_a : x_f ∈ U_R}) = d_Φ(a)`   (`ENNReal.ofReal` of the value density).

This is the shell-trace step; the finite part of `d_Φ(a)` is the
replacement lemma.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix CompactlySupported MeasureTheory

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The real-valued residue-restricted indicator. -/
def realResidueRestrictedIndicator (n N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (y : Fin n → RationalFiniteAdele) : ℝ :=
  (residueRestrictedIndicator n N₀ R y).re

theorem coe_realResidueRestrictedIndicator (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    (y : Fin n → RationalFiniteAdele) :
    ((realResidueRestrictedIndicator n N₀ R y : ℝ) : ℂ) = residueRestrictedIndicator n N₀ R y := by
  unfold realResidueRestrictedIndicator residueRestrictedIndicator
  split_ifs <;> simp

theorem realResidueRestrictedIndicator_eq_zero_or_one (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) (y : Fin n → RationalFiniteAdele) :
    realResidueRestrictedIndicator n N₀ R y = 0 ∨ realResidueRestrictedIndicator n N₀ R y = 1 := by
  unfold realResidueRestrictedIndicator residueRestrictedIndicator
  split_ifs <;> simp

theorem mem_integral_of_realResidueRestrictedIndicator_ne_zero (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) {y : Fin n → RationalFiniteAdele}
    (hy : realResidueRestrictedIndicator n N₀ R y ≠ 0) :
    y ∈ standardDividedLattice n 1 := by
  by_contra h
  apply hy
  have h' : y ∉ integralFiniteAdeleVectors n := by simpa [standardDividedLattice] using h
  unfold realResidueRestrictedIndicator residueRestrictedIndicator
  rw [dif_neg h']
  simp

/-- The residue-restricted Gaussian unit, a member of the real Gaussian core. -/
def gaussianResidueRestrictedUnit (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀)) : realGaussianCore L b :=
  Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) •
    ⟨fun x ↦ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x),
      Submodule.subset_span ⟨0, 1, N₀, realResidueRestrictedIndicator n N₀ R, one_ne_zero,
        NeZero.ne N₀,
        by simpa only [coe_realResidueRestrictedIndicator] using
          isStandardCarried_residueRestrictedIndicator (n := n) N₀ R,
        by simpa only [coe_realResidueRestrictedIndicator] using
          isStandardPeriodic_residueRestrictedIndicator (n := n) N₀ R, rfl⟩⟩

/-- On the value fiber, the unit is the residue-restricted indicator of the finite part. -/
theorem gaussianResidueRestrictedUnit_apply_of_value (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀))
    {x : Fin n → RationalAdele}
    (hx : L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a) :
    (gaussianResidueRestrictedUnit L b a N₀ R).val x =
      realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x) := by
  classical
  change Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
      (realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
        realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x)) = _
  by_cases hg : realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x) = 0
  · rw [hg]; ring
  · have hcar : x ∈ adelicFiberCarrier L a 1 :=
      ⟨hx, mem_integral_of_realResidueRestrictedIndicator_ne_zero N₀ R hg⟩
    have hone := gaussianCarrierUnit_on L b a one_ne_zero hcar
    change Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
      (realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
        (standardDividedLattice n 1).indicator (fun _ ↦ (1 : ℝ))
          (rationalAdeleVectorFinitePart n x)) = 1 at hone
    rw [Set.indicator_of_mem hcar.2, mul_one] at hone
    calc _ = (Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
          realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x)) *
          realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x) := by ring
      _ = _ := by rw [hone, one_mul]

/-- The fiber set carried by the residue data: `{x ∈ X_a : x_f ∈ U_R}`. -/
def fiberResidueRestrictedSet (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin n → ZMod N₀)) : Set (adelicValueFiber L a) :=
  {x | realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x.val) = 1}

/-- The trace of the unit is the indicator of the carried fiber set. -/
theorem gaussianResidueRestrictedUnit_trace_indicator (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀)) :
    (fun x : adelicValueFiber L a ↦ (gaussianResidueRestrictedUnit L b a N₀ R).val x.val) =
      (fiberResidueRestrictedSet L a N₀ R).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext x
  rw [gaussianResidueRestrictedUnit_apply_of_value L b a N₀ R x.property]
  rcases realResidueRestrictedIndicator_eq_zero_or_one N₀ R
      (rationalAdeleVectorFinitePart n x.val) with h | h
  · rw [Set.indicator_of_notMem (by simp [fiberResidueRestrictedSet, h]), h]
  · rw [Set.indicator_of_mem (show x ∈ fiberResidueRestrictedSet L a N₀ R from h), h]

/-- The σ-mass of the carried fiber set is the value density of the orbit test. -/
theorem gaussianFiberMeasure_fiberResidueRestrictedSet (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀)) :
    gaussianFiberMeasure L hn hb a (fiberResidueRestrictedSet L a N₀ R) =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianResidueRestrictedUnit L b a N₀ R).val a) := by
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
  have hfin : gaussianFiberMeasure L hn hb a (fiberResidueRestrictedSet L a N₀ R) ≠ ⊤ :=
    ((measure_mono hsub).trans_lt (gaussianFiberMeasure_carrier_lt_top L hn hb a one_ne_zero)).ne
  have h := integral_gaussianFiberMeasure_core L hn hb a (gaussianResidueRestrictedUnit L b a N₀ R)
  rw [gaussianResidueRestrictedUnit_trace_indicator, integral_indicator_const (1 : ℝ)
    hclosed.measurableSet, smul_eq_mul, mul_one] at h
  rw [← h, measureReal_def, ENNReal.ofReal_toReal hfin]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
