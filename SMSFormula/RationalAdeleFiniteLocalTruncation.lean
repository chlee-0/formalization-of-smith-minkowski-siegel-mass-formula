import SMSFormula.RationalAdeleFiniteLocalUnitLevel

/-!
# The truncated finite local integral is a level-`m` local density

The finite local integral is absolutely convergent but not evaluated.  This file
evaluates every truncation of it: cutting the integration variable down to the `m`-divided
integral finite adeles turns the integral into `m` times the measure of an explicit
congruence set inside the integral carrier,

```text
int_{A_fin} 1_Ztilde(m y) psi_{-b}(y) G(y) dy
  = m * (measure of {x in Ztilde^n : Q(x) - b in m Ztilde}).
```

Everything used is existing: the Gauss integral is an integral of the phase against
the carrier, the character splits the two frequencies, the existing scalar Haar
scaling law transports the truncation, and the existing self-duality of the indicator
evaluates the inner character integral.  No section of any quotient is chosen and no Euler
product is asserted.

Negative scope: this is a truncation, not the full integral.  The limit is not taken here,
the congruence measure is not identified with a residue count, and no comparison with the
representation number follows.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open MeasureTheory RationalQuadraticSpaceMatrix Filter Topology
open scoped NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_sigmaFinite' (d : ℕ) :
    SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure
  infer_instance

/-- The vector carrier has measure one. -/
theorem measure_integralFiniteAdeleVectors (d : ℕ) :
    rationalFiniteAdeleCoordinateAddHaarMeasure d (integralFiniteAdeleVectors d) = 1 := by
  rw [show integralFiniteAdeleVectors d =
      Set.univ.pi fun _ : Fin d => (integralFiniteAdeleSubring : Set RationalFiniteAdele) from by
    ext x
    simp [integralFiniteAdeleVectors]]
  change (Measure.pi fun _ : Fin d => rationalFiniteAdeleAddHaarMeasure)
    (Set.univ.pi fun _ : Fin d => (integralFiniteAdeleSubring : Set RationalFiniteAdele)) = 1
  rw [Measure.pi_pi]
  simp

/-- The `m`-divided integral finite adeles, as the literal preimage of the carrier. -/
theorem natScalePreimage_eq_image {m : ℕ} (hm : m ≠ 0) :
    (fun y : RationalFiniteAdele => (m : RationalFiniteAdele) * y) ⁻¹'
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) =
      (fun y : RationalFiniteAdele =>
        algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * y) ''
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) := by
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hcast : (m : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by
    norm_num
  ext y
  constructor
  · intro hy
    refine ⟨(m : RationalFiniteAdele) * y, hy, ?_⟩
    show algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
      ((m : RationalFiniteAdele) * y) = y
    rw [hcast, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hmq, map_one, one_mul]
  · rintro ⟨z, hz, rfl⟩
    show (m : RationalFiniteAdele) *
      (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ * z) ∈ integralFiniteAdeleSubring
    rw [hcast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hmq, map_one, one_mul]
    exact hz

/-- The truncated indicator is the indicator of a compact open set, hence integrable. -/
theorem integrable_natScaleIndicator {m : ℕ} (hm : m ≠ 0) :
    Integrable (fun y : RationalFiniteAdele =>
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y))
      rationalFiniteAdeleAddHaarMeasure := by
  have hq : ((m : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hm)
  set S : Set RationalFiniteAdele :=
    (fun y : RationalFiniteAdele => (m : RationalFiniteAdele) * y) ⁻¹'
      (integralFiniteAdeleSubring : Set RationalFiniteAdele) with hS
  have hopen : IsOpen S := by
    refine IsOpen.preimage ?_ isOpen_integralFiniteAdeleSubring
    exact continuous_const.mul continuous_id
  have hcompact : IsCompact S := by
    rw [hS, natScalePreimage_eq_image hm]
    exact isCompact_integralFiniteAdeleSubring.image
      (continuous_rationalFiniteAdeleScaleAddEquiv hq)
  have hfin : rationalFiniteAdeleAddHaarMeasure S < ⊤ := hcompact.measure_lt_top
  have heq : (fun y : RationalFiniteAdele =>
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y)) =
      Set.indicator S (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : (m : RationalFiniteAdele) * y ∈ integralFiniteAdeleSubring
    · rw [rationalFiniteAdeleIntegralIndicator_of_mem hy,
        Set.indicator_of_mem (show y ∈ S from hy)]
    · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hy,
        Set.indicator_of_notMem (show y ∉ S from hy)]
  rw [heq]
  exact (integrableOn_const (C := (1 : ℂ)) hfin.ne).integrable_indicator
    hopen.measurableSet

/-- The vector indicator is a literal set indicator. -/
theorem vectorIntegralIndicator_eq_indicator (d : ℕ) :
    (rationalFiniteAdeleVectorIntegralIndicator : (Fin d → RationalFiniteAdele) → ℂ) =
      Set.indicator (integralFiniteAdeleVectors d) (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : x ∈ integralFiniteAdeleVectors d
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx, Set.indicator_of_notMem hx]

theorem measurable_vectorIntegralIndicator (d : ℕ) :
    Measurable (rationalFiniteAdeleVectorIntegralIndicator :
      (Fin d → RationalFiniteAdele) → ℂ) := by
  rw [vectorIntegralIndicator_eq_indicator d]
  exact measurable_const.indicator (isOpen_integralFiniteAdeleVectors d).measurableSet

theorem measurable_natScaleIndicator {m : ℕ} :
    Measurable (fun y : RationalFiniteAdele =>
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y)) := by
  have hS : IsOpen ((fun y : RationalFiniteAdele => (m : RationalFiniteAdele) * y) ⁻¹'
      (integralFiniteAdeleSubring : Set RationalFiniteAdele)) :=
    IsOpen.preimage (continuous_const.mul continuous_id) isOpen_integralFiniteAdeleSubring
  have heq : (fun y : RationalFiniteAdele =>
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y)) =
      Set.indicator ((fun y : RationalFiniteAdele => (m : RationalFiniteAdele) * y) ⁻¹'
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)) (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : (m : RationalFiniteAdele) * y ∈ integralFiniteAdeleSubring
    · rw [rationalFiniteAdeleIntegralIndicator_of_mem hy,
        Set.indicator_of_mem (show y ∈ (fun y : RationalFiniteAdele =>
          (m : RationalFiniteAdele) * y) ⁻¹'
          (integralFiniteAdeleSubring : Set RationalFiniteAdele) from hy)]
    · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hy,
        Set.indicator_of_notMem (show y ∉ (fun y : RationalFiniteAdele =>
          (m : RationalFiniteAdele) * y) ⁻¹'
          (integralFiniteAdeleSubring : Set RationalFiniteAdele) from hy)]
  rw [heq]
  exact measurable_const.indicator hS.measurableSet

/-- The vector carrier indicator is integrable. -/
theorem integrable_vectorIntegralIndicator (d : ℕ) :
    Integrable (rationalFiniteAdeleVectorIntegralIndicator :
        (Fin d → RationalFiniteAdele) → ℂ)
      (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  rw [vectorIntegralIndicator_eq_indicator d]
  have hfin : rationalFiniteAdeleCoordinateAddHaarMeasure d
      (integralFiniteAdeleVectors d) ≠ ⊤ := by
    rw [measure_integralFiniteAdeleVectors d]
    simp
  exact (integrableOn_const (C := (1 : ℂ)) hfin).integrable_indicator
    (isOpen_integralFiniteAdeleVectors d).measurableSet

theorem continuous_quadraticPhaseAt_uncurry (L : PositiveDefiniteIntegralLattice n) :
    Continuous (fun p : RationalFiniteAdele × (Fin n → RationalFiniteAdele) =>
      ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt p.1 p.2 :
        Circle) : ℂ)) := by
  refine continuous_induced_dom.comp ?_
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
    RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
  refine continuous_rationalFiniteAdeleFourierChar.comp ?_
  fun_prop

set_option maxHeartbeats 1000000 in
/-- The truncated finite local integral is a level-`m` congruence measure. -/
theorem integral_natScaleTruncated_finiteLocal (L : PositiveDefiniteIntegralLattice n) {m : ℕ} (hm : m ≠ 0)
    (b : ℚ) :
    (∫ y : RationalFiniteAdele,
        rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          (((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      (m : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele b))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  set Fn : RationalFiniteAdele → (Fin n → RationalFiniteAdele) → ℂ := fun y x =>
    rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
      (((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
        (((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt y x :
            Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator x)) with hFn
  have hpull : ∀ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
        (((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y) =
        ∫ x : Fin n → RationalFiniteAdele, Fn y x
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
    intro y
    rw [hFn]
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    rfl
  have hnorm : ∀ (y : RationalFiniteAdele) (x : Fin n → RationalFiniteAdele),
      ‖Fn y x‖ =
        ‖rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y)‖ *
          ‖rationalFiniteAdeleVectorIntegralIndicator x‖ := by
    intro y x
    rw [hFn]
    simp only [norm_mul, Circle.norm_coe]
    ring
  have hmaj : Integrable (fun p : RationalFiniteAdele × (Fin n → RationalFiniteAdele) =>
      ‖rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * p.1)‖ *
        ‖rationalFiniteAdeleVectorIntegralIndicator p.2‖)
      (rationalFiniteAdeleAddHaarMeasure.prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :=
    (integrable_natScaleIndicator hm).norm.mul_prod
      ((integrable_vectorIntegralIndicator n).norm)
  have hint : Integrable (Function.uncurry Fn)
      (rationalFiniteAdeleAddHaarMeasure.prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
    refine hmaj.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      rw [hFn]
      refine Measurable.mul (measurable_natScaleIndicator.comp measurable_fst) ?_
      refine Measurable.mul ?_ ?_
      · exact (continuous_induced_dom.comp
          (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))).measurable.comp
          measurable_fst
      · exact ((L.continuous_quadraticPhaseAt_uncurry).measurable).mul
          ((measurable_vectorIntegralIndicator n).comp measurable_snd)
    · filter_upwards with p
      obtain ⟨y, x⟩ := p
      rw [Function.uncurry_apply_pair, hnorm y x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpull),
    integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hchar : ∀ y : RationalFiniteAdele,
      Fn y x = rationalFiniteAdeleVectorIntegralIndicator x *
        (rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          ((rationalFiniteAdeleFourierChar
            (y * (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
              algebraMap ℚ RationalFiniteAdele b)) : Circle) : ℂ)) := by
    intro y
    have harg : y * (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
        algebraMap ℚ RationalFiniteAdele b) =
        algebraMap ℚ RationalFiniteAdele (-b) * y +
          y * L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x := by
      rw [map_neg]
      ring
    have hphase : ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt y x :
        Circle) : ℂ) =
        ((rationalFiniteAdeleFourierChar
          (y * L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x) :
          Circle) : ℂ) := rfl
    rw [hFn]
    dsimp only
    rw [hphase, harg, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [hchar]
  rw [integral_const_mul,
    integral_natScaleIndicator_mul_char hm
      (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
        algebraMap ℚ RationalFiniteAdele b)]
  ring

/-! ## Exhausting the finite adeles -/

/-- Every finite adele has a natural denominator. -/
theorem exists_natScale_mem_integral (y : RationalFiniteAdele) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : RationalFiniteAdele) * y ∈ integralFiniteAdeleSubring := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring y
  refine ⟨q.den, q.den_nz, ?_⟩
  have hNmem : ((q.den : ℕ) : RationalFiniteAdele) ∈ integralFiniteAdeleSubring :=
    natCast_mem integralFiniteAdeleSubring q.den
  have h1 : ((q.den : ℕ) : RationalFiniteAdele) *
      (y - algebraMap ℚ RationalFiniteAdele q) ∈ integralFiniteAdeleSubring :=
    Subring.mul_mem _ hNmem hq
  have hnum : ((q.den : ℕ) : ℚ) * q = (q.num : ℚ) := by
    rw [mul_comm]
    exact_mod_cast Rat.mul_den_eq_num q
  have h2 : ((q.den : ℕ) : RationalFiniteAdele) *
      algebraMap ℚ RationalFiniteAdele q ∈ integralFiniteAdeleSubring := by
    have hcast : ((q.den : ℕ) : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele ((q.den : ℕ) : ℚ) := by norm_num
    rw [hcast, ← map_mul, hnum]
    exact (rational_mem_integralFiniteAdeleSubring_iff (q.num : ℚ)).mpr ⟨q.num, by simp⟩
  have hsum := Subring.add_mem _ h1 h2
  rw [show ((q.den : ℕ) : RationalFiniteAdele) *
      (y - algebraMap ℚ RationalFiniteAdele q) +
      ((q.den : ℕ) : RationalFiniteAdele) * algebraMap ℚ RationalFiniteAdele q =
      ((q.den : ℕ) : RationalFiniteAdele) * y from by ring] at hsum
  exact hsum

/-- The factorial truncations eventually contain any fixed finite adele. -/
theorem eventually_factorialScale_mem_integral (y : RationalFiniteAdele) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((Nat.factorial k : ℕ) : RationalFiniteAdele) * y ∈ integralFiniteAdeleSubring := by
  obtain ⟨N, hN, hNy⟩ := exists_natScale_mem_integral y
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hk
  have hcast : ((Nat.factorial k : ℕ) : RationalFiniteAdele) =
      ((c : ℕ) : RationalFiniteAdele) * ((N : ℕ) : RationalFiniteAdele) := by
    rw [hc]
    push_cast
    ring
  rw [hcast, mul_assoc]
  exact Subring.mul_mem _ (natCast_mem integralFiniteAdeleSubring c) hNy

theorem norm_rationalFiniteAdeleIntegralIndicator_le_one (z : RationalFiniteAdele) :
    ‖rationalFiniteAdeleIntegralIndicator z‖ ≤ 1 := by
  by_cases hz : z ∈ integralFiniteAdeleSubring
  · rw [rationalFiniteAdeleIntegralIndicator_of_mem hz]
    simp
  · rw [rationalFiniteAdeleIntegralIndicator_of_not_mem hz]
    simp

/-- The finite local integral is the limit of its level-`k!` congruence measures. -/
theorem tendsto_natScaleTruncated_finiteLocal (L : PositiveDefiniteIntegralLattice n) {scale : ℝ}
    (hscale : 0 < scale) (hrank : 5 ≤ n) (b : ℚ) :
    Filter.Tendsto (fun k : ℕ =>
        ((Nat.factorial k : ℕ) : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
          rationalFiniteAdeleVectorIntegralIndicator x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n)
      Filter.atTop
      (𝓝 (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure)) := by
  have hG := L.integrable_finiteGaussIntegral hscale hrank
  have hchar : Continuous (fun y : RationalFiniteAdele =>
      ((rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ)) :=
    continuous_induced_dom.comp
      (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))
  have hlim : Filter.Tendsto (fun k : ℕ => ∫ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator
          (((Nat.factorial k : ℕ) : RationalFiniteAdele) * y) *
        (((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
      ∂rationalFiniteAdeleAddHaarMeasure) Filter.atTop
      (𝓝 (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y‖)
      (fun k => (measurable_natScaleIndicator.aestronglyMeasurable).mul
        (hchar.aestronglyMeasurable.mul hG.aestronglyMeasurable))
      hG.norm ?_ ?_
    · intro k
      filter_upwards with y
      rw [norm_mul, norm_mul, Circle.norm_coe, one_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      exact norm_rationalFiniteAdeleIntegralIndicator_le_one _
    · filter_upwards with y
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_factorialScale_mem_integral y] with k hk
      rw [rationalFiniteAdeleIntegralIndicator_of_mem hk, one_mul]
  refine hlim.congr fun k => ?_
  exact (L.integral_natScaleTruncated_finiteLocal (Nat.factorial_ne_zero k) b)

end PositiveDefiniteIntegralLattice
