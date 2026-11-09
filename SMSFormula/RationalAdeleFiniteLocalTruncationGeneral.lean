import SMSFormula.RationalAdeleFiniteLocalTruncation
import SMSFormula.AdelicValueDensityLocalProduct

/-!
# The finite value density of an arbitrary test is a limit of congruence tube masses

The truncation argument for the standard integral indicator uses only two properties of the
test: it is integrable (Fubini against the compact truncation indicator), and its finite
Bruhat coefficient is integrable (dominated convergence).  For every such finite test `Φ`, the
finite local value density at a rational value `b` is therefore

```text
d_fin(Φ)(b) = lim_k k! · ∫ Φ(x) · 1_Zhat((Q(x) - b) / k!) dx,
```

the limit of the normalized masses of the congruence tubes `{Q(x) ∈ b + k! Zhat}` weighted by
`Φ`.  This is the analytic entry point of the finite-place replacement lemma: the same
limit for `1_{U_f}` and `1_Zhat` compares the two densities through congruence counts, with no
Euler product for the general test and no splitting of the adelic Haar measure.
No section, cutoff or Haar normalization is chosen.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance rationalFiniteAdeleCoordinateAddHaarMeasure_sigmaFinite'' (d : ℕ) :
    SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure d) := by
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleCoordinateAddHaarMeasure
  infer_instance

theorem continuous_quadraticPhaseAt_uncurry' (V : RationalQuadraticSpaceMatrix n) :
    Continuous (fun p : RationalFiniteAdele × (Fin n → RationalFiniteAdele) =>
      ((V.rationalFiniteAdeleQuadraticPhaseAt p.1 p.2 : Circle) : ℂ)) := by
  refine continuous_induced_dom.comp ?_
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt
    RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
  refine continuous_rationalFiniteAdeleFourierChar.comp ?_
  fun_prop

/-- The truncated finite value density of an integrable test is a congruence tube mass. -/
theorem integral_natScaleTruncated_finiteLocalBruhatCoefficient
    (V : RationalQuadraticSpaceMatrix n) {Φ : (Fin n → RationalFiniteAdele) → ℂ}
    (hΦ : Integrable Φ (rationalFiniteAdeleCoordinateAddHaarMeasure n)) {m : ℕ} (hm : m ≠ 0)
    (b : ℚ) :
    (∫ y : RationalFiniteAdele,
        rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          (((rationalFiniteAdeleFourierChar
              (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
            V.finiteLocalBruhatCoefficient Φ y)
        ∂rationalFiniteAdeleAddHaarMeasure) =
      (m : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
        Φ x * rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  set Fn : RationalFiniteAdele → (Fin n → RationalFiniteAdele) → ℂ := fun y x =>
    rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
      (((rationalFiniteAdeleFourierChar
          (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
        (((V.rationalFiniteAdeleQuadraticPhaseAt y x : Circle) : ℂ) * Φ x)) with hFn
  have hpull : ∀ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
        (((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          V.finiteLocalBruhatCoefficient Φ y) =
        ∫ x : Fin n → RationalFiniteAdele, Fn y x
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
    intro y
    rw [hFn]
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    rfl
  have hnorm : ∀ (y : RationalFiniteAdele) (x : Fin n → RationalFiniteAdele),
      ‖Fn y x‖ =
        ‖rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y)‖ * ‖Φ x‖ := by
    intro y x
    rw [hFn]
    simp only [norm_mul, Circle.norm_coe]
    ring
  have hmaj : Integrable (fun p : RationalFiniteAdele × (Fin n → RationalFiniteAdele) =>
      ‖rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * p.1)‖ * ‖Φ p.2‖)
      (rationalFiniteAdeleAddHaarMeasure.prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :=
    (integrable_natScaleIndicator hm).norm.mul_prod hΦ.norm
  have hint : Integrable (Function.uncurry Fn)
      (rationalFiniteAdeleAddHaarMeasure.prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
    refine hmaj.mono' ?_ ?_
    · rw [hFn]
      refine ((measurable_natScaleIndicator.comp measurable_fst).aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((continuous_induced_dom.comp
          (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))).measurable.comp
          measurable_fst).aestronglyMeasurable
      · exact (V.continuous_quadraticPhaseAt_uncurry').aestronglyMeasurable.mul
          (hΦ.aestronglyMeasurable.comp_snd)
    · filter_upwards with p
      obtain ⟨y, x⟩ := p
      rw [Function.uncurry_apply_pair, hnorm y x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpull),
    integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hchar : ∀ y : RationalFiniteAdele,
      Fn y x = Φ x *
        (rationalFiniteAdeleIntegralIndicator ((m : RationalFiniteAdele) * y) *
          ((rationalFiniteAdeleFourierChar
            (y * (V.finiteAdelicQuadraticFormValue x -
              algebraMap ℚ RationalFiniteAdele b)) : Circle) : ℂ)) := by
    intro y
    have harg : y * (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b) =
        algebraMap ℚ RationalFiniteAdele (-b) * y + y * V.finiteAdelicQuadraticFormValue x := by
      rw [map_neg]
      ring
    have hphase : ((V.rationalFiniteAdeleQuadraticPhaseAt y x : Circle) : ℂ) =
        ((rationalFiniteAdeleFourierChar (y * V.finiteAdelicQuadraticFormValue x) :
          Circle) : ℂ) := rfl
    rw [hFn]
    dsimp only
    rw [hphase, harg, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [hchar]
  rw [integral_const_mul,
    integral_natScaleIndicator_mul_char hm
      (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b)]
  ring

/-- The finite value density of an integrable test with integrable Bruhat coefficient is the
limit of its level-`k!` congruence tube masses:
`d_fin(Φ)(b) = lim_k k! · ∫ Φ(x) 1_Zhat((Q(x) - b)/k!) dx`. -/
theorem tendsto_natScaleTruncated_finiteLocalValueDensity
    (V : RationalQuadraticSpaceMatrix n) {Φ : (Fin n → RationalFiniteAdele) → ℂ}
    (hΦ : Integrable Φ (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (hB : Integrable (V.finiteLocalBruhatCoefficient Φ) rationalFiniteAdeleAddHaarMeasure)
    (b : ℚ) :
    Tendsto (fun k : ℕ =>
        ((Nat.factorial k : ℕ) : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
          Φ x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n)
      atTop (𝓝 (V.finiteLocalValueDensity Φ (algebraMap ℚ RationalFiniteAdele b))) := by
  have hchar : Continuous (fun y : RationalFiniteAdele =>
      ((rationalFiniteAdeleFourierChar
        (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ)) :=
    continuous_induced_dom.comp
      (continuous_rationalFiniteAdeleFourierChar.comp (by fun_prop))
  have hdens : V.finiteLocalValueDensity Φ (algebraMap ℚ RationalFiniteAdele b) =
      ∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          V.finiteLocalBruhatCoefficient Φ y ∂rationalFiniteAdeleAddHaarMeasure := by
    rw [finiteLocalValueDensity]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ((rationalFiniteAdeleFourierChar (-(y * algebraMap ℚ RationalFiniteAdele b)) :
        Circle) : ℂ) * _ = _
    rw [show -(y * algebraMap ℚ RationalFiniteAdele b) =
      algebraMap ℚ RationalFiniteAdele (-b) * y by rw [map_neg]; ring]
  rw [hdens]
  have hlim : Tendsto (fun k : ℕ => ∫ y : RationalFiniteAdele,
      rationalFiniteAdeleIntegralIndicator
          (((Nat.factorial k : ℕ) : RationalFiniteAdele) * y) *
        (((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          V.finiteLocalBruhatCoefficient Φ y)
      ∂rationalFiniteAdeleAddHaarMeasure) atTop
      (𝓝 (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-b) * y) : Circle) : ℂ) *
          V.finiteLocalBruhatCoefficient Φ y ∂rationalFiniteAdeleAddHaarMeasure)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖V.finiteLocalBruhatCoefficient Φ y‖)
      (fun k => (measurable_natScaleIndicator.aestronglyMeasurable).mul
        (hchar.aestronglyMeasurable.mul hB.aestronglyMeasurable))
      hB.norm ?_ ?_
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
  exact V.integral_natScaleTruncated_finiteLocalBruhatCoefficient hΦ (Nat.factorial_ne_zero k) b

/-- Tube ratio ⇒ density ratio: if the level-`k!` congruence tube masses of two admissible tests
are eventually in the constant ratio `c`, then so are their finite value densities at `b`.
This reduces the finite-place replacement lemma to a congruence-counting statement. -/
theorem finiteLocalValueDensity_eq_mul_of_eventually_tube_eq
    (V : RationalQuadraticSpaceMatrix n) {Φ Ψ : (Fin n → RationalFiniteAdele) → ℂ}
    (hΦ : Integrable Φ (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (hBΦ : Integrable (V.finiteLocalBruhatCoefficient Φ) rationalFiniteAdeleAddHaarMeasure)
    (hΨ : Integrable Ψ (rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (hBΨ : Integrable (V.finiteLocalBruhatCoefficient Ψ) rationalFiniteAdeleAddHaarMeasure)
    (b : ℚ) (c : ℂ)
    (h : ∀ᶠ k : ℕ in atTop,
      (∫ x : Fin n → RationalFiniteAdele,
          Φ x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
        c * ∫ x : Fin n → RationalFiniteAdele,
          Ψ x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (V.finiteAdelicQuadraticFormValue x - algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) :
    V.finiteLocalValueDensity Φ (algebraMap ℚ RationalFiniteAdele b) =
      c * V.finiteLocalValueDensity Ψ (algebraMap ℚ RationalFiniteAdele b) := by
  refine tendsto_nhds_unique (V.tendsto_natScaleTruncated_finiteLocalValueDensity hΦ hBΦ b) ?_
  refine ((V.tendsto_natScaleTruncated_finiteLocalValueDensity hΨ hBΨ b).const_mul c).congr'
    ?_
  filter_upwards [h] with k hk
  rw [hk]
  ring

end RationalQuadraticSpaceMatrix
