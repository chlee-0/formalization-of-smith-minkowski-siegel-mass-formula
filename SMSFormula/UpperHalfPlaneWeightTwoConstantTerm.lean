import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A weight-two function invariant under `S` and `T` has zero constant term

Let `U = {z : ℂ | 0 < Im z}`.  Let `f` be continuous on `U` with a primitive `F` (`F' = f` on `U`),
and assume

* `f(z + 1) = f(z)` (invariance under `T`),
* `f(-1/z) = z² f(z)` (weight-two invariance under `S`),
* `f(z) → a₀` as `Im z → ∞`, uniformly in `Re z`.

Then `a₀ = 0`.

This replaces the usual contour-integral argument by an elementary period
argument.  The functions `F(-1/z) - F(z)` and `F(z + 1) - F(z)` have zero derivative on the convex
set `U`, so they are constants `κ` and `c`.  The Möbius maps `z ↦ -1/z` and `z ↦ -1/(z + 1)` have
orders two and three on `U` (the matrix relations `S² = (ST)³ = -1`), so `2κ = 0` and
`3(κ + c) = 0`, whence `c = 0`.  Finally `c = ∫₀¹ f(t + iy) dt → a₀`.

No contour integral, no generation of `SL₂(ℤ)` and no finite-level factorization is used: only the
two transformation laws.  Nothing is chosen.
-/

noncomputable section

open Complex Filter Topology intervalIntegral

namespace SMSFormula.WeightTwoConstantTerm

/-- The upper half-plane as a subset of `ℂ`. -/
def upperHalfSet : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperHalfSet : IsOpen upperHalfSet :=
  isOpen_lt continuous_const continuous_im

theorem isPreconnected_upperHalfSet : IsPreconnected upperHalfSet :=
  (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected

theorem ne_zero_of_mem {z : ℂ} (hz : z ∈ upperHalfSet) : z ≠ 0 := by
  rintro rfl
  simp [upperHalfSet] at hz

theorem neg_inv_mem {z : ℂ} (hz : z ∈ upperHalfSet) : -z⁻¹ ∈ upperHalfSet := by
  have hz0 := ne_zero_of_mem hz
  have hn : 0 < normSq z := normSq_pos.2 hz0
  change 0 < (-z⁻¹).im
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hz hn

theorem add_one_mem {z : ℂ} (hz : z ∈ upperHalfSet) : z + 1 ∈ upperHalfSet := by
  change 0 < (z + 1).im
  simpa using hz

theorem add_real_mem {z : ℂ} (hz : z ∈ upperHalfSet) (t : ℝ) : z + t ∈ upperHalfSet := by
  change 0 < (z + t).im
  simpa using hz

/-- A function with zero derivative on `U` is constant there. -/
theorem exists_const_of_hasDerivAt_zero {H : ℂ → ℂ}
    (hH : ∀ z ∈ upperHalfSet, HasDerivAt H 0 z) : ∃ κ, ∀ z ∈ upperHalfSet, H z = κ :=
  isOpen_upperHalfSet.exists_is_const_of_deriv_eq_zero isPreconnected_upperHalfSet
    (fun z hz ↦ (hH z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hH z hz).deriv)

variable {F f : ℂ → ℂ}

/-- The `S`-period: `F(-1/z) - F(z)` is constant on `U`. -/
theorem exists_period_S (hF : ∀ z ∈ upperHalfSet, HasDerivAt F (f z) z)
    (hS : ∀ z ∈ upperHalfSet, f (-z⁻¹) = z ^ 2 * f z) :
    ∃ κ, ∀ z ∈ upperHalfSet, F (-z⁻¹) = F z + κ := by
  obtain ⟨κ, hκ⟩ := exists_const_of_hasDerivAt_zero (H := fun z ↦ F (-z⁻¹) - F z) fun z hz ↦ by
    have hz0 := ne_zero_of_mem hz
    have hinv : HasDerivAt (fun w : ℂ ↦ -w⁻¹) ((z ^ 2)⁻¹) z := by
      simpa using (hasDerivAt_inv hz0).neg
    have hcomp := (hF _ (neg_inv_mem hz)).comp z hinv
    have h := hcomp.sub (hF z hz)
    convert h using 1
    rw [hS z hz]
    field_simp
    ring
  exact ⟨κ, fun z hz ↦ by rw [← hκ z hz]; ring⟩

/-- The `T`-period: `F(z + 1) - F(z)` is constant on `U`. -/
theorem exists_period_T (hF : ∀ z ∈ upperHalfSet, HasDerivAt F (f z) z)
    (hT : ∀ z ∈ upperHalfSet, f (z + 1) = f z) :
    ∃ c, ∀ z ∈ upperHalfSet, F (z + 1) = F z + c := by
  obtain ⟨c, hc⟩ := exists_const_of_hasDerivAt_zero (H := fun z ↦ F (z + 1) - F z) fun z hz ↦ by
    have hshift : HasDerivAt (fun w : ℂ ↦ w + 1) 1 z := (hasDerivAt_id z).add_const 1
    have hcomp := (hF _ (add_one_mem hz)).comp z hshift
    have h := hcomp.sub (hF z hz)
    convert h using 1
    rw [hT z hz]
    ring
  exact ⟨c, fun z hz ↦ by rw [← hc z hz]; ring⟩

/-- The periods vanish: from `S² = (ST)³ = -1` acting trivially on `U`. -/
theorem periods_eq_zero {κ c : ℂ} (hκ : ∀ z ∈ upperHalfSet, F (-z⁻¹) = F z + κ)
    (hc : ∀ z ∈ upperHalfSet, F (z + 1) = F z + c) : κ = 0 ∧ c = 0 := by
  have hI : I ∈ upperHalfSet := by simp [upperHalfSet]
  -- `S² = 1` on `U`
  have hSS : κ = 0 := by
    have h1 := hκ _ (neg_inv_mem hI)
    rw [hκ I hI, neg_inv, neg_neg, inv_inv] at h1
    have h2 : (2 : ℂ) * κ = 0 := by linear_combination -h1
    simpa using h2
  -- `(ST)³ = 1` on `U`, with `φ(w) = -1/(w + 1)`
  have hstep : ∀ w ∈ upperHalfSet, F (-(w + 1)⁻¹) = F w + (c + κ) := by
    intro w hw
    rw [hκ _ (add_one_mem hw), hc w hw]
    ring
  have hφ : ∀ w ∈ upperHalfSet, -(w + 1)⁻¹ ∈ upperHalfSet := fun w hw ↦
    neg_inv_mem (add_one_mem hw)
  set z₁ := -(I + 1)⁻¹ with hz₁
  set z₂ := -(z₁ + 1)⁻¹ with hz₂
  have hz₁m : z₁ ∈ upperHalfSet := hφ I hI
  have hz₂m : z₂ ∈ upperHalfSet := hφ z₁ hz₁m
  have hcycle : -(z₂ + 1)⁻¹ = I := by
    have hI1 : I + 1 ≠ 0 := ne_zero_of_mem (add_one_mem hI)
    have hz11 : z₁ + 1 ≠ 0 := ne_zero_of_mem (add_one_mem hz₁m)
    have hz21 : z₂ + 1 ≠ 0 := ne_zero_of_mem (add_one_mem hz₂m)
    have hI0 : I ≠ 0 := I_ne_zero
    have hz₁' : z₁ + 1 = I * (I + 1)⁻¹ := by
      rw [hz₁]; field_simp; ring
    have hz₂' : z₂ + 1 = -I⁻¹ := by
      rw [hz₂, hz₁']
      field_simp
      ring_nf
    rw [hz₂', neg_inv, neg_neg, inv_inv]
  have h3 : F I = F I + 3 * (c + κ) := by
    have e1 := hstep I hI
    have e2 := hstep z₁ hz₁m
    have e3 := hstep z₂ hz₂m
    rw [hcycle] at e3
    rw [← hz₁] at e1
    rw [← hz₂] at e2
    linear_combination e3 + e2 + e1
  refine ⟨hSS, ?_⟩
  have h4 : (3 : ℂ) * (c + κ) = 0 := by linear_combination -h3
  rw [hSS, add_zero] at h4
  simpa using h4

/-- The `T`-period is the horizontal integral of `f`. -/
theorem period_T_eq_integral (hF : ∀ z ∈ upperHalfSet, HasDerivAt F (f z) z)
    (hfc : ContinuousOn f upperHalfSet) {c : ℂ}
    (hc : ∀ z ∈ upperHalfSet, F (z + 1) = F z + c) {z : ℂ} (hz : z ∈ upperHalfSet) :
    c = ∫ t in (0 : ℝ)..1, f (z + t) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ F (z + s)) (f (z + t)) t := by
    intro t _
    have h1 : HasDerivAt (fun w : ℂ ↦ z + w) 1 (t : ℂ) := (hasDerivAt_id _).const_add z
    have h2 := (hF _ (add_real_mem hz t)).comp (t : ℂ) h1
    simpa using h2.comp_ofReal
  have hcont : Continuous fun t : ℝ ↦ z + t := continuous_const.add continuous_ofReal
  have hint : IntervalIntegrable (fun t : ℝ ↦ f (z + t)) MeasureTheory.volume 0 1 :=
    (hfc.comp_continuous hcont fun t ↦ add_real_mem hz t).intervalIntegrable 0 1
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, add_zero]
  rw [hc z hz]
  ring

/-- A weight-two function invariant under `S` and `T` has zero constant term. -/
theorem constTerm_eq_zero (hF : ∀ z ∈ upperHalfSet, HasDerivAt F (f z) z)
    (hfc : ContinuousOn f upperHalfSet)
    (hT : ∀ z ∈ upperHalfSet, f (z + 1) = f z)
    (hS : ∀ z ∈ upperHalfSet, f (-z⁻¹) = z ^ 2 * f z) {a₀ : ℂ}
    (hlim : ∀ ε > 0, ∃ Y : ℝ, ∀ z ∈ upperHalfSet, Y < z.im → ‖f z - a₀‖ ≤ ε) :
    a₀ = 0 := by
  obtain ⟨κ, hκ⟩ := exists_period_S hF hS
  obtain ⟨c, hc⟩ := exists_period_T hF hT
  obtain ⟨-, hc0⟩ := periods_eq_zero hκ hc
  -- `c = a₀`
  refine (norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_))
  obtain ⟨Y, hY⟩ := hlim ε hε
  set y : ℝ := max Y 0 + 1 with hy
  have hyY : Y < y := by rw [hy]; linarith [le_max_left Y 0]
  have hy0 : 0 < y := by rw [hy]; linarith [le_max_right Y 0]
  set z : ℂ := (y : ℂ) * I with hz
  have hzm : z ∈ upperHalfSet := by simp [upperHalfSet, hz, hy0]
  have hcint := period_T_eq_integral hF hfc hc hzm
  rw [hc0] at hcint
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖f (z + t) - a₀‖ ≤ ε := by
    intro t _
    refine hY _ (add_real_mem hzm t) ?_
    simp [hz, hyY]
  have hcont : Continuous fun t : ℝ ↦ z + t := continuous_const.add continuous_ofReal
  have hint : IntervalIntegrable (fun t : ℝ ↦ f (z + t)) MeasureTheory.volume 0 1 :=
    (hfc.comp_continuous hcont fun t ↦ add_real_mem hzm t).intervalIntegrable 0 1
  have heq : ∫ t in (0 : ℝ)..1, (f (z + t) - a₀) = -a₀ := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, ← hcint]
    simp
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [heq, norm_neg] at hnorm
  simpa using hnorm

end SMSFormula.WeightTwoConstantTerm
