import SMSFormula.UpperHalfPlaneWeightTwoConstantTerm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Bounded cluster points remove the weight-two anomaly

Let `V` be a finite-dimensional complex normed space, `U` an operator on `V`, and `K` a subspace on
which `U` has no nonzero fixed vector.  (In the application `K = Inv^⊥ ∩ ker(T₀ - 1)` and `U = ρ(S)`.)
Suppose a regularized family splits as `E_s(z) = H_s(z) + y^{-1-s} W_s` for `s > 0`, and:

* `W_s ∈ K` and `‖W_s‖ ≤ C` for `0 < s ≤ 1`;
* `H_s(z) → E₀(z)` as `s → 0⁺`, with `E₀` holomorphic on the upper half-plane;
* the exact weight-two S-law `E_s(-1/z) = z² U E_s(z)` holds for every `s > 0`.

Then `W_s → 0` and `E₀(-1/z) = z² U E₀(z)` (`tendsto_zero_and_sLaw_of_boundedCluster`).

Proof.  Along `comap W (𝓝 w) ⊓ 𝓝[>] 0` for a cluster point `w`, the S-law passes to the limit:
`E₀(-1/z) - z² U E₀(z) = z²(Uw - w)/y + 2izw`.  The left side and `2izw` are holomorphic, so
`z ↦ (Uw - w)/Im z` is holomorphic, which forces `Uw = w` (`eq_zero_of_differentiableOn_inv_im_smul`:
compare the real- and imaginary-direction derivatives at `i`).  Since `K` is closed, `w ∈ K`, so
`w = 0`.  A bounded family in a finite-dimensional space whose only cluster point is `0` tends to `0`.
No limit of the anomaly coefficient is computed.  Nothing is chosen.
-/

noncomputable section

open Filter Topology Complex Set Metric SMSFormula.WeightTwoConstantTerm

namespace SMSFormula.BoundedClusterAnomaly

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ## (7a) A constant vector over `Im z` is holomorphic only if it is zero -/

theorem eq_zero_of_differentiableOn_inv_im_smul {f : ℂ → V}
    (hf : DifferentiableOn ℂ f upperHalfSet) {v : V}
    (hv : ∀ z ∈ upperHalfSet, f z = (((z.im)⁻¹ : ℝ) : ℂ) • v) : v = 0 := by
  have hI : I ∈ upperHalfSet := by simp [upperHalfSet]
  have hd : HasDerivAt f (deriv f I) I :=
    (hf.differentiableAt (isOpen_upperHalfSet.mem_nhds hI)).hasDerivAt
  -- the real direction: `t ↦ f(i + t)` is constant
  have hd0 : HasDerivAt f (deriv f I) (I + (0 : ℂ)) := by rw [add_zero]; exact hd
  have h1 : HasDerivAt (fun t : ℝ ↦ f (I + t)) (deriv f I) 0 := by
    have h := HasDerivAt.scomp (0 : ℂ) hd0 ((hasDerivAt_id (0 : ℂ)).const_add I)
    have h' : HasDerivAt (fun w : ℂ ↦ f (I + w)) (deriv f I) ((0 : ℝ) : ℂ) := by
      simpa [Function.comp_def] using h
    have h'' := HasDerivAt.scomp (0 : ℝ) h' ((hasDerivAt_id (0 : ℝ)).ofReal_comp)
    simpa [Function.comp_def] using h''
  have h1c : (fun t : ℝ ↦ f (I + t)) = fun _ ↦ v := by
    funext t
    rw [hv _ (add_real_mem hI t)]
    simp
  have hf0 : deriv f I = 0 := by
    rw [h1c] at h1
    exact h1.unique (hasDerivAt_const _ _)
  -- the imaginary direction: `t ↦ f(i + i t) = (1 + t)⁻¹ v` near `0`
  have h2 : HasDerivAt (fun t : ℝ ↦ f (I + I * t)) (I • deriv f I) 0 := by
    have hlin : HasDerivAt (fun w : ℂ ↦ I + I * w) I 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul I).const_add I
    have hdI : HasDerivAt f (deriv f I) (I + I * 0) := by rw [mul_zero, add_zero]; exact hd
    have h := HasDerivAt.scomp (0 : ℂ) hdI hlin
    have h' : HasDerivAt (fun w : ℂ ↦ f (I + I * w)) (I • deriv f I) ((0 : ℝ) : ℂ) := by
      simpa [Function.comp_def] using h
    have h'' := HasDerivAt.scomp (0 : ℝ) h' ((hasDerivAt_id (0 : ℝ)).ofReal_comp)
    simpa [Function.comp_def] using h''
  have hev : (fun t : ℝ ↦ f (I + I * t)) =ᶠ[𝓝 0] fun t ↦ (((1 + t)⁻¹ : ℝ) : ℂ) • v := by
    have hmem : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
    filter_upwards [hmem] with t ht
    have htm : I + I * t ∈ upperHalfSet := by
      change 0 < (I + I * (t : ℂ)).im
      simp only [add_im, I_im, mul_im, I_re, ofReal_re, ofReal_im, zero_mul, one_mul]
      simp only [mem_Ioi] at ht
      linarith
    rw [hv _ htm]
    congr 3
    simp only [add_im, I_im, mul_im, I_re, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
  have h3 : HasDerivAt (fun t : ℝ ↦ (((1 + t)⁻¹ : ℝ) : ℂ) • v) ((((-1 : ℝ)) : ℂ) • v) 0 := by
    have hr : HasDerivAt (fun t : ℝ ↦ (1 + t)⁻¹) (-1 : ℝ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
      simpa using this
    exact hr.ofReal_comp.smul_const v
  have h4 := (h3.congr_of_eventuallyEq hev).unique h2
  rw [hf0, smul_zero] at h4
  have : (((-1 : ℝ)) : ℂ) • v = -v := by simp
  rw [this] at h4
  exact neg_eq_zero.1 h4

/-! ## The scalar identity behind (7.2) -/

theorem normSq_div_add_two_I_div (z : ℂ) (hz : z ∈ upperHalfSet) :
    ((normSq z : ℝ) : ℂ) / (z ^ 2 * (z.im : ℂ)) + 2 * I / z = ((z.im)⁻¹ : ℝ) := by
  have hz0 : z ≠ 0 := ne_zero_of_mem hz
  have hy : (z.im : ℂ) ≠ 0 := by
    have : 0 < z.im := hz
    exact_mod_cast this.ne'
  push_cast
  field_simp
  apply Complex.ext <;> simp [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem neg_inv_im (z : ℂ) : (-z⁻¹).im = z.im / normSq z := by
  rw [neg_im, inv_im, neg_div, neg_neg]

/-! ## (7) The bounded cluster lemma -/

theorem tendsto_rpow_neg_one_sub (a : ℝ) (ha : 0 < a) :
    Tendsto (fun s : ℝ ↦ (((a ^ (-1 - s) : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 ((a⁻¹ : ℝ) : ℂ)) := by
  have hc : ContinuousAt (fun s : ℝ ↦ a ^ (-1 - s)) 0 :=
    (Real.continuousAt_const_rpow ha.ne').comp (continuous_const.sub continuous_id).continuousAt
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  simpa [Function.comp_def, Real.rpow_neg_one] using h

/-- The S-law passes to the limit along any nontrivial filter `ℱ ≤ 𝓝[>] 0` on which `W → w`. -/
theorem limit_sLaw (U : V →L[ℂ] V) (W : ℝ → V) (H : ℝ → ℂ → V) (E₀ : ℂ → V)
    (hH : ∀ z ∈ upperHalfSet, Tendsto (fun s ↦ H s z) (𝓝[>] 0) (𝓝 (E₀ z)))
    (hS : ∀ s, 0 < s → ∀ z ∈ upperHalfSet,
      H s (-z⁻¹) + ((((-z⁻¹).im ^ (-1 - s) : ℝ)) : ℂ) • W s =
        z ^ 2 • U (H s z + ((((z.im) ^ (-1 - s) : ℝ)) : ℂ) • W s))
    {ℱ : Filter ℝ} [NeBot ℱ] (hℱ : ℱ ≤ 𝓝[>] 0) {w : V} (hW : Tendsto W ℱ (𝓝 w))
    {z : ℂ} (hz : z ∈ upperHalfSet) :
    E₀ (-z⁻¹) + ((((-z⁻¹).im)⁻¹ : ℝ) : ℂ) • w = z ^ 2 • U (E₀ z + (((z.im)⁻¹ : ℝ) : ℂ) • w) := by
  have hz' : 0 < z.im := hz
  have hzi : 0 < (-z⁻¹).im := neg_inv_mem hz
  have hL := ((hH _ (neg_inv_mem hz)).mono_left hℱ).add
    (((tendsto_rpow_neg_one_sub _ hzi).mono_left hℱ).smul hW)
  have hin := ((hH z hz).mono_left hℱ).add (((tendsto_rpow_neg_one_sub _ hz').mono_left hℱ).smul hW)
  have hR := ((U.continuous.tendsto _).comp hin).const_smul (z ^ 2)
  have hpos : ∀ᶠ s in ℱ, 0 < s := (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0) |> hℱ
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [hpos] with s hs
  exact (hS s hs z hz).symm

variable [FiniteDimensional ℂ V]

/-- The bounded cluster lemma. -/
theorem tendsto_zero_and_sLaw_of_boundedCluster (U : V →L[ℂ] V) (K : Submodule ℂ V)
    (hK : ∀ w ∈ K, U w = w → w = 0) (W : ℝ → V) (hWK : ∀ s, 0 < s → W s ∈ K) (C : ℝ)
    (hWb : ∀ s, 0 < s → s ≤ 1 → ‖W s‖ ≤ C) (H : ℝ → ℂ → V) (E₀ : ℂ → V)
    (hE₀ : DifferentiableOn ℂ E₀ upperHalfSet)
    (hH : ∀ z ∈ upperHalfSet, Tendsto (fun s ↦ H s z) (𝓝[>] 0) (𝓝 (E₀ z)))
    (hS : ∀ s, 0 < s → ∀ z ∈ upperHalfSet,
      H s (-z⁻¹) + ((((-z⁻¹).im ^ (-1 - s) : ℝ)) : ℂ) • W s =
        z ^ 2 • U (H s z + ((((z.im) ^ (-1 - s) : ℝ)) : ℂ) • W s)) :
    Tendsto W (𝓝[>] 0) (𝓝 0) ∧ ∀ z ∈ upperHalfSet, E₀ (-z⁻¹) = z ^ 2 • U (E₀ z) := by
  have hKc : IsClosed (K : Set V) := Submodule.closed_of_finiteDimensional K
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  -- every cluster point vanishes
  have hcl : ∀ w, MapClusterPt w (𝓝[>] 0) W → w = 0 := by
    intro w hw
    haveI : NeBot (comap W (𝓝 w) ⊓ 𝓝[>] 0) :=
      neBot_inf_comap_iff_map'.2 (mapClusterPt_def.1 hw).neBot
    have hWℱ : Tendsto W (comap W (𝓝 w) ⊓ 𝓝[>] 0) (𝓝 w) := tendsto_comap.mono_left inf_le_left
    have hℱl : comap W (𝓝 w) ⊓ 𝓝[>] (0 : ℝ) ≤ 𝓝[>] 0 := inf_le_right
    have hwK : w ∈ K :=
      hKc.mem_of_tendsto hWℱ ((hpos.filter_mono hℱl).mono fun s hs ↦ hWK s hs)
    -- `f(z) = z⁻² E₀(-1/z) - U E₀(z) - (2i/z) w` is holomorphic and equals `(Uw - w)/Im z`
    set f : ℂ → V := fun z ↦ (z ^ 2)⁻¹ • E₀ (-z⁻¹) - U (E₀ z) - (2 * I / z) • w with hfdef
    have hfd : DifferentiableOn ℂ f upperHalfSet := by
      have hneg : DifferentiableOn ℂ (fun z : ℂ ↦ -z⁻¹) upperHalfSet := fun z hz ↦
        ((differentiableAt_inv (ne_zero_of_mem hz)).neg).differentiableWithinAt
      have h1 : DifferentiableOn ℂ (fun z : ℂ ↦ (z ^ 2)⁻¹) upperHalfSet := fun z hz ↦
        ((hasDerivAt_pow 2 z).differentiableAt.inv
          (pow_ne_zero 2 (ne_zero_of_mem hz))).differentiableWithinAt
      have h2 : DifferentiableOn ℂ (fun z ↦ E₀ (-z⁻¹)) upperHalfSet :=
        hE₀.comp hneg fun z hz ↦ neg_inv_mem hz
      have h3 : DifferentiableOn ℂ (fun z ↦ U (E₀ z)) upperHalfSet :=
        U.differentiable.comp_differentiableOn hE₀
      have h4 : DifferentiableOn ℂ (fun z : ℂ ↦ 2 * I / z) upperHalfSet := fun z hz ↦
        ((differentiableAt_const _).div differentiableAt_id (ne_zero_of_mem hz)).differentiableWithinAt
      exact ((h1.smul h2).sub h3).sub (h4.smul_const w)
    have hfv : ∀ z ∈ upperHalfSet, f z = (((z.im)⁻¹ : ℝ) : ℂ) • (U w - w) := by
      intro z hz
      have hz0 : z ≠ 0 := ne_zero_of_mem hz
      have hy : (z.im : ℂ) ≠ 0 := by
        have : 0 < z.im := hz
        exact_mod_cast this.ne'
      have hN : (normSq z : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos.2 hz0).ne'
      have hlim := limit_sLaw U W H E₀ hH hS hℱl hWℱ hz
      set y' : ℂ := (((z.im)⁻¹ : ℝ) : ℂ) with hy'
      set c : ℂ := ((((-z⁻¹).im)⁻¹ : ℝ) : ℂ) with hc
      have hE : E₀ (-z⁻¹) = z ^ 2 • U (E₀ z) + (z ^ 2 * y') • U w - c • w := by
        rw [eq_sub_iff_add_eq, hlim, map_add, map_smul, smul_add, smul_smul]
      have hz2 : (z ^ 2) ≠ 0 := pow_ne_zero 2 hz0
      have hsc1 : (z ^ 2)⁻¹ * (z ^ 2 * y') = y' := by
        rw [← mul_assoc, inv_mul_cancel₀ hz2, one_mul]
      have hsc2 : (z ^ 2)⁻¹ * c + 2 * I / z = y' := by
        have key := normSq_div_add_two_I_div z hz
        have hcN : c = ((normSq z : ℝ) : ℂ) / (z.im : ℂ) := by
          rw [hc, neg_inv_im]
          push_cast
          field_simp
        rw [hcN, hy', ← key]
        ring
      calc f z = (z ^ 2)⁻¹ • (z ^ 2 • U (E₀ z) + (z ^ 2 * y') • U w - c • w) - U (E₀ z) -
            (2 * I / z) • w := by rw [hfdef]; simp only [hE]
        _ = y' • U w - ((z ^ 2)⁻¹ * c + 2 * I / z) • w := by
            rw [smul_sub, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ hz2, one_smul,
              hsc1, add_smul]
            abel
        _ = y' • (U w - w) := by rw [hsc2, smul_sub]
    have hv := eq_zero_of_differentiableOn_inv_im_smul hfd hfv
    exact hK w hwK (sub_eq_zero.1 hv)
  -- boundedness and the unique cluster point
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hW0 : Tendsto W (𝓝[>] 0) (𝓝 0) := by
    refine (isCompact_closedBall (0 : V) C).tendsto_nhds_of_unique_mapClusterPt ?_
      fun w _ hw ↦ hcl w hw
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with s hs using
      mem_closedBall_zero_iff.2 (hWb s hs.1 hs.2)
  refine ⟨hW0, fun z hz ↦ ?_⟩
  have h := limit_sLaw U W H E₀ hH hS le_rfl hW0 hz
  simpa using h

end SMSFormula.BoundedClusterAnomaly
