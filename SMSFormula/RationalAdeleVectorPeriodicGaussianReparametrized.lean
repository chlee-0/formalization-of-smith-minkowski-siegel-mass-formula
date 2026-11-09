import SMSFormula.RationalAdeleVectorPeriodicGaussianOscillatory

/-!
# Periodic Gaussian Abel limits along a reparameterized scale

The boundary parameter arising from rational Gauss reciprocity has a positive
real part which is not the original regularization variable.  This file
records the exact filter-level form of the already proved oscillatory Abel
estimate: any positive scale tending to zero may be used, provided the
remaining imaginary error is little-oh relative to that scale.

The proof reuses the moment bound and proves all series summable before
comparison.
-/

noncomputable section

open Filter Matrix Topology

namespace PositiveDefiniteIntegralLattice

/-- The normalized oscillatory error tends to zero along any reparameterized
positive scale. -/
theorem tendsto_normalized_periodicQuadraticOscillation_error_along
    {κ : Type*} {l : Filter κ}
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ)
    (scale error : κ → ℝ)
    (hscale : Tendsto scale l (𝓝[>] 0))
    (herror : Tendsto (fun x ↦ error x / scale x) l (𝓝 0)) :
    Tendsto
      (fun x ↦ (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            (quadraticOscillation S (error x) z - 1) *
            centeredMatrixGaussianSummand S (scale x) 0 z)
      l (𝓝 0) := by
  let C : ℝ := ∑ r : Fin n → ZMod m, ‖weight r‖
  let B : κ → ℝ := fun x ↦ Real.sqrt ((scale x) ^ n * S.det) *
    ∑' z : Fin n → ℤ,
      ‖centeredMatrixGaussianSummand S (scale x / 2) 0 z‖
  let R : κ → ℝ := fun x ↦
    (C * 2 * Real.exp (-1)) * |error x / scale x| * B x
  have hscalePos : ∀ᶠ x in l, 0 < scale x :=
    hscale self_mem_nhdsWithin
  have herrorAbs :
      Tendsto (fun x ↦ |error x / scale x|) l (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_div, abs_zero] using herror.norm
  have hB : Tendsto B l (𝓝 (Real.sqrt ((2 : ℝ) ^ n))) := by
    exact
      (tendsto_sqrt_det_mul_tsum_norm_centered_halfScale_nhdsGT_zero
        S hS).comp hscale
  have hR : Tendsto R l (𝓝 0) := by
    have hprod := herrorAbs.mul hB
    have hscaled := hprod.const_mul (C * 2 * Real.exp (-1))
    simpa only [R, mul_assoc, zero_mul, mul_zero] using hscaled
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [hscalePos] with x hx
    let K : ℝ := C * (Real.pi * |error x|) *
      (2 * Real.exp (-1) / (Real.pi * scale x))
    let err : (Fin n → ℤ) → ℂ := fun z ↦
      weight (fun i ↦ (z i : ZMod m)) *
        (quadraticOscillation S (error x) z - 1) *
        centeredMatrixGaussianSummand S (scale x) 0 z
    let halfGaussian : (Fin n → ℤ) → ℝ := fun z ↦
      ‖centeredMatrixGaussianSummand S (scale x / 2) 0 z‖
    have herrNorm : Summable (fun z ↦ ‖err z‖) := by
      exact summable_norm_periodicQuadraticOscillation_error
        S hS hx (error x) weight
    have hhalf : Summable halfGaussian := by
      exact (summable_centeredMatrixGaussianSummand
        S hS (half_pos hx) 0).norm
    have hpoint : ∀ z, ‖err z‖ ≤ K * halfGaussian z := by
      intro z
      exact norm_periodicQuadraticOscillation_error_le_halfScale
        S hS hx (error x) weight z
    have hsum : ‖∑' z, err z‖ ≤ K * ∑' z, halfGaussian z := by
      calc
        ‖∑' z, err z‖ ≤ ∑' z, ‖err z‖ :=
          norm_tsum_le_tsum_norm herrNorm
        _ ≤ ∑' z, K * halfGaussian z :=
          herrNorm.tsum_le_tsum hpoint (hhalf.mul_left K)
        _ = K * ∑' z, halfGaussian z := tsum_mul_left
    change ‖(Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z, err z‖ ≤ R x
    rw [norm_mul]
    have hsqrtNorm :
        ‖(Real.sqrt ((scale x) ^ n * S.det) : ℂ)‖ =
          Real.sqrt ((scale x) ^ n * S.det) := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hsqrtNorm]
    calc
      Real.sqrt ((scale x) ^ n * S.det) * ‖∑' z, err z‖ ≤
          Real.sqrt ((scale x) ^ n * S.det) *
            (K * ∑' z, halfGaussian z) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
      _ = R x := by
        dsimp [R, B, K, C, halfGaussian]
        rw [abs_div, show |scale x| = scale x from abs_of_pos hx]
        field_simp [Real.pi_ne_zero, hx.ne']
  · exact hR

/-- Periodic Gaussian Abel limit with a small imaginary perturbation along an
arbitrary positive scale tending to zero. -/
theorem tendsto_periodicGaussianAbel_along
    {κ : Type*} {l : Filter κ}
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ)
    (scale error : κ → ℝ)
    (hscale : Tendsto scale l (𝓝[>] 0))
    (herror : Tendsto (fun x ↦ error x / scale x) l (𝓝 0)) :
    Tendsto
      (fun x ↦ (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            quadraticOscillation S (error x) z *
            centeredMatrixGaussianSummand S (scale x) 0 z)
      l (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
  have hpositive :=
    (tendsto_periodicGaussianAbel_nhdsGT_zero S hS weight).comp hscale
  have herr :=
    tendsto_normalized_periodicQuadraticOscillation_error_along
      S hS weight scale error hscale herror
  have hcombined := hpositive.add herr
  have hcombined' :
      Tendsto
        (fun x ↦
          (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
              ∑' z : Fin n → ℤ,
                weight (fun i ↦ (z i : ZMod m)) *
                  centeredMatrixGaussianSummand S (scale x) 0 z +
            (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
              ∑' z : Fin n → ℤ,
                weight (fun i ↦ (z i : ZMod m)) *
                  (quadraticOscillation S (error x) z - 1) *
                  centeredMatrixGaussianSummand S (scale x) 0 z)
        l (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
    simpa only [Function.comp_apply, add_zero] using hcombined
  have hscalePos : ∀ᶠ x in l, 0 < scale x :=
    hscale self_mem_nhdsWithin
  apply hcombined'.congr'
  filter_upwards [hscalePos] with x hx
  let base : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      centeredMatrixGaussianSummand S (scale x) 0 z
  let err : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      (quadraticOscillation S (error x) z - 1) *
      centeredMatrixGaussianSummand S (scale x) 0 z
  let perturbed : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      quadraticOscillation S (error x) z *
      centeredMatrixGaussianSummand S (scale x) 0 z
  have hbase : Summable base := by
    exact summable_periodicWeight_mul_centeredMatrixGaussianSummand
      S hS hx weight
  have herrNorm : Summable (fun z ↦ ‖err z‖) := by
    exact summable_norm_periodicQuadraticOscillation_error
      S hS hx (error x) weight
  have herrSummable : Summable err := herrNorm.of_norm
  change
    (Real.sqrt ((scale x) ^ n * S.det) : ℂ) * ∑' z, base z +
        (Real.sqrt ((scale x) ^ n * S.det) : ℂ) * ∑' z, err z =
      (Real.sqrt ((scale x) ^ n * S.det) : ℂ) * ∑' z, perturbed z
  calc
    (Real.sqrt ((scale x) ^ n * S.det) : ℂ) * ∑' z, base z +
          (Real.sqrt ((scale x) ^ n * S.det) : ℂ) * ∑' z, err z =
        (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
          ((∑' z, base z) + ∑' z, err z) := by ring
    _ = (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
          (∑' z : Fin n → ℤ, (base z + err z)) := by
      rw [(hbase.hasSum.add herrSummable.hasSum).tsum_eq]
    _ = (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
          (∑' z : Fin n → ℤ, perturbed z) := by
      congr 1
      apply tsum_congr
      intro z
      dsimp [base, err, perturbed]
      ring

/-- Complex-scale form of the reparameterized oscillatory Abel theorem. -/
theorem tendsto_periodicShiftedMatrixGaussian_along
    {κ : Type*} {l : Filter κ}
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ)
    (scale error : κ → ℝ)
    (hscale : Tendsto scale l (𝓝[>] 0))
    (herror : Tendsto (fun x ↦ error x / scale x) l (𝓝 0)) :
    Tendsto
      (fun x ↦ (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            shiftedMatrixGaussianSummand S
              ((scale x : ℂ) + (error x : ℂ) * Complex.I) 0 z)
      l (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
  have h := tendsto_periodicGaussianAbel_along
    S hS weight scale error hscale herror
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro x
  change
    (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            quadraticOscillation S (error x) z *
            centeredMatrixGaussianSummand S (scale x) 0 z =
      (Real.sqrt ((scale x) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            shiftedMatrixGaussianSummand S
              ((scale x : ℂ) + (error x : ℂ) * Complex.I) 0 z
  congr 1
  apply tsum_congr
  intro z
  calc
    weight (fun i ↦ (z i : ZMod m)) * quadraticOscillation S (error x) z *
        centeredMatrixGaussianSummand S (scale x) 0 z =
      weight (fun i ↦ (z i : ZMod m)) *
        (quadraticOscillation S (error x) z *
          centeredMatrixGaussianSummand S (scale x) 0 z) := by ring
    _ = _ := by rw [quadraticOscillation_mul_centeredGaussian_eq_shifted]

end PositiveDefiniteIntegralLattice
