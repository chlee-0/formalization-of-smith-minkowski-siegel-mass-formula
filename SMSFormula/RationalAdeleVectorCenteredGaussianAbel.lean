import SMSFormula.RationalAdeleVectorShiftedGaussianFiniteTheta
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Centered Gaussian Abel limits

This file derives the centered positive-definite lattice Gaussian limit needed
for the periodic Gaussian Abel argument from the existing shifted matrix-theta
transformation.  The proof first sends the reciprocal-scale shifted theta to
its zero term by dominated convergence, and then rewrites that theta as the
exact determinant-normalized centered Gaussian.

The final theorem permits a finite weighted family of centers.  It is the
analytic endpoint required after a periodic lattice sum has been split into
its finitely many residue classes.  No complex matrix-theta transformation,
phase perturbation, finite Gauss reciprocity, or Weil index is used here.
-/

noncomputable section

open Filter Matrix Topology

namespace PositiveDefiniteIntegralLattice

/-- At large positive scale, a shifted positive-definite Gaussian with purely
imaginary linear term converges to its unique surviving zero-lattice term. -/
theorem tendsto_tsum_shiftedMatrixGaussianSummand_atTop
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (r : Fin n → ℝ) :
    Tendsto
      (fun a : ℝ => ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S (a : ℂ)
          (pureImaginaryLinear r) z)
      atTop (𝓝 1) := by
  classical
  let bound : (Fin n → ℤ) → ℝ := fun z =>
    ‖shiftedMatrixGaussianSummand S (1 : ℂ) 0 z‖
  have hbound : Summable bound := by
    exact (summable_shiftedMatrixGaussianSummand_zero S hS zero_lt_one).norm
  have hpoint : ∀ z : Fin n → ℤ,
      Tendsto
        (fun a : ℝ => shiftedMatrixGaussianSummand S (a : ℂ)
          (pureImaginaryLinear r) z)
        atTop (𝓝 (if z = 0 then 1 else 0)) := by
    intro z
    by_cases hz : z = 0
    · subst z
      convert
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1))
          using 1 <;>
        simp [shiftedMatrixGaussianSummand, pureImaginaryLinear,
          integerVectorReal, dotProduct, Matrix.mulVec]
    · have hq : 0 < integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z) :=
        hS.dotProduct_mulVec_pos (by
          intro hzreal
          apply hz
          funext i
          have hi := congrFun hzreal i
          simp only [Pi.zero_apply]
          exact Int.cast_eq_zero.mp hi)
      let q : ℝ := integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)
      have hid : Tendsto (fun a : ℝ => a) atTop atTop :=
        Filter.tendsto_atTop.2 fun b => Filter.eventually_ge_atTop b
      have hmul : Tendsto (fun a : ℝ => a * (Real.pi * q)) atTop atTop :=
        hid.atTop_mul_const (mul_pos Real.pi_pos hq)
      have hneg : Tendsto (fun a : ℝ => -(a * (Real.pi * q))) atTop atBot :=
        Filter.tendsto_neg_atBot_iff.mpr hmul
      rw [if_neg hz, tendsto_zero_iff_norm_tendsto_zero]
      have hexp := Real.tendsto_exp_atBot.comp hneg
      convert hexp using 1
      funext a
      rw [norm_shiftedMatrixGaussianSummand_pureImaginaryLinear]
      rw [shiftedMatrixGaussianSummand, Complex.norm_exp]
      simp [q, Complex.mul_re]
      ring
  have hdom : ∀ᶠ a : ℝ in atTop, ∀ z,
      ‖shiftedMatrixGaussianSummand S (a : ℂ)
        (pureImaginaryLinear r) z‖ ≤ bound z := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with a ha
    intro z
    dsimp only [bound]
    rw [norm_shiftedMatrixGaussianSummand_pureImaginaryLinear]
    rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand,
      Complex.norm_exp, Complex.norm_exp]
    simp [Complex.mul_re]
    have hq := hS.posSemidef.dotProduct_mulVec_nonneg (integerVectorReal z)
    have hq' : 0 ≤
        integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z) := by
      simpa using hq
    have hpq : 0 ≤ Real.pi *
        (integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)) :=
      mul_nonneg Real.pi_pos.le hq'
    calc
      Real.pi * (integerVectorReal z ⬝ᵥ
          S.mulVec (integerVectorReal z)) ≤
          a * (Real.pi * (integerVectorReal z ⬝ᵥ
            S.mulVec (integerVectorReal z))) :=
        by simpa using mul_le_mul_of_nonneg_right ha hpq
      _ = Real.pi * a * (integerVectorReal z ⬝ᵥ
          S.mulVec (integerVectorReal z)) := by ring
  have ht := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  simpa using ht

/-- The reciprocal-scale shifted theta is exactly the normalized centered
Gaussian theta. -/
theorem shifted_inv_theta_eq_normalization_mul_centered
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (r : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand S⁻¹ ((1 / a : ℝ) : ℂ)
          (pureImaginaryLinear r) z) =
      shiftedMatrixThetaNormalization S⁻¹ (1 / a) *
        ∑' z : Fin n → ℤ, centeredMatrixGaussianSummand S a r z := by
  letI : Invertible S := Matrix.invertibleOfIsUnitDet S
    (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  simpa using
    (tsum_shiftedMatrixGaussianSummand_pureImaginaryLinear_eq_centered_inv
      n S⁻¹ hS.inv (one_div_pos.mpr ha) r)

/-- The shifted-theta normalization at reciprocal scale is the positive real
square root of the centered Gaussian determinant factor. -/
theorem shiftedMatrixThetaNormalization_inv_one_div
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) :
    shiftedMatrixThetaNormalization S⁻¹ (1 / a) =
      (Real.sqrt (a ^ n * S.det) : ℂ) := by
  rw [shiftedMatrixThetaNormalization, Matrix.det_nonsing_inv]
  have harg : (1 / a) ^ n * Ring.inverse S.det =
      (a ^ n * S.det)⁻¹ := by
    simp [Ring.inverse_eq_inv, one_div, inv_pow]
    ring
  simp only [Fintype.card_fin]
  rw [harg, Real.sqrt_inv]
  push_cast
  have hsqrt : Real.sqrt (a ^ n * S.det) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos (pow_pos ha n) hS.det_pos)
  field_simp

/-- Reciprocal-scale theta transformation followed by large-scale decay gives
the determinant-normalized centered Gaussian limit. -/
theorem tendsto_normalization_mul_tsum_centered_nhdsGT_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (r : Fin n → ℝ) :
    Tendsto
      (fun a : ℝ => shiftedMatrixThetaNormalization S⁻¹ (1 / a) *
        ∑' z : Fin n → ℤ, centeredMatrixGaussianSummand S a r z)
      (𝓝[>] 0) (𝓝 1) := by
  have ht :=
    (tendsto_tsum_shiftedMatrixGaussianSummand_atTop S⁻¹ hS.inv r).comp
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] 0) atTop)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := ha
  simpa [one_div] using
    (shifted_inv_theta_eq_normalization_mul_centered S hS ha' r)

/-- A centered positive-definite lattice Gaussian has the exact Abel limit
after multiplication by the determinant square-root normalization. -/
theorem tendsto_sqrt_det_mul_tsum_centered_nhdsGT_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (r : Fin n → ℝ) :
    Tendsto
      (fun a : ℝ => (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ, centeredMatrixGaussianSummand S a r z)
      (𝓝[>] 0) (𝓝 1) := by
  apply (tendsto_normalization_mul_tsum_centered_nhdsGT_zero S hS r).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [shiftedMatrixThetaNormalization_inv_one_div S hS ha]

/-- The centered Gaussian Abel limit remains exact after multiplying the
small positive scale by a fixed positive constant. -/
theorem tendsto_sqrt_det_mul_tsum_centered_mul_nhdsGT_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (r : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun a : ℝ => (Real.sqrt ((a * c) ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ, centeredMatrixGaussianSummand S (a * c) r z)
      (𝓝[>] 0) (𝓝 1) := by
  have hbase : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0) := continuousAt_id
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
  have hnhds : Tendsto (fun a : ℝ => a * c) (𝓝[>] 0) (𝓝 0) :=
    by simpa using (hbase.mul_const c).mono_left hle
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, a * c ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact mul_pos ha hc
  have hscale : Tendsto (fun a : ℝ => a * c) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩
  exact (tendsto_sqrt_det_mul_tsum_centered_nhdsGT_zero S hS r).comp hscale

/-- A finite weighted family of centered lattice Gaussians has Abel limit the
sum of its weights.  This is the analytic form used after a periodic lattice
sum is split into finitely many residue classes. -/
theorem tendsto_fintype_sum_centeredGaussianAbel_nhdsGT_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {ι : Type*} [Fintype ι] (weight : ι → ℂ)
    (center : ι → Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun a : ℝ => ∑ j : ι, weight j *
        ((Real.sqrt ((a * c) ^ n * S.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            centeredMatrixGaussianSummand S (a * c) (center j) z))
      (𝓝[>] 0) (𝓝 (∑ j : ι, weight j)) := by
  apply tendsto_finset_sum
  intro j _hj
  simpa using
    (tendsto_sqrt_det_mul_tsum_centered_mul_nhdsGT_zero
      S hS (center j) hc).const_mul (weight j)

end PositiveDefiniteIntegralLattice
