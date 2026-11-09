import SMSFormula.RationalLatticeGaussColumnEuclid
import SMSFormula.BoundedClusterAnomalyVanishing
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The regularized vector Eisenstein series and its exact S, T laws

For real `s > 0` and `z` in the upper half-plane, put

`E_s(z) = ½ Σ_{(c,d) primitive} (Im z / |cz+d|²)^s (cz+d)⁻² F(c,d)`   (`regEisenstein`),

a sum over all primitive signed pairs of the Gauss columns.  The pairs `(0, ±1)` contribute
`(Im z)^s e₀`, so this is the answer's `y^s e₀ + Σ_{c ≥ 1} Σ_{(c,d)=1} y^s F(c,d) / ((cz+d)²|cz+d|^{2s})`
(the terms at `(c,d)` and `(-c,-d)` agree by `gaussColumn_neg_neg`).  The regularizer is `(Im γz)^s`.

* Absolute convergence (`summable_regEisSummand`): the summand has norm at most
  `(Im z)^s ‖cz+d‖^{-(2+2s)}`, because every coprime column has sup norm at most one (Euclid,
  `norm_gaussColumn_le`).  Mathlib's lattice-point bound `EisensteinSeries.summand_bound` and
  `summable_one_div_norm_rpow` (exponent `2 + 2s > 2`) finish.
* The exact laws: `E_s(z + 1) = T₀ E_s(z)` (`regEisenstein_add_one`) and
  `E_s(-1/z) = z² U E_s(z)` (`regEisenstein_neg_inv`).  Termwise, `Im γz` is transported exactly and
  the columns obey `F(c, d) = T₀ F(c, c + d)` and `F(c, d) = U F(d, -c)` (the transport laws).  The
  reindexings `(c,d) ↦ (c, c+d)` and `(c,d) ↦ (d, -c)` are bijections of `ℤ²`, and all sums are
  absolute.

No matrix with a given bottom row is chosen and no word independence is used.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm

namespace PositiveDefiniteIntegralLattice

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## `T₀` as a continuous linear operator -/

/-- `T₀` as a linear map. -/
def gaussTLinear : (L.PolarDiscriminantGroup → ℂ) →ₗ[ℂ] (L.PolarDiscriminantGroup → ℂ) where
  toFun := L.gaussT
  map_add' := L.gaussT_add
  map_smul' := L.gaussT_smul

/-- `T₀` as a continuous linear operator. -/
def gaussTCLM : (L.PolarDiscriminantGroup → ℂ) →L[ℂ] (L.PolarDiscriminantGroup → ℂ) :=
  LinearMap.toContinuousLinearMap L.gaussTLinear

@[simp]
theorem gaussTCLM_apply (v : L.PolarDiscriminantGroup → ℂ) : L.gaussTCLM v = L.gaussT v :=
  rfl

/-! ## The summand -/

/-- The regularizer `(Im z / |cz+d|²)^s = (Im γz)^s`. -/
def eisRegularizer (s : ℝ) (z : ℂ) (p : Fin 2 → ℤ) : ℝ :=
  (z.im / normSq ((p 0 : ℂ) * z + p 1)) ^ s

open Classical in
/-- The regularized summand `(Im γz)^s (cz+d)⁻² F(c,d)` on primitive pairs, `0` otherwise. -/
def regEisSummand (s : ℝ) (z : ℂ) (p : Fin 2 → ℤ) : L.PolarDiscriminantGroup → ℂ :=
  if IsCoprime (p 0) (p 1) then
    (((eisRegularizer s z p : ℝ) : ℂ) * (((p 0 : ℂ) * z + p 1) ^ 2)⁻¹) •
      L.gaussColumn (p 0) (p 1)
  else 0

/-- The regularized vector Eisenstein series `E_s(z) = ½ Σ_{(c,d) primitive} (Im γz)^s (cz+d)⁻² F(c,d)`. -/
def regEisenstein (s : ℝ) (z : ℂ) : L.PolarDiscriminantGroup → ℂ :=
  (1 / 2 : ℂ) • ∑' p : Fin 2 → ℤ, L.regEisSummand s z p

/-! ## Absolute convergence -/

theorem linear_ne_zero_of_ne_zero {z : ℂ} (hz : z ∈ upperHalfSet) {p : Fin 2 → ℤ} (hp : p ≠ 0) :
    (p 0 : ℂ) * z + p 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
  have hz' : 0 < z.im := hz
  have h0 : p 0 = 0 := by
    have : (p 0 : ℝ) = 0 := by
      rcases mul_eq_zero.1 him with h | h
      · exact h
      · exact absurd h hz'.ne'
    exact_mod_cast this
  simp only [add_re, intCast_re, h0, Int.cast_zero, zero_mul, zero_re] at hre
  apply hp
  funext i
  fin_cases i
  · exact h0
  · simp only [zero_add] at hre
    exact_mod_cast hre

theorem ne_zero_of_isCoprime {p : Fin 2 → ℤ} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 := by
  intro hp
  rw [hp] at h
  simp only [Pi.zero_apply] at h
  exact not_isCoprime_zero_zero h

/-- The scalar factor has modulus `(Im z)^s |w|^{-(2+2s)}`. -/
theorem norm_eisRegularizer_mul_inv_sq {s : ℝ} {z : ℂ} (hz : z ∈ upperHalfSet) {w : ℂ} (hw : w ≠ 0) :
    ‖(((z.im / normSq w) ^ s : ℝ) : ℂ) * (w ^ 2)⁻¹‖ = z.im ^ s * ‖w‖ ^ (-(2 + 2 * s)) := by
  have hy : 0 < z.im := hz
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg hy.le (normSq_nonneg _)) _),
    Complex.normSq_eq_norm_sq, Real.div_rpow hy.le (by positivity),
    show -(2 + 2 * s) = -(2 * s) + -2 by ring, Real.rpow_add hwpos, Real.rpow_neg hwpos.le,
    Real.rpow_neg hwpos.le, Real.rpow_mul hwpos.le, Real.rpow_two]
  ring

theorem norm_regEisSummand_le {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ upperHalfSet)
    (p : Fin 2 → ℤ) :
    ‖L.regEisSummand s z p‖ ≤
      z.im ^ s * (EisensteinSeries.r (UpperHalfPlane.mk z hz) ^ (-(2 + 2 * s)) *
        ‖p‖ ^ (-(2 + 2 * s))) := by
  have hy : 0 < z.im := hz
  have hb := EisensteinSeries.summand_bound (UpperHalfPlane.mk z hz) (k := 2 + 2 * s)
    (by positivity) p
  rw [UpperHalfPlane.coe_mk] at hb
  unfold regEisSummand
  split_ifs with h
  · rw [norm_smul]
    have hw := linear_ne_zero_of_ne_zero hz (ne_zero_of_isCoprime h)
    calc ‖(((eisRegularizer s z p : ℝ) : ℂ) * (((p 0 : ℂ) * z + p 1) ^ 2)⁻¹)‖ *
          ‖L.gaussColumn (p 0) (p 1)‖
        ≤ ‖(((eisRegularizer s z p : ℝ) : ℂ) * (((p 0 : ℂ) * z + p 1) ^ 2)⁻¹)‖ * 1 :=
          mul_le_mul_of_nonneg_left (L.norm_gaussColumn_le h) (norm_nonneg _)
      _ = z.im ^ s * ‖(p 0 : ℂ) * z + p 1‖ ^ (-(2 + 2 * s)) := by
          rw [mul_one, eisRegularizer, norm_eisRegularizer_mul_inv_sq hz hw]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  · rw [norm_zero]
    have := EisensteinSeries.r_pos (UpperHalfPlane.mk z hz)
    positivity

/-- Absolute convergence for `s > 0`. -/
theorem summable_norm_regEisSummand {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    Summable fun p ↦ ‖L.regEisSummand s z p‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (L.norm_regEisSummand_le hs.le hz)
    (((EisensteinSeries.summable_one_div_norm_rpow (k := 2 + 2 * s) (by linarith)).mul_left _).mul_left _)

theorem summable_regEisSummand {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    Summable (L.regEisSummand s z) :=
  (L.summable_norm_regEisSummand hs hz).of_norm

/-! ## The T law -/

/-- The reindexing `(c, d) ↦ (c, c + d)`. -/
def eisShift : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun p := ![p 0, p 0 + p 1]
  invFun q := ![q 0, q 1 - q 0]
  left_inv p := by funext i; fin_cases i <;> simp
  right_inv q := by funext i; fin_cases i <;> simp

theorem regEisSummand_add_one (s : ℝ) (z : ℂ) (p : Fin 2 → ℤ) :
    L.regEisSummand s (z + 1) p = L.gaussT (L.regEisSummand s z (eisShift p)) := by
  have hcop : IsCoprime (p 0) (p 1) ↔ IsCoprime (p 0) (p 0 + p 1) := by
    rw [show p 0 + p 1 = p 1 + p 0 * 1 by ring, IsCoprime.add_mul_left_right_iff]
  unfold regEisSummand eisRegularizer
  simp only [eisShift, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  by_cases h : IsCoprime (p 0) (p 1)
  · rw [if_pos h, if_pos (hcop.1 h), gaussT_smul]
    have hF : L.gaussColumn (p 0) (p 1) = L.gaussT (L.gaussColumn (p 0) (p 0 + p 1)) := by
      have := L.gaussColumn_sub_self (p 0) (p 0 + p 1)
      rwa [show p 0 + p 1 - p 0 = p 1 by ring] at this
    rw [hF]
    have hw : ((p 0 : ℂ) * (z + 1) + p 1) = (p 0 : ℂ) * z + ((p 0 + p 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [hw, add_im, one_im, add_zero]
  · rw [if_neg h, if_neg (mt hcop.2 h), gaussT_zero]

/-- The T law `E_s(z + 1) = T₀ E_s(z)`. -/
theorem regEisenstein_add_one {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    L.regEisenstein s (z + 1) = L.gaussT (L.regEisenstein s z) := by
  unfold regEisenstein
  simp_rw [L.regEisSummand_add_one]
  have h1 : ∑' p, L.gaussT (L.regEisSummand s z (eisShift p)) =
      L.gaussT (∑' p, L.regEisSummand s z p) :=
    (eisShift.tsum_eq (fun q ↦ L.gaussT (L.regEisSummand s z q))).trans
      ((L.gaussTCLM).map_tsum (L.summable_regEisSummand hs hz)).symm
  rw [h1, gaussT_smul]

/-! ## The S law -/

/-- The reindexing `(c, d) ↦ (d, -c)`. -/
def eisSwap : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun p := ![p 1, -p 0]
  invFun q := ![-q 1, q 0]
  left_inv p := by funext i; fin_cases i <;> simp
  right_inv q := by funext i; fin_cases i <;> simp

theorem regEisSummand_neg_inv {z : ℂ} (hz : z ∈ upperHalfSet) (s : ℝ) (p : Fin 2 → ℤ) :
    L.regEisSummand s (-z⁻¹) p = z ^ 2 • L.gaussU (L.regEisSummand s z (eisSwap p)) := by
  have hz0 : z ≠ 0 := ne_zero_of_mem hz
  have hcop : IsCoprime (p 0) (p 1) ↔ IsCoprime (p 1) (-p 0) := by
    rw [IsCoprime.neg_right_iff, isCoprime_comm]
  unfold regEisSummand eisRegularizer
  simp only [eisSwap, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  by_cases h : IsCoprime (p 0) (p 1)
  · rw [if_pos h, if_pos (hcop.1 h), gaussU_smul, smul_smul]
    have hF : L.gaussColumn (p 0) (p 1) = L.gaussU (L.gaussColumn (p 1) (-p 0)) := by
      have := L.gaussColumn_neg_inv_of_isCoprime (c := p 1) (d := -p 0) (hcop.1 h)
      rwa [neg_neg] at this
    rw [hF]
    congr 1
    have hw : (p 0 : ℂ) * -z⁻¹ + p 1 = ((p 1 : ℂ) * z + ((-p 0 : ℤ) : ℂ)) / z := by
      field_simp
      push_cast
      ring
    have hN : normSq z ≠ 0 := (normSq_pos.2 hz0).ne'
    have hR : (-z⁻¹).im / normSq ((p 0 : ℂ) * -z⁻¹ + p 1) =
        z.im / normSq ((p 1 : ℂ) * z + ((-p 0 : ℤ) : ℂ)) := by
      rw [SMSFormula.BoundedClusterAnomaly.neg_inv_im, hw, normSq_div]
      field_simp
    rw [hR, hw, div_pow, inv_div, div_eq_mul_inv]
    ring
  · rw [if_neg h, if_neg (mt hcop.2 h), gaussU_zero, smul_zero]

/-- The exact S law `E_s(-1/z) = z² U E_s(z)`. -/
theorem regEisenstein_neg_inv {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    L.regEisenstein s (-z⁻¹) = z ^ 2 • L.gaussU (L.regEisenstein s z) := by
  unfold regEisenstein
  simp_rw [L.regEisSummand_neg_inv hz]
  have h1 : ∑' p, z ^ 2 • L.gaussU (L.regEisSummand s z (eisSwap p)) =
      z ^ 2 • L.gaussU (∑' p, L.regEisSummand s z p) :=
    (eisSwap.tsum_eq (fun q ↦ z ^ 2 • L.gaussU (L.regEisSummand s z q))).trans
      ((z ^ 2 • L.gaussUCLM).map_tsum (L.summable_regEisSummand hs hz)).symm
  rw [h1, gaussU_smul, smul_comm]

end PositiveDefiniteIntegralLattice
