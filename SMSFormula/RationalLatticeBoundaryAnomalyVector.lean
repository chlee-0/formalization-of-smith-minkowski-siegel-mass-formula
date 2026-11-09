import SMSFormula.RationalLatticeRegularizedEisenstein
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The boundary anomaly vector `W_s` is bounded and lies in `K`

The zero frequency of the regularized rows is the explicit vector

`W_s = -κ(s) Σ_{c ≥ 1} c^{-2s} b_c`,  `b_c = c⁻² Σ*_{a mod c} Π₀ F(c, a)`   (`gaussBoundaryAnomaly`),

with the zero-mode constant `κ(s) = s/(1+s) ∫_ℝ (1+u²)^{-1-s} du` (`zeroModeKappa`, (5.4)).
This file proves the bounds on `W_s` used by the bounded cluster lemma, with no limit and no residue:

* `0 ≤ κ(s) ≤ π s` (`zeroModeKappa_le`), from `(1+u²)^{-1-s} ≤ (1+u²)⁻¹` and `∫ (1+u²)⁻¹ = π`;
* `b_c ∈ K = Inv^⊥ ∩ ker(T₀ - 1)` and `‖b_c‖ ≤ φ(c)/c² ≤ 1/c` (Euclid: `‖Π₀ F‖ ≤ 1`);
* for `s > 0` the series is absolute, `W_s ∈ K` (`K` is closed), and
  `‖W_s‖ ≤ π s (1 + 1/(2s)) = π (s + 1/2)` (`norm_gaussBoundaryAnomaly_le`), using Mathlib's
  `ZetaAsymptotics.zeta_limit_aux1` for `Σ_{c ≥ 1} c^{-1-2s} ≤ 1 + 1/(2s)`.

The unit numerators are indexed by `0 ≤ a < c` as in the grouped coefficient; the vector
`Π₀ F(c, a)` depends only on `a mod c` (`gaussPi0_gaussColumn_add`).  Nothing is chosen.
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace PositiveDefiniteIntegralLattice

/-! ## The zero-mode constant -/

/-- `κ(s) = s/(1+s) ∫_ℝ (1+u²)^{-1-s} du`. -/
def zeroModeKappa (s : ℝ) : ℝ := s / (1 + s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 + s))

theorem one_add_sq_rpow_le_inv {s : ℝ} (hs : 0 ≤ s) (u : ℝ) :
    (1 + u ^ 2) ^ (-(1 + s)) ≤ (1 + u ^ 2)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg u]) (by linarith)

theorem integrable_one_add_sq_rpow {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun u : ℝ ↦ (1 + u ^ 2) ^ (-(1 + s)) := by
  refine integrable_inv_one_add_sq.mono' ?_ (Eventually.of_forall fun u ↦ ?_)
  · exact (Continuous.rpow_const (by fun_prop) fun u ↦ Or.inl (by positivity)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact one_add_sq_rpow_le_inv hs u

theorem integral_one_add_sq_rpow_le {s : ℝ} (hs : 0 ≤ s) :
    ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 + s)) ≤ Real.pi := by
  rw [← integral_univ_inv_one_add_sq]
  exact integral_mono (integrable_one_add_sq_rpow hs) integrable_inv_one_add_sq
    (one_add_sq_rpow_le_inv hs)

theorem integral_one_add_sq_rpow_nonneg (s : ℝ) : 0 ≤ ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 + s)) :=
  integral_nonneg fun u ↦ by positivity

theorem zeroModeKappa_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ zeroModeKappa s :=
  mul_nonneg (div_nonneg hs (by linarith)) (integral_one_add_sq_rpow_nonneg s)

/-- `κ(s) ≤ π s`. -/
theorem zeroModeKappa_le {s : ℝ} (hs : 0 ≤ s) : zeroModeKappa s ≤ Real.pi * s := by
  unfold zeroModeKappa
  have h1 : s / (1 + s) ≤ s := div_le_self hs (by linarith)
  calc s / (1 + s) * ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 + s))
      ≤ s * Real.pi :=
        mul_le_mul h1 (integral_one_add_sq_rpow_le hs) (integral_one_add_sq_rpow_nonneg s) hs
    _ = Real.pi * s := mul_comm _ _

/-! ## The row vectors `b_c` -/

variable (L : PositiveDefiniteIntegralLattice 4)

/-- `Π₀ F(c, a)` depends only on `a mod c`. -/
theorem gaussPi0_gaussColumn_add (c a : ℤ) :
    L.gaussPi0 (L.gaussColumn c (a + c)) = L.gaussPi0 (L.gaussColumn c a) := by
  have h := L.gaussColumn_sub_self c (a + c)
  rw [add_sub_cancel_right] at h
  rw [h]
  funext b
  unfold gaussPi0 gaussT
  split_ifs with hb
  · rw [hb, one_mul]
  · rfl

/-- `b_c = c⁻² Σ*_{a mod c} Π₀ F(c, a)`. -/
def gaussBoundaryRowVector (c : ℕ) : L.PolarDiscriminantGroup → ℂ :=
  ((c : ℂ) ^ 2)⁻¹ • ∑ a ∈ (Finset.range c).filter (fun a ↦ c.Coprime a),
    L.gaussPi0 (L.gaussColumn c a)

theorem gaussBoundaryRowVector_mem_gaussBoundaryK (c : ℕ) :
    L.gaussBoundaryRowVector c ∈ L.gaussBoundaryK := by
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a ha ↦ ?_)
  have hca : c.Coprime a := (Finset.mem_filter.1 ha).2
  exact L.gaussPi0_gaussColumn_mem_gaussBoundaryK (Nat.isCoprime_iff_coprime.2 hca)

/-- `‖b_c‖ ≤ φ(c)/c²`. -/
theorem norm_gaussBoundaryRowVector_le_totient (c : ℕ) :
    ‖L.gaussBoundaryRowVector c‖ ≤ (c.totient : ℝ) / (c : ℝ) ^ 2 := by
  unfold gaussBoundaryRowVector
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_natCast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ (Finset.range c).filter (fun a ↦ c.Coprime a), ‖L.gaussPi0 (L.gaussColumn c a)‖
      ≤ ∑ a ∈ (Finset.range c).filter (fun a ↦ c.Coprime a), (1 : ℝ) :=
        Finset.sum_le_sum fun a ha ↦
          L.norm_gaussPi0_gaussColumn_le (Nat.isCoprime_iff_coprime.2 (Finset.mem_filter.1 ha).2)
    _ = (c.totient : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.totient_eq_card_coprime]

/-- `‖b_c‖ ≤ 1/c`. -/
theorem norm_gaussBoundaryRowVector_le (c : ℕ) : ‖L.gaussBoundaryRowVector c‖ ≤ (c : ℝ)⁻¹ := by
  refine (L.norm_gaussBoundaryRowVector_le_totient c).trans ?_
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [div_le_iff₀ (by positivity), sq, ← mul_assoc, inv_mul_cancel₀ hc'.ne', one_mul]
  exact_mod_cast Nat.totient_le c

/-! ## The anomaly vector `W_s` -/

/-- The boundary anomaly vector `W_s = -κ(s) Σ_{c ≥ 1} c^{-2s} b_c` (the `c = 0` term is `b_0 = 0`). -/
def gaussBoundaryAnomaly (s : ℝ) : L.PolarDiscriminantGroup → ℂ :=
  -((zeroModeKappa s : ℝ) : ℂ) •
    ∑' c : ℕ, (((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c

theorem norm_anomalyTerm_le (s : ℝ) (c : ℕ) :
    ‖(((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c‖ ≤ 1 / (c : ℝ) ^ (1 + 2 * s) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have h0 : L.gaussBoundaryRowVector 0 = 0 := by simp [gaussBoundaryRowVector]
    rw [h0, smul_zero, norm_zero]
    exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
  calc (c : ℝ) ^ (-2 * s) * ‖L.gaussBoundaryRowVector c‖ ≤ (c : ℝ) ^ (-2 * s) * (c : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (L.norm_gaussBoundaryRowVector_le c) (Real.rpow_nonneg hc'.le _)
    _ = 1 / (c : ℝ) ^ (1 + 2 * s) := by
        rw [Real.rpow_add hc', Real.rpow_one, show -2 * s = -(2 * s) by ring,
          Real.rpow_neg hc'.le]
        field_simp

theorem summable_one_div_rpow_one_add {s : ℝ} (hs : 0 < s) :
    Summable fun c : ℕ ↦ 1 / (c : ℝ) ^ (1 + 2 * s) :=
  Real.summable_one_div_nat_rpow.2 (by linarith)

theorem summable_anomalyTerm {s : ℝ} (hs : 0 < s) :
    Summable fun c : ℕ ↦ (((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c :=
  Summable.of_norm_bounded (summable_one_div_rpow_one_add hs) (L.norm_anomalyTerm_le s)

/-- `Σ_{c ≥ 1} c^{-1-2s} ≤ 1 + 1/(2s)`. -/
theorem tsum_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) :
    ∑' c : ℕ, 1 / (c : ℝ) ^ (1 + 2 * s) ≤ 1 + 1 / (2 * s) := by
  have hσ : 1 < 1 + 2 * s := by linarith
  rw [(summable_one_div_rpow_one_add hs).tsum_eq_zero_add]
  have h0 : 1 / ((0 : ℕ) : ℝ) ^ (1 + 2 * s) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
  rw [h0, zero_add]
  have h := ZetaAsymptotics.zeta_limit_aux1 hσ
  have hterm : 0 ≤ ZetaAsymptotics.term_tsum (1 + 2 * s) :=
    tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) _
  have heq : ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ (1 + 2 * s) =
      ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + 2 * s) := by
    push_cast; rfl
  rw [heq]
  have : 1 + 2 * s - 1 = 2 * s := by ring
  rw [this] at h
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * s) hterm]

/-- `W_s ∈ K` for `s > 0`. -/
theorem gaussBoundaryAnomaly_mem_gaussBoundaryK {s : ℝ} (hs : 0 < s) :
    L.gaussBoundaryAnomaly s ∈ L.gaussBoundaryK := by
  refine Submodule.smul_mem _ _ ?_
  have hK : IsClosed (L.gaussBoundaryK : Set (L.PolarDiscriminantGroup → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  refine hK.mem_of_tendsto (L.summable_anomalyTerm hs).hasSum.tendsto_sum_nat
    (Eventually.of_forall fun N ↦ ?_)
  exact Submodule.sum_mem _ fun c _ ↦
    Submodule.smul_mem _ _ (L.gaussBoundaryRowVector_mem_gaussBoundaryK c)

/-- The anomaly bound (6.3): `‖W_s‖ ≤ π (s + 1/2)` for `s > 0`. -/
theorem norm_gaussBoundaryAnomaly_le {s : ℝ} (hs : 0 < s) :
    ‖L.gaussBoundaryAnomaly s‖ ≤ Real.pi * (s + 1 / 2) := by
  unfold gaussBoundaryAnomaly
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (zeroModeKappa_nonneg hs.le)]
  have hsum : ‖∑' c : ℕ, (((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c‖ ≤
      1 + 1 / (2 * s) :=
    (norm_tsum_le_tsum_norm (L.summable_anomalyTerm hs).norm).trans
      (((L.summable_anomalyTerm hs).norm.tsum_le_tsum (L.norm_anomalyTerm_le s)
        (summable_one_div_rpow_one_add hs)).trans (tsum_one_div_rpow_one_add_le hs))
  calc zeroModeKappa s * ‖∑' c : ℕ, (((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c‖
      ≤ (Real.pi * s) * (1 + 1 / (2 * s)) :=
        mul_le_mul (zeroModeKappa_le hs.le) hsum (norm_nonneg _) (by positivity)
    _ = Real.pi * (s + 1 / 2) := by field_simp

/-- The uniform bound on `0 < s ≤ 1` used by the bounded cluster lemma. -/
theorem norm_gaussBoundaryAnomaly_le_uniform {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ‖L.gaussBoundaryAnomaly s‖ ≤ Real.pi * (3 / 2) :=
  (L.norm_gaussBoundaryAnomaly_le hs).trans
    (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)

/-! ## The reduction to the row limit (Lemma 7 applied) -/

/-- The boundary reduction: if `H_s = E_s - y^{-1-s} W_s` converges on the upper half-plane to a
holomorphic `E₀`, then `W_s → 0` and `E₀(-1/z) = z² U E₀(z)`.  Every other input of the bounded cluster
lemma (the exact S law of `E_s`, `W_s ∈ K`, the uniform bound, no `U`-fixed vector in `K`) is
proved. -/
theorem tendsto_gaussBoundaryAnomaly_and_sLaw (E₀ : ℂ → L.PolarDiscriminantGroup → ℂ)
    (hE₀ : DifferentiableOn ℂ E₀ SMSFormula.WeightTwoConstantTerm.upperHalfSet)
    (hH : ∀ z ∈ SMSFormula.WeightTwoConstantTerm.upperHalfSet,
      Tendsto (fun s ↦ L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
        (𝓝[>] 0) (𝓝 (E₀ z))) :
    Tendsto L.gaussBoundaryAnomaly (𝓝[>] 0) (𝓝 0) ∧
      ∀ z ∈ SMSFormula.WeightTwoConstantTerm.upperHalfSet, E₀ (-z⁻¹) = z ^ 2 • L.gaussU (E₀ z) := by
  have h := SMSFormula.BoundedClusterAnomaly.tendsto_zero_and_sLaw_of_boundedCluster
    L.gaussUCLM L.gaussBoundaryK L.gaussUCLM_eq_self_imp L.gaussBoundaryAnomaly
    (fun s hs ↦ L.gaussBoundaryAnomaly_mem_gaussBoundaryK hs) (Real.pi * (3 / 2))
    (fun s hs hs1 ↦ L.norm_gaussBoundaryAnomaly_le_uniform hs hs1)
    (fun s z ↦ L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
    E₀ hE₀ hH (fun s hs z hz ↦ by
      simp only [sub_add_cancel, gaussUCLM_apply]
      exact L.regEisenstein_neg_inv hs hz)
  exact ⟨h.1, fun z hz ↦ by simpa using h.2 z hz⟩

end PositiveDefiniteIntegralLattice
