import SMSFormula.RationalAdeleGaussRamanujanRankFourBound
import SMSFormula.RationalAdeleRankOneEisensteinPoisson
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The ordered standard Eisenstein aggregate converges in rank four

For the polar Gaussian at scale `c > 0`, the rank-one Bruhat family is `B(t) = A_c(t) G(t)`, where
`A_c` is the archimedean factor and `G` the finite Gauss integral.  In rank four `Σ_t |B(t)|`
diverges, so the rank-five Poisson interchange is unavailable.  Order the rational parameters by
their denominator instead:

`E_Q(c) = 1 + Σ_{q < Q} Σ*_{a mod q} G(a/q) Σ_{ℓ ∈ ℤ} A_c(ℓ + a/q)`.

Then, in rank at least four,

`E_Q(c) → 1 + Σ_{k ≥ 1} Â_c(k) ∏'_p δ_p(k)`   (`tendsto_orderedStandardAggregate`),

where `Â_c` is the archimedean Fourier transform (zero at nonpositive frequencies).  Proof:

* for each denominator the real Poisson summation gives `Σ_ℓ A_c(ℓ + a/q) = Σ_k Â_c(k) e(k a/q)`,
  so the denominator term is `Σ_k Â_c(k) A_q(k)` with the Gauss--Ramanujan coefficient `A_q`;
* the grouped estimate `Σ_q ‖A_q(k)‖ ≤ K |k|^c` and the exponential decay of `Â_c` dominate;
* `Σ_q A_q(k) = ∏'_p δ_p(k)` (`hasSum_gaussRamanujanCoefficient_tprod_localResidueDensity`).

The limit is by dominated convergence of series (Tannery), not monotone; the approximants are not
nonnegative.  Nothing is chosen.
-/

noncomputable section

open Finset Filter Topology
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The archimedean Fourier transform with a polynomial weight -/

/-- `Σ_k ‖Â_c(k)‖ |k|^e < ∞` for every `e`. -/
theorem summable_norm_fourier_polarArchimedeanBruhatFactor_mul_pow {N : ℕ} (L : PositiveDefiniteIntegralLattice N)
    {c : ℝ} (hc : 0 < c) (hN : 3 ≤ N) (e : ℕ) :
    Summable fun k : ℤ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ * (|(k : ℝ)|) ^ e := by
  set K : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ *
    ((2 * Real.pi) ^ ((N : ℝ) / 2) / Real.Gamma ((N : ℝ) / 2)) with hKdef
  have hK : 0 ≤ K := by
    have hdet : 0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_nonneg.2 L.polarRealDeterminantScale_pos.le
    have hΓ : 0 < Real.Gamma ((N : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have ha : 0 < 2 * Real.pi * c := by positivity
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun m ↦ ?_)
      ((Real.summable_pow_mul_exp_neg_nat_mul (N + e) ha).mul_left K)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Int.cast_natCast, Nat.cast_zero,
        L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hN le_rfl, norm_zero, zero_mul]
      positivity
    · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [Int.cast_natCast, L.fourier_polarArchimedeanBruhatFactor_of_pos hc hN hmpos,
        Complex.norm_real, Real.norm_of_nonneg (by positivity), abs_of_pos hmpos]
      have hpow : (m : ℝ) ^ ((N : ℝ) / 2 - 1) ≤ (m : ℝ) ^ N := by
        rw [← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
        have : (0 : ℝ) ≤ (N : ℝ) := by positivity
        linarith
      calc K * (m : ℝ) ^ ((N : ℝ) / 2 - 1) * Real.exp (-(2 * Real.pi * c) * m) * (m : ℝ) ^ e
          ≤ K * (m : ℝ) ^ N * Real.exp (-(2 * Real.pi * c) * m) * (m : ℝ) ^ e := by
            gcongr
        _ = K * ((m : ℝ) ^ (N + e) * Real.exp (-(2 * Real.pi * c) * m)) := by ring
  · have hzero : (fun m : ℕ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c) ((-(m : ℤ) : ℤ) : ℝ)‖ *
        |(((-(m : ℤ) : ℤ) : ℝ))| ^ e) = fun _ ↦ 0 := by
      funext m
      have hm : ((-(m : ℤ) : ℤ) : ℝ) ≤ 0 := by
        push_cast
        exact neg_nonpos.2 (Nat.cast_nonneg m)
      rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hN hm, norm_zero, zero_mul]
    rw [hzero]
    exact summable_zero

/-! ## One denominator -/

/-- The denominator-`q` term of the ordered aggregate: `Σ*_{a mod q} G(a/q) Σ_ℓ A_c(ℓ + a/q)`. -/
def orderedStandardDenominatorTerm (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a ↦ q.Coprime a),
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((a : ℚ) / q) *
      ∑' m : ℤ, L.polarArchimedeanBruhatFactor c ((((a : ℚ) / q : ℚ) : ℝ) + m)

theorem fourier_coe_eq_fourierChar (k : ℤ) (r : ℚ) :
    fourier k ((r : ℝ) : UnitAddCircle) = ((Real.fourierChar (((k : ℚ) * r : ℚ) : ℝ) : Circle) : ℂ) := by
  rw [fourier_coe_eq_fourierChar_inv, ← AddChar.map_neg_eq_inv]
  congr 3
  push_cast
  ring

/-- One denominator, after real Poisson: the term is `Σ_k Â_c(k) A_q(k)`. -/
theorem orderedStandardDenominatorTerm_eq_tsum (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {c : ℝ}
    (hc : 0 < c) (q : ℕ) :
    L.orderedStandardDenominatorTerm c q =
      ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor c) k * L.gaussRamanujanCoefficient q k := by
  have hsumF := (L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn).of_norm
  have hterm : ∀ a : ℕ, ∑' m : ℤ, L.polarArchimedeanBruhatFactor c ((((a : ℚ) / q : ℚ) : ℝ) + m) =
      ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor c) k *
        ((Real.fourierChar (((k : ℚ) * ((a : ℚ) / q) : ℚ) : ℝ) : Circle) : ℂ) := by
    intro a
    rw [L.tsum_polarArchimedeanBruhatFactor_add_int hc hn]
    refine tsum_congr fun k ↦ ?_
    rw [fourier_coe_eq_fourierChar]
  have hsum_a : ∀ a ∈ (range q).filter (fun a ↦ q.Coprime a), Summable fun k : ℤ ↦
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((a : ℚ) / q) *
        (𝓕 (L.polarArchimedeanBruhatFactor c) k *
          ((Real.fourierChar (((k : ℚ) * ((a : ℚ) / q) : ℚ) : ℝ) : Circle) : ℂ)) := by
    intro a _
    refine Summable.mul_left _ ?_
    refine Summable.of_norm_bounded
      (L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn) fun k ↦ ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
  unfold orderedStandardDenominatorTerm gaussRamanujanCoefficient gaussRamanujanTerm
  simp_rw [hterm, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsum_a]
  refine tsum_congr fun k ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-! ## The limit -/

/-- For fixed `q`, `‖A_q(k)‖ ≤ Σ*_a ‖G(a/q)‖` uniformly in `k`. -/
theorem norm_gaussRamanujanCoefficient_le_sum (L : PositiveDefiniteIntegralLattice n) (q : ℕ) (k : ℤ) :
    ‖L.gaussRamanujanCoefficient q k‖ ≤ ∑ a ∈ (range q).filter (fun a ↦ q.Coprime a),
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral ((a : ℚ) / q)‖ := by
  unfold gaussRamanujanCoefficient gaussRamanujanTerm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [norm_mul, Circle.norm_coe, mul_one]

/-- The ordered standard aggregate converges (rank at least four):
`1 + Σ_{q < Q} (denominator-q term) → 1 + Σ_k Â_c(k) · [k > 0] ∏'_p δ_p(k)`. -/
theorem tendsto_orderedStandardAggregate (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun Q : ℕ ↦ 1 + ∑ q ∈ range Q, L.orderedStandardDenominatorTerm c q) atTop
      (𝓝 (1 + ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor c) k *
        (if 0 < k then ((∏' p : Nat.Primes, L.localResidueDensity k p : ℝ) : ℂ) else 0))) := by
  have hn1 : 3 ≤ n + 1 := by omega
  obtain ⟨K, e, hK0, hK⟩ := L.exists_summable_norm_gaussRamanujanCoefficient_le hn
  refine Tendsto.const_add _ ?_
  have hrew : ∀ Q : ℕ, ∑ q ∈ range Q, L.orderedStandardDenominatorTerm c q =
      ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor c) k *
        ∑ q ∈ range Q, L.gaussRamanujanCoefficient q k := by
    intro Q
    simp_rw [L.orderedStandardDenominatorTerm_eq_tsum hn1 hc, Finset.mul_sum]
    refine (Summable.tsum_finsetSum fun q _ ↦ ?_).symm
    refine Summable.of_norm_bounded
      ((L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn1).mul_right
        (∑ a ∈ (range q).filter (fun a ↦ q.Coprime a),
          ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
            ((a : ℚ) / q)‖)) fun k ↦ ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (L.norm_gaussRamanujanCoefficient_le_sum q k) (norm_nonneg _)
  simp_rw [hrew]
  have hFzero : ∀ k : ℤ, ¬ 0 < k → 𝓕 (L.polarArchimedeanBruhatFactor c) k = 0 := fun k hk ↦
    L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn1 (by exact_mod_cast not_lt.1 hk)
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k : ℤ ↦ K * (‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ * |(k : ℝ)| ^ e))
    ((L.summable_norm_fourier_polarArchimedeanBruhatFactor_mul_pow hc hn1 e).mul_left K)
    (fun k ↦ ?_) (Eventually.of_forall fun Q k ↦ ?_)
  · by_cases hk : 0 < k
    · rw [if_pos hk]
      exact ((L.hasSum_gaussRamanujanCoefficient_tprod_localResidueDensity hn
        hk.ne').tendsto_sum_nat).const_mul _
    · simp only [hFzero k hk, zero_mul]
      exact tendsto_const_nhds
  · by_cases hk : 0 < k
    · have hsum := (hK k hk.ne').1
      rw [norm_mul]
      calc ‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ *
            ‖∑ q ∈ range Q, L.gaussRamanujanCoefficient q k‖
          ≤ ‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ * (K * |(k : ℝ)| ^ e) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (norm_sum_le _ _).trans ((hsum.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _)).trans ?_)
            have h := (hK k hk.ne').2
            rwa [Nat.cast_natAbs, Int.cast_abs] at h
        _ = K * (‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ * |(k : ℝ)| ^ e) := by ring
    · rw [hFzero k hk, zero_mul, norm_zero]
      positivity

end PositiveDefiniteIntegralLattice
