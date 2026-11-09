import SMSFormula.RationalLatticeCosetGroupedBound
import SMSFormula.RationalAdeleSingularSeriesLocalDensity
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The coset singular series

For a rank-four lattice, `u ∈ ℤ⁴` and `λ ∈ ℤ` with nonzero target `M = q(adj(S) u) + D²λ`:

* the coset local density `δ^{cos}_p(u, λ) = lim_k R_{p^k}(u, λ)` exists at every prime and is the sum of the
  prime-power coefficients (`hasSum_cosetGRCoeff_primePow`): by orthogonality the counts at `p^k` are the partial sums,
  and the squaring bound makes the series absolute;
* at every prime `p ∤ D` it is the local density at the fixed target `M`
  (`cosetLocalDensity_eq_localResidueDensity`);
* The coset singular series (`hasSum_cosetGRCoeff`): `Σ_c A^{cos}_c(u, λ) = ∏'_p δ^{cos}_p(u, λ)`, by Mathlib's
  Euler product for the multiplicative, absolutely summable coset coefficients.
No bad-prime density is chosen: every local factor is a limit of counts.  Nothing is chosen.
-/

noncomputable section

open Finset Filter Topology

namespace PositiveDefiniteIntegralLattice

variable (L : PositiveDefiniteIntegralLattice 4)

/-- The coset local density `δ^{cos}_p(u, λ) = lim_k R_{p^k}(u, λ)`. -/
def cosetLocalDensity (u : Fin 4 → ℤ) (lam : ℤ) (p : ℕ) : ℝ :=
  limUnder atTop fun k : ℕ ↦ L.cosetResidueCount u lam (p ^ k)

theorem summable_norm_cosetGRCoeff_primePow (u : Fin 4 → ℤ) (lam : ℤ) {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ ↦ ‖L.cosetGRCoeff u lam (p ^ j)‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left ((L.polarGramMatrix.det.natAbs : ℝ) ^ 2))
  refine (L.norm_cosetGRCoeff_primePow_le u lam hp j).trans (le_of_eq ?_)
  rw [div_pow, one_pow, div_eq_mul_one_div]

/-- The local series: `Σ_j A^{cos}_{p^j}(u, λ) = δ^{cos}_p(u, λ)` at every prime. -/
theorem hasSum_cosetGRCoeff_primePow (u : Fin 4 → ℤ) (lam : ℤ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ ↦ L.cosetGRCoeff u lam (p ^ j)) ((L.cosetLocalDensity u lam p : ℝ) : ℂ) := by
  have hs := (L.summable_norm_cosetGRCoeff_primePow u lam hp).of_norm
  set S := ∑' j : ℕ, L.cosetGRCoeff u lam (p ^ j) with hS
  -- the counts are the partial sums
  have hpart : Tendsto (fun k : ℕ ↦ ((L.cosetResidueCount u lam (p ^ k) : ℝ) : ℂ)) atTop (𝓝 S) := by
    have h := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun k ↦ ?_
    simp only [Function.comp_def]
    exact L.sum_range_cosetGRCoeff_primePow u lam hp k
  have hre : Tendsto (fun k : ℕ ↦ L.cosetResidueCount u lam (p ^ k)) atTop (𝓝 S.re) := by
    have := (Complex.continuous_re.tendsto S).comp hpart
    simpa [Function.comp_def] using this
  have him : S.im = 0 := by
    have := (Complex.continuous_im.tendsto S).comp hpart
    simp only [Function.comp_def, Complex.ofReal_im] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have hSreal : S = ((S.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hlim : L.cosetLocalDensity u lam p = S.re := hre.limUnder_eq
  rw [hlim, ← hSreal]
  exact hs.hasSum

/-- At every prime `p ∤ D` the coset local density is the local density at the fixed target. -/
theorem cosetLocalDensity_eq_localResidueDensity (u : Fin 4 → ℤ) (lam : ℤ) {p : ℕ} (hp : p.Prime)
    (hpD : ¬ p ∣ L.polarGramMatrix.det.natAbs) :
    L.cosetLocalDensity u lam p = L.localResidueDensity (L.cosetStandardTarget u lam) p := by
  unfold cosetLocalDensity localResidueDensity
  congr 1
  funext k
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  exact L.cosetResidueCount_eq_normalizedResidueCount u lam
    (Nat.Coprime.pow_right k ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpD)))

/-- The coset singular series: `Σ_c A^{cos}_c(u, λ) = ∏'_p δ^{cos}_p(u, λ)` for nonzero target. -/
theorem hasSum_cosetGRCoeff (u : Fin 4 → ℤ) (lam : ℤ) (hM : L.cosetStandardTarget u lam ≠ 0) :
    HasSum (L.cosetGRCoeff u lam)
      (∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ)) := by
  obtain ⟨K, -, hK⟩ := L.exists_summable_norm_cosetGRCoeff_le_sqrt
  have hsum := (hK u lam hM).1
  have hE := EulerProduct.eulerProduct_tprod (f := L.cosetGRCoeff u lam) (L.cosetGRCoeff_one u lam)
    (fun h ↦ L.cosetGRCoeff_mul_of_coprime u lam h) hsum (L.cosetGRCoeff_zero u lam)
  have hloc : ∀ p : Nat.Primes, ∑' e, L.cosetGRCoeff u lam ((p : ℕ) ^ e) =
      ((L.cosetLocalDensity u lam p : ℝ) : ℂ) := fun p ↦
    (L.hasSum_cosetGRCoeff_primePow u lam p.2).tsum_eq
  simp_rw [hloc] at hE
  rw [hE]
  exact hsum.of_norm.hasSum

end PositiveDefiniteIntegralLattice
