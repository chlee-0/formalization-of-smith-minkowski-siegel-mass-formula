import SMSFormula.AdelicGaussianRankFourLatticeShell
import SMSFormula.RationalLatticeRowLimitIdentification
import SMSFormula.RationalAdeleSingularSeriesRepresentation

/-!
# The lattice-side aggregate of the rank-four shell densities (the `ρ_Φ` half of `hE`)

For the rank-four lattice shell density `ρ_Φ(b) = [b ∈ ℤ] Re Â_a(b) · ∏'_p δ_p(b)`
(`latticeShellDensity`, the density of the all-shell identity
`exists_complement_representedNormTheta_latticeTest_mul_spinTamagawa_eq_rankFour`):

* `ρ_Φ ≥ 0` (closed form of `Â_a`, the normalized counts are nonnegative);
* `ρ_Φ` is summable over the represented nonzero norms (rank-four Gauss–Ramanujan bound
  `Σ_q ‖A_q(M)‖ ≤ K|M|^c` and `summable_norm_fourier_polarArchimedeanBruhatFactor_mul_pow`);
* `1 + Σ_b ρ_Φ(b) = E_std(a)`, the standard aggregate (`latticeShellDensity_aggregate`).  The reindexing from the
  represented norms to the integers is exact: `ρ_Φ` vanishes off the integers, `Â_a` vanishes at nonpositive
  frequencies, and a positive integer with nonzero singular series is represented over `ℚ` (rank-four
  `exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero`).
Nothing is chosen.
-/

noncomputable section

open Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

theorem latticeShellDensity_intCast (L : PositiveDefiniteIntegralLattice (n + 1)) (a : ℝ) (k : ℤ) :
    latticeShellDensity L a (k : ℚ) =
      (𝓕 (L.polarArchimedeanBruhatFactor a) (k : ℝ)).re *
        ∏' p : Nat.Primes, L.localResidueDensity k p := by
  unfold latticeShellDensity
  rw [if_pos (Rat.den_intCast k), Rat.num_intCast]

theorem latticeShellDensity_eq_zero_of_den_ne_one (L : PositiveDefiniteIntegralLattice (n + 1)) (a : ℝ) {q : ℚ}
    (hq : q.den ≠ 1) : latticeShellDensity L a q = 0 := by
  unfold latticeShellDensity
  rw [if_neg hq]

theorem tprod_localResidueDensity_nonneg (L : PositiveDefiniteIntegralLattice (n + 1)) {M : ℤ} (hM : M ≠ 0) :
    0 ≤ ∏' p : Nat.Primes, L.localResidueDensity M p := by
  by_cases hmult : Multipliable fun p : Nat.Primes ↦ L.localResidueDensity M p
  · exact ge_of_tendsto hmult.hasProd
      (Eventually.of_forall fun s ↦ Finset.prod_nonneg fun q _ ↦ by
        haveI : Fact (Nat.Prime q.1) := ⟨q.2⟩
        obtain ⟨k, hk⟩ := (L.eventually_normalizedResidueCount_eq_localResidueDensity q.1 hM).exists
        rw [← hk, normalizedResidueCount]
        exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _))
  · rw [tprod_eq_one_of_not_multipliable hmult]
    exact zero_le_one

/-- The integer lattice shell density vanishes at nonpositive integers. -/
theorem latticeShellDensity_intCast_of_nonpos (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {a : ℝ}
    (ha : 0 < a) {k : ℤ} (hk : k ≤ 0) : latticeShellDensity L a (k : ℚ) = 0 := by
  rw [latticeShellDensity_intCast, L.fourier_polarArchimedeanBruhatFactor_of_nonpos ha (by omega)
    (by exact_mod_cast hk), Complex.zero_re, zero_mul]

theorem latticeShellDensity_nonneg (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (q : ℚ) : 0 ≤ latticeShellDensity L a q := by
  by_cases hden : q.den = 1
  · have hq : ((q.num : ℤ) : ℚ) = q := by
      have := Rat.num_div_den q
      rwa [hden, Nat.cast_one, div_one] at this
    rw [← hq]
    rcases le_or_gt q.num 0 with hk | hk
    · rw [latticeShellDensity_intCast_of_nonpos L hn ha hk]
    · rw [latticeShellDensity_intCast, L.fourier_polarArchimedeanBruhatFactor_of_pos ha (by omega)
        (by exact_mod_cast hk), Complex.ofReal_re]
      have hdet : (0 : ℝ) < (L.polarRealDeterminantScale : ℝ)⁻¹ :=
        inv_pos.2 (by exact_mod_cast L.polarRealDeterminantScale_pos)
      have hΓ : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
      have hk' : (0 : ℝ) < (q.num : ℝ) := by exact_mod_cast hk
      have hΔ := tprod_localResidueDensity_nonneg L hk.ne'
      positivity
  · rw [latticeShellDensity_eq_zero_of_den_ne_one L a hden]

/-- The integer lattice shell densities are summable. -/
theorem summable_latticeShellDensity_intCast (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {a : ℝ}
    (ha : 0 < a) : Summable fun k : ℤ ↦ latticeShellDensity L a (k : ℚ) := by
  obtain ⟨K, c, hK0, hK⟩ := L.exists_summable_norm_gaussRamanujanCoefficient_le hn
  refine Summable.of_norm_bounded
    ((L.summable_norm_fourier_polarArchimedeanBruhatFactor_mul_pow ha (by omega) c).mul_left K)
    fun k ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · rw [latticeShellDensity_intCast_of_nonpos L hn ha le_rfl, norm_zero]
    positivity
  · rw [latticeShellDensity_intCast, norm_mul]
    have hsum := L.hasSum_gaussRamanujanCoefficient_tprod_localResidueDensity hn hk
    have hΔ : ‖∏' p : Nat.Primes, L.localResidueDensity k p‖ ≤ K * |(k : ℝ)| ^ c := by
      have h1 : ‖((∏' p : Nat.Primes, L.localResidueDensity k p : ℝ) : ℂ)‖ ≤
          ∑' q, ‖L.gaussRamanujanCoefficient q k‖ := by
        rw [← hsum.tsum_eq]
        exact norm_tsum_le_tsum_norm (hK k hk).1
      rw [Complex.norm_real] at h1
      refine h1.trans ((hK k hk).2.trans_eq ?_)
      rw [Nat.cast_natAbs, Int.cast_abs]
    calc ‖(𝓕 (L.polarArchimedeanBruhatFactor a) (k : ℝ)).re‖ *
          ‖∏' p : Nat.Primes, L.localResidueDensity k p‖
        ≤ ‖𝓕 (L.polarArchimedeanBruhatFactor a) (k : ℝ)‖ * (K * |(k : ℝ)| ^ c) :=
          mul_le_mul (by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _) hΔ (norm_nonneg _)
            (norm_nonneg _)
      _ = K * (‖𝓕 (L.polarArchimedeanBruhatFactor a) (k : ℝ)‖ * |(k : ℝ)| ^ c) := by ring

/-- The support of the lattice shell density on `ℚ` consists of represented nonzero norms. -/
theorem support_latticeShellDensity_subset (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {a : ℝ}
    (ha : 0 < a) :
    Function.support (latticeShellDensity L a) ⊆
      Set.range (Subtype.val : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℚ) := by
  intro q hq
  by_cases hden : q.den = 1
  · have hqk : ((q.num : ℤ) : ℚ) = q := by
      have := Rat.num_div_den q
      rwa [hden, Nat.cast_one, div_one] at this
    rw [Function.mem_support, ← hqk] at hq
    rcases le_or_gt q.num 0 with hk | hk
    · exact absurd (latticeShellDensity_intCast_of_nonpos L hn ha hk) hq
    · have hΔ : ∏' p : Nat.Primes, L.localResidueDensity q.num p ≠ 0 := by
        intro h0
        rw [latticeShellDensity_intCast, h0, mul_zero] at hq
        exact hq rfl
      obtain ⟨x, hx⟩ := L.exists_nativeRationalQuadraticForm_eq_of_tprod_localResidueDensity_ne_zero
        hn hk hΔ
      refine ⟨⟨q, ?_, x, ?_⟩, rfl⟩
      · rw [← hqk]; exact_mod_cast hk.ne'
      · rw [hx, hqk]
  · exact absurd (latticeShellDensity_eq_zero_of_den_ne_one L a hden) hq

theorem support_latticeShellDensity_subset_intCast (L : PositiveDefiniteIntegralLattice (n + 1)) (a : ℝ) :
    Function.support (latticeShellDensity L a) ⊆ Set.range (Int.cast : ℤ → ℚ) := by
  intro q hq
  by_cases hden : q.den = 1
  · refine ⟨q.num, ?_⟩
    have := Rat.num_div_den q
    rwa [hden, Nat.cast_one, div_one] at this
  · exact absurd (latticeShellDensity_eq_zero_of_den_ne_one L a hden) hq

/-- The reindexing: summing `ρ_Φ` over the represented nonzero norms is summing it over the integers. -/
theorem summable_and_tsum_latticeShellDensity_represented (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {a : ℝ} (ha : 0 < a) :
    Summable (fun b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm ↦
        latticeShellDensity L a b.1) ∧
      ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm, latticeShellDensity L a b.1 =
        ∑' k : ℤ, latticeShellDensity L a (k : ℚ) := by
  have hval : Function.Injective
      (Subtype.val : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm → ℚ) :=
    Subtype.val_injective
  have hint : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
  have hsQ : Summable (latticeShellDensity L a) :=
    (hint.summable_iff fun x hx ↦ Function.notMem_support.1 fun h ↦
      hx (support_latticeShellDensity_subset_intCast L a h)).1
      (summable_latticeShellDensity_intCast L hn ha)
  refine ⟨(hval.summable_iff fun x hx ↦ Function.notMem_support.1 fun h ↦
    hx (support_latticeShellDensity_subset L hn ha h)).2 hsQ, ?_⟩
  change ∑' b, latticeShellDensity L a (Subtype.val b) = ∑' k, latticeShellDensity L a (Int.cast k)
  rw [hval.tsum_eq (support_latticeShellDensity_subset L hn ha),
    hint.tsum_eq (support_latticeShellDensity_subset_intCast L a)]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

open IntegralFiniteAdelePhase

/-- The standard aggregate term is the integer lattice shell density. -/
theorem standardAggregate_term_eq_latticeShellDensity (L : PositiveDefiniteIntegralLattice 4) {a : ℝ} (ha : 0 < a)
    (k : ℤ) :
    𝓕 (L.polarArchimedeanBruhatFactor a) k *
        (if 0 < k then ((∏' p : Nat.Primes, L.localResidueDensity k p : ℝ) : ℂ) else 0) =
      ((latticeShellDensity L a (k : ℚ) : ℝ) : ℂ) := by
  rcases le_or_gt k 0 with hk | hk
  · rw [if_neg (not_lt.2 hk), mul_zero, latticeShellDensity_intCast_of_nonpos L (by norm_num) ha hk,
      Complex.ofReal_zero]
  · rw [if_pos hk, latticeShellDensity_intCast,
      L.fourier_polarArchimedeanBruhatFactor_of_pos ha (by norm_num) (by exact_mod_cast hk),
      Complex.ofReal_re]
    push_cast
    ring

/-- The lattice-side aggregate (rank four): `ρ_Φ ≥ 0`, `ρ_Φ` summable over the represented norms, and
`1 + Σ_b ρ_Φ(b) = E_std(a)`. -/
theorem latticeShellDensity_aggregate (L : PositiveDefiniteIntegralLattice 4) {a : ℝ} (ha : 0 < a) :
    (∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        0 ≤ latticeShellDensity L a b.1) ∧
      Summable (fun b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm ↦
        latticeShellDensity L a b.1) ∧
      (((1 + ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          latticeShellDensity L a b.1 : ℝ)) : ℂ) = L.standardAggregate a := by
  obtain ⟨hsum, htsum⟩ := summable_and_tsum_latticeShellDensity_represented L (n := 3) le_rfl ha
  refine ⟨fun b ↦ latticeShellDensity_nonneg L le_rfl ha _, hsum, ?_⟩
  rw [htsum, standardAggregate, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_tsum]
  congr 1
  exact tsum_congr fun k ↦ (standardAggregate_term_eq_latticeShellDensity L ha k).symm

end PositiveDefiniteIntegralLattice
