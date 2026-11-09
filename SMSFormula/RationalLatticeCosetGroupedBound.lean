import SMSFormula.RationalLatticeCosetGaussBound
import SMSFormula.RationalAdeleGaussRamanujanRankFourBound

/-!
# The grouped estimate for every coset

For the rank-four coset coefficients `A^{cos}_c(u, λ)` and a nonzero target `M = q(adj(S) u) + D² λ`
(`= D² (q(ν) + λ)`),

`Σ_c ‖A^{cos}_c(u, λ)‖ ≤ e² (2 |M| |det F|)^{c₀}`   (`exists_summable_norm_cosetGRCoeff_le`),

with `c₀` depending only on the lattice.  Ingredients:

* multiplicativity (`cosetGRCoeff_mul_of_coprime`);
* the squaring bound at every prime power, `‖A^{cos}_{p^j}‖ ≤ D²/p^j` (`norm_cosetGRCoeff_primePow_le`);
* at an odd prime `p ∤ M det F` (so `p ∤ D`), the coset coefficient is the standard coefficient at `M`
  (`cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient`), so the level stability and finite-field
  count give `A^{cos}_{p^j} = 0` for `j ≥ 2` and `‖A^{cos}_p‖ ≤ 1/p²`;
* an abstract Euler-product assembly (`tsum_norm_le_of_multiplicative`), the smooth-number argument
  for a general multiplicative function.
Nothing is chosen.
-/

noncomputable section

open Finset Filter Topology

namespace PositiveDefiniteIntegralLattice

/-! ## The abstract Euler assembly -/

/-- Abstract Euler assembly: a multiplicative `f` with `‖f(p^j)‖ ≤ B/p^j` at every prime power, and with
`f(p^j) = 0` (`j ≥ 2`), `‖f(p)‖ ≤ 1/p²` at every prime `p ∤ X`, is absolutely summable with
`Σ ‖f‖ ≤ e² X^c` whenever `2(1 + B) ≤ 2^c`. -/
theorem tsum_norm_le_of_multiplicative (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → f (a * b) = f a * f b) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ p, p.Prime → ∀ j, ‖f (p ^ j)‖ ≤ B / (p : ℝ) ^ j) {X : ℕ} (hX : X ≠ 0)
    (hgood : ∀ p, p.Prime → ¬ p ∣ X → (∀ j, 2 ≤ j → f (p ^ j) = 0) ∧ ‖f p‖ ≤ 1 / (p : ℝ) ^ 2)
    {c : ℕ} (hc : 2 * (1 + B) ≤ 2 ^ c) :
    Summable (fun q ↦ ‖f q‖) ∧ ∑' q, ‖f q‖ ≤ Real.exp 2 * (X : ℝ) ^ c := by
  classical
  -- the geometric majorant at every prime
  have hgeo : ∀ p, p.Prime → ∀ j, ‖f (p ^ j)‖ ≤ (1 + B) * (1 / 2 : ℝ) ^ j := by
    intro p hp j
    refine (hbd p hp j).trans ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [div_eq_mul_inv, one_div, inv_pow]
    have h1 : ((p : ℝ) ^ j)⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 j)
    calc B * ((p : ℝ) ^ j)⁻¹ ≤ B * ((2 : ℝ) ^ j)⁻¹ := mul_le_mul_of_nonneg_left h1 hB
      _ ≤ (1 + B) * ((2 : ℝ) ^ j)⁻¹ := by gcongr; linarith
  have hsumloc : ∀ p, p.Prime → Summable fun j : ℕ ↦ ‖f (p ^ j)‖ := fun p hp ↦
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hgeo p hp) ((summable_geometric_two).mul_left _)
  have hloc : ∀ p, p.Prime → ∑' j : ℕ, ‖f (p ^ j)‖ ≤ 2 * (1 + B) := by
    intro p hp
    refine (Summable.tsum_le_tsum (hgeo p hp) (hsumloc p hp) ((summable_geometric_two).mul_left _)).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  have hlocgood : ∀ p, p.Prime → ¬ p ∣ X → ∑' j : ℕ, ‖f (p ^ j)‖ ≤ 1 + 1 / (p : ℝ) ^ 2 := by
    intro p hp hpX
    obtain ⟨hz, hp1⟩ := hgood p hp hpX
    have hsupp : ∀ j ∉ range 2, ‖f (p ^ j)‖ = 0 := by
      intro j hj
      rw [mem_range, not_lt] at hj
      rw [hz j hj, norm_zero]
    rw [tsum_eq_sum hsupp, sum_range_succ, sum_range_one, pow_zero, pow_one, hf1, norm_one]
    gcongr
  -- partial sums are bounded by the local product
  have hpart : ∀ N : ℕ, ∑ q ∈ range N, ‖f q‖ ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, ‖f (p ^ j)‖ := by
    intro N
    set g : ℕ → ℝ := fun q ↦ ‖f q‖ with hg
    have hg₁ : g 1 = 1 := by simp [hg, hf1]
    have hgmul : ∀ {a b : ℕ}, a.Coprime b → g (a * b) = g a * g b := fun h ↦ by
      simp only [hg, hmul h, norm_mul]
    have hgsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ ↦ ‖g (p ^ j)‖) := fun hp ↦ by
      simpa [hg] using hsumloc _ hp
    obtain ⟨-, hHas⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg₁ hgmul hgsum N
    have hg0 : g 0 = 0 := by simp [hg, hf0]
    have hsplit : ∑ q ∈ range N, g q = ∑ q ∈ (range N).subtype (· ∈ N.smoothNumbers), g q := by
      rw [Finset.sum_subtype_eq_sum_filter]
      symm
      refine Finset.sum_filter_of_ne fun q hq hne ↦ ?_
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h ↦ hne (by rw [h, hg0])
      exact Nat.mem_smoothNumbers_of_lt hq0 (mem_range.1 hq)
    change ∑ q ∈ range N, g q ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, g (p ^ j)
    rw [hsplit]
    exact sum_le_hasSum _ (fun _ _ ↦ norm_nonneg _) hHas
  -- the local product is at most `e² X^c`
  have hprod : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' j : ℕ, ‖f (p ^ j)‖ ≤ Real.exp 2 * (X : ℝ) ^ c := by
    intro N
    set S : ℕ → ℝ := fun p ↦ ∑' j : ℕ, ‖f (p ^ j)‖ with hSdef
    have hS0 : ∀ p, 0 ≤ S p := fun p ↦ tsum_nonneg fun _ ↦ norm_nonneg _
    change ∏ p ∈ N.primesBelow, S p ≤ _
    rw [← Finset.prod_filter_mul_prod_filter_not N.primesBelow (· ∣ X), mul_comm (Real.exp 2)]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun p _ ↦ hS0 p) (by positivity)
    · have hle : ∀ p ∈ N.primesBelow.filter (· ∣ X), S p ≤ (p : ℝ) ^ c := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primesBelow (mem_filter.1 hp).1
        refine (hloc p hpp).trans (hc.trans ?_)
        exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hpp.two_le) c
      refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
      rw [Finset.prod_pow]
      refine pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _) ?_ c
      have hsub : N.primesBelow.filter (· ∣ X) ⊆ X.primeFactors := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
        exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primesBelow hp1, hp2, hX⟩
      have hprodX : ∏ p ∈ N.primesBelow.filter (· ∣ X), p ≤ X :=
        (Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ ↦
          (Nat.prime_of_mem_primeFactors hp).one_lt.le).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hX) (Nat.prod_primeFactors_dvd X))
      have hcast := (Nat.cast_le (α := ℝ)).2 hprodX
      rwa [Nat.cast_prod] at hcast
    · have hle : ∀ p ∈ N.primesBelow.filter (fun p ↦ ¬ p ∣ X), S p ≤ Real.exp (1 / (p : ℝ) ^ 2) := by
        intro p hp
        obtain ⟨hp1, hpX⟩ := mem_filter.1 hp
        have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp1
        refine (hlocgood p hpp hpX).trans ?_
        have := Real.add_one_le_exp (1 / (p : ℝ) ^ 2)
        linarith
      refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
      rw [← Real.exp_sum]
      refine Real.exp_le_exp.2 ?_
      have hsub : N.primesBelow.filter (fun p ↦ ¬ p ∣ X) ⊆ Ioo 0 N := by
        intro p hp
        have hp1 := (mem_filter.1 hp).1
        exact mem_Ioo.2 ⟨(Nat.prime_of_mem_primesBelow hp1).pos, Nat.lt_of_mem_primesBelow hp1⟩
      calc ∑ p ∈ N.primesBelow.filter (fun p ↦ ¬ p ∣ X), 1 / (p : ℝ) ^ 2
          ≤ ∑ i ∈ Ioo 0 N, ((i : ℝ) ^ 2)⁻¹ := by
            simp_rw [one_div]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
        _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 N
        _ = 2 := by norm_num
  have hbound : ∀ N : ℕ, ∑ q ∈ range N, ‖f q‖ ≤ Real.exp 2 * (X : ℝ) ^ c :=
    fun N ↦ (hpart N).trans (hprod N)
  exact ⟨summable_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound⟩

/-! ## The coset application -/

variable (L : PositiveDefiniteIntegralLattice 4)

theorem cosetGRCoeff_zero (u : Fin 4 → ℤ) (lam : ℤ) : L.cosetGRCoeff u lam 0 = 0 := by
  simp [cosetGRCoeff]

/-- The grouped estimate for every coset (4.3): there are `K > 0` and `c₀` (depending only on the lattice)
such that for every `u`, `λ` with nonzero target `M = q(adj(S) u) + D²λ`,
`Σ_c ‖A^{cos}_c(u, λ)‖ < ∞` and `Σ_c ‖A^{cos}_c(u, λ)‖ ≤ K |M|^{c₀}`. -/
theorem exists_summable_norm_cosetGRCoeff_le :
    ∃ (K : ℝ) (c₀ : ℕ), 0 < K ∧ ∀ (u : Fin 4 → ℤ) (lam : ℤ), L.cosetStandardTarget u lam ≠ 0 →
      Summable (fun c ↦ ‖L.cosetGRCoeff u lam c‖) ∧
        ∑' c, ‖L.cosetGRCoeff u lam c‖ ≤ K * ((L.cosetStandardTarget u lam).natAbs : ℝ) ^ c₀ := by
  set B : ℝ := (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  obtain ⟨c₀, hc₀⟩ := pow_unbounded_of_one_lt (2 * (1 + B)) (by norm_num : (1 : ℝ) < 2)
  have hdetF : L.pairingMatrix.det.natAbs ≠ 0 := Int.natAbs_ne_zero.2 L.pairingMatrix_det_ne_zero
  refine ⟨Real.exp 2 * ((2 * L.pairingMatrix.det.natAbs : ℕ) : ℝ) ^ c₀, c₀, by positivity,
    fun u lam hM ↦ ?_⟩
  set M := L.cosetStandardTarget u lam with hMdef
  set X : ℕ := 2 * M.natAbs * L.pairingMatrix.det.natAbs with hXdef
  have hX : X ≠ 0 := by
    rw [hXdef]
    have : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hM
    positivity
  have hgood : ∀ p, p.Prime → ¬ p ∣ X →
      (∀ j, 2 ≤ j → L.cosetGRCoeff u lam (p ^ j) = 0) ∧
        ‖L.cosetGRCoeff u lam p‖ ≤ 1 / (p : ℝ) ^ 2 := by
    intro p hp hpX
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hpX (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl 2) _) _)
    have hpM : ¬ (p : ℤ) ∣ M := fun h ↦ hpX
      (Dvd.dvd.mul_right (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _) _)
    have hpdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det := fun h ↦ hpX
      (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
    have hpD : ¬ p ∣ L.polarGramMatrix.det.natAbs := by
      intro h
      have h' : (p : ℤ) ∣ L.polarGramMatrix.det := Int.natCast_dvd.2 h
      have hdisc : L.polarGramMatrix.det = 2 ^ 4 * L.pairingMatrix.det := L.polarDeterminant_eq_two_pow_mul_pairingDeterminant
      rw [hdisc] at h'
      rcases (Int.Prime.dvd_mul' hp h') with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (Nat.Prime.dvd_of_dvd_pow hp (Int.natCast_dvd_natCast.1 (by exact_mod_cast h2))))
      · exact hpdet h2
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · rw [L.cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient u lam hp hpD j]
      exact L.gaussRamanujanCoefficient_primePow_eq_zero hp hp2 hpM hj
    · have h := L.cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient u lam hp hpD 1
      rw [pow_one] at h
      rw [h]
      exact L.norm_gaussRamanujanCoefficient_prime_le (by norm_num) hp hp2 hpM hpdet
  obtain ⟨hsum, hle⟩ := tsum_norm_le_of_multiplicative (L.cosetGRCoeff u lam)
    (L.cosetGRCoeff_zero u lam) (L.cosetGRCoeff_one u lam)
    (fun h ↦ L.cosetGRCoeff_mul_of_coprime u lam h) hB
    (fun p hp j ↦ L.norm_cosetGRCoeff_primePow_le u lam hp j) hX hgood hc₀.le
  refine ⟨hsum, hle.trans (le_of_eq ?_)⟩
  rw [hXdef]
  push_cast
  ring

/-! ## The sharp form: square-root growth -/

theorem one_le_prod_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact one_le_mul_of_one_le_of_one_le (h a (mem_insert_self a s))
      (ih fun i hi ↦ h i (mem_insert_of_mem hi))

theorem prod_le_prod_of_subset_of_one_le_real {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    (hst : s ⊆ t) (f : ι → ℝ) (h : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := one_le_prod_real _ _ fun i hi ↦ h i (mem_sdiff.1 hi).1
  have h0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi ↦ le_trans zero_le_one (h i (hst hi))
  exact le_mul_of_one_le_left h0 h1

/-- `Π_{p ∣ M} p/(p-1) ≤ √(2M)`. -/
theorem prod_primeFactors_div_sub_one_le_sqrt {M : ℕ} (hM : M ≠ 0) :
    ∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ≤ Real.sqrt (2 * M) := by
  classical
  have hsq : (∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) ^ 2 ≤ 2 * M := by
    rw [← Finset.prod_pow]
    have hloc : ∀ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤
        (p : ℝ) * (if p = 2 then 2 else 1) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [div_pow, div_le_iff₀ (by positivity)]
      split_ifs with h
      · subst h; norm_num
      · have hp3 : (3 : ℝ) ≤ p := by
          have : 3 ≤ p := by
            rcases hpp.eq_two_or_odd' with h2 | hodd
            · exact absurd h2 h
            · have := hpp.two_le; obtain ⟨k, hk⟩ := hodd; omega
          exact_mod_cast this
        nlinarith
    refine (Finset.prod_le_prod (fun p _ ↦ by positivity) hloc).trans ?_
    rw [Finset.prod_mul_distrib]
    have h2 : ∏ p ∈ M.primeFactors, (if p = 2 then (2 : ℝ) else 1) ≤ 2 := by
      rw [Finset.prod_ite_eq' M.primeFactors 2 (fun _ ↦ (2 : ℝ))]
      split_ifs <;> norm_num
    have hprod : ∏ p ∈ M.primeFactors, (p : ℝ) ≤ M := by
      have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M)
      have h' := (Nat.cast_le (α := ℝ)).2 h
      rwa [Nat.cast_prod] at h'
    have hprod0 : 0 ≤ ∏ p ∈ M.primeFactors, (p : ℝ) := Finset.prod_nonneg fun _ _ ↦ by positivity
    calc (∏ p ∈ M.primeFactors, (p : ℝ)) * ∏ p ∈ M.primeFactors, (if p = 2 then (2 : ℝ) else 1)
        ≤ (M : ℝ) * 2 := mul_le_mul hprod h2 (Finset.prod_nonneg fun _ _ ↦ by split_ifs <;> norm_num)
          (by positivity)
      _ = 2 * M := by ring
  have hnn : 0 ≤ ∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    refine Finset.prod_nonneg fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (by linarith) (by linarith)
  calc ∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      = |∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))| := (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (2 * M) := Real.abs_le_sqrt hsq

/-- Sharp abstract Euler assembly: with a bad set `p ∣ D₀`, `‖f(p^j)‖ ≤ 1/p^j` at `p ∤ D₀`, and the good-prime
behaviour at `p ∤ D₀ M₀`, `Σ ‖f‖ ≤ (2(1+B))^{ω(D₀)} √(2M₀) e²`. -/
theorem tsum_norm_le_sqrt_of_multiplicative (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → f (a * b) = f a * f b) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ p, p.Prime → ∀ j, ‖f (p ^ j)‖ ≤ B / (p : ℝ) ^ j) {D₀ M₀ : ℕ} (hD₀ : D₀ ≠ 0) (hM₀ : M₀ ≠ 0)
    (hcop : ∀ p, p.Prime → ¬ p ∣ D₀ → ∀ j, ‖f (p ^ j)‖ ≤ 1 / (p : ℝ) ^ j)
    (hgood : ∀ p, p.Prime → ¬ p ∣ D₀ → ¬ p ∣ M₀ →
      (∀ j, 2 ≤ j → f (p ^ j) = 0) ∧ ‖f p‖ ≤ 1 / (p : ℝ) ^ 2) :
    Summable (fun q ↦ ‖f q‖) ∧
      ∑' q, ‖f q‖ ≤ (2 * (1 + B)) ^ D₀.primeFactors.card * Real.sqrt (2 * M₀) * Real.exp 2 := by
  classical
  have hgeo : ∀ p, p.Prime → ∀ j, ‖f (p ^ j)‖ ≤ (1 + B) * (1 / 2 : ℝ) ^ j := by
    intro p hp j
    refine (hbd p hp j).trans ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [div_eq_mul_inv, one_div, inv_pow]
    have h1 : ((p : ℝ) ^ j)⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 j)
    calc B * ((p : ℝ) ^ j)⁻¹ ≤ B * ((2 : ℝ) ^ j)⁻¹ := mul_le_mul_of_nonneg_left h1 hB
      _ ≤ (1 + B) * ((2 : ℝ) ^ j)⁻¹ := by gcongr; linarith
  have hsumloc : ∀ p, p.Prime → Summable fun j : ℕ ↦ ‖f (p ^ j)‖ := fun p hp ↦
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hgeo p hp) ((summable_geometric_two).mul_left _)
  have hloc : ∀ p, p.Prime → ∑' j : ℕ, ‖f (p ^ j)‖ ≤ 2 * (1 + B) := by
    intro p hp
    refine (Summable.tsum_le_tsum (hgeo p hp) (hsumloc p hp) ((summable_geometric_two).mul_left _)).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  have hlocD : ∀ p, p.Prime → ¬ p ∣ D₀ → ∑' j : ℕ, ‖f (p ^ j)‖ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp hpD
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    have hg : ∀ j, ‖f (p ^ j)‖ ≤ (1 / (p : ℝ)) ^ j := fun j ↦ by
      rw [div_pow, one_pow]; exact hcop p hp hpD j
    refine (Summable.tsum_le_tsum hg (hsumloc p hp) (summable_geometric_of_lt_one hr0 hr1)).trans
      (le_of_eq ?_)
    rw [tsum_geometric_of_lt_one hr0 hr1]
    field_simp
  have hlocgood : ∀ p, p.Prime → ¬ p ∣ D₀ → ¬ p ∣ M₀ →
      ∑' j : ℕ, ‖f (p ^ j)‖ ≤ 1 + 1 / (p : ℝ) ^ 2 := by
    intro p hp hpD hpM
    obtain ⟨hz, hp1⟩ := hgood p hp hpD hpM
    have hsupp : ∀ j ∉ range 2, ‖f (p ^ j)‖ = 0 := by
      intro j hj
      rw [mem_range, not_lt] at hj
      rw [hz j hj, norm_zero]
    rw [tsum_eq_sum hsupp, sum_range_succ, sum_range_one, pow_zero, pow_one, hf1, norm_one]
    gcongr
  have hpart : ∀ N : ℕ, ∑ q ∈ range N, ‖f q‖ ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, ‖f (p ^ j)‖ := by
    intro N
    set g : ℕ → ℝ := fun q ↦ ‖f q‖ with hg
    have hg₁ : g 1 = 1 := by simp [hg, hf1]
    have hgmul : ∀ {a b : ℕ}, a.Coprime b → g (a * b) = g a * g b := fun h ↦ by
      simp only [hg, hmul h, norm_mul]
    have hgsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ ↦ ‖g (p ^ j)‖) := fun hp ↦ by
      simpa [hg] using hsumloc _ hp
    obtain ⟨-, hHas⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg₁ hgmul hgsum N
    have hg0 : g 0 = 0 := by simp [hg, hf0]
    have hsplit : ∑ q ∈ range N, g q = ∑ q ∈ (range N).subtype (· ∈ N.smoothNumbers), g q := by
      rw [Finset.sum_subtype_eq_sum_filter]
      symm
      refine Finset.sum_filter_of_ne fun q hq hne ↦ ?_
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h ↦ hne (by rw [h, hg0])
      exact Nat.mem_smoothNumbers_of_lt hq0 (mem_range.1 hq)
    change ∑ q ∈ range N, g q ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, g (p ^ j)
    rw [hsplit]
    exact sum_le_hasSum _ (fun _ _ ↦ norm_nonneg _) hHas
  have hprod : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' j : ℕ, ‖f (p ^ j)‖ ≤
      (2 * (1 + B)) ^ D₀.primeFactors.card * Real.sqrt (2 * M₀) * Real.exp 2 := by
    intro N
    set S : ℕ → ℝ := fun p ↦ ∑' j : ℕ, ‖f (p ^ j)‖ with hSdef
    have hS0 : ∀ p, 0 ≤ S p := fun p ↦ tsum_nonneg fun _ ↦ norm_nonneg _
    change ∏ p ∈ N.primesBelow, S p ≤ _
    rw [← Finset.prod_filter_mul_prod_filter_not N.primesBelow (· ∣ D₀),
      ← Finset.prod_filter_mul_prod_filter_not (N.primesBelow.filter fun p ↦ ¬ p ∣ D₀) (· ∣ M₀),
      ← mul_assoc]
    have hB1 : (1 : ℝ) ≤ 2 * (1 + B) := by linarith
    refine mul_le_mul (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun p _ ↦ hS0 p) (by positivity)) ?_
      (Finset.prod_nonneg fun p _ ↦ hS0 p) (by positivity)
    · -- the bad primes
      have hle : ∀ p ∈ N.primesBelow.filter (· ∣ D₀), S p ≤ 2 * (1 + B) := fun p hp ↦
        hloc p (Nat.prime_of_mem_primesBelow (mem_filter.1 hp).1)
      refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
      rw [Finset.prod_const]
      refine pow_le_pow_right₀ hB1 (Finset.card_le_card fun p hp ↦ ?_)
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primesBelow hp1, hp2, hD₀⟩
    · -- the primes dividing `M₀` only
      have hle : ∀ p ∈ (N.primesBelow.filter fun p ↦ ¬ p ∣ D₀).filter (· ∣ M₀),
          S p ≤ (p : ℝ) / ((p : ℝ) - 1) := by
        intro p hp
        obtain ⟨hp1, -⟩ := mem_filter.1 hp
        obtain ⟨hp0, hpD⟩ := mem_filter.1 hp1
        exact hlocD p (Nat.prime_of_mem_primesBelow hp0) hpD
      refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
      refine le_trans ?_ (prod_primeFactors_div_sub_one_le_sqrt hM₀)
      refine prod_le_prod_of_subset_of_one_le_real (fun p hp ↦ ?_) _ fun p hp ↦ ?_
      · obtain ⟨hp1, hpM⟩ := mem_filter.1 hp
        exact Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primesBelow (mem_filter.1 hp1).1, hpM, hM₀⟩
      · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        rw [le_div_iff₀ (by linarith)]
        linarith
    · -- the good primes
      have hle : ∀ p ∈ (N.primesBelow.filter fun p ↦ ¬ p ∣ D₀).filter (fun p ↦ ¬ p ∣ M₀),
          S p ≤ Real.exp (1 / (p : ℝ) ^ 2) := by
        intro p hp
        obtain ⟨hp1, hpM⟩ := mem_filter.1 hp
        obtain ⟨hp0, hpD⟩ := mem_filter.1 hp1
        refine (hlocgood p (Nat.prime_of_mem_primesBelow hp0) hpD hpM).trans ?_
        have := Real.add_one_le_exp (1 / (p : ℝ) ^ 2)
        linarith
      refine (Finset.prod_le_prod (fun p _ ↦ hS0 p) hle).trans ?_
      rw [← Real.exp_sum]
      refine Real.exp_le_exp.2 ?_
      have hsub : (N.primesBelow.filter fun p ↦ ¬ p ∣ D₀).filter (fun p ↦ ¬ p ∣ M₀) ⊆ Ioo 0 N := by
        intro p hp
        have hp1 := (mem_filter.1 (mem_filter.1 hp).1).1
        exact mem_Ioo.2 ⟨(Nat.prime_of_mem_primesBelow hp1).pos, Nat.lt_of_mem_primesBelow hp1⟩
      calc ∑ p ∈ (N.primesBelow.filter fun p ↦ ¬ p ∣ D₀).filter (fun p ↦ ¬ p ∣ M₀), 1 / (p : ℝ) ^ 2
          ≤ ∑ i ∈ Ioo 0 N, ((i : ℝ) ^ 2)⁻¹ := by
            simp_rw [one_div]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
        _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 N
        _ = 2 := by norm_num
  have hbound : ∀ N : ℕ, ∑ q ∈ range N, ‖f q‖ ≤
      (2 * (1 + B)) ^ D₀.primeFactors.card * Real.sqrt (2 * M₀) * Real.exp 2 :=
    fun N ↦ (hpart N).trans (hprod N)
  exact ⟨summable_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _) hbound⟩

/-- The sharp grouped estimate for every coset: `Σ_c ‖A^{cos}_c(u, λ)‖ ≤ K √|M|` for nonzero
`M = q(adj(S) u) + D²λ`, with `K` depending only on the lattice. -/
theorem exists_summable_norm_cosetGRCoeff_le_sqrt :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Fin 4 → ℤ) (lam : ℤ), L.cosetStandardTarget u lam ≠ 0 →
      Summable (fun c ↦ ‖L.cosetGRCoeff u lam c‖) ∧
        ∑' c, ‖L.cosetGRCoeff u lam c‖ ≤
          K * Real.sqrt ((L.cosetStandardTarget u lam).natAbs : ℝ) := by
  set B : ℝ := (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  set D₀ := L.polarGramMatrix.det.natAbs with hD₀
  refine ⟨(2 * (1 + B)) ^ D₀.primeFactors.card * Real.sqrt 2 * Real.exp 2, by positivity,
    fun u lam hM ↦ ?_⟩
  set M := L.cosetStandardTarget u lam with hMdef
  have hM₀ : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hM
  have h2D : 2 ∣ D₀ := by
    have hdisc : L.polarGramMatrix.det = 2 ^ 4 * L.pairingMatrix.det := L.polarDeterminant_eq_two_pow_mul_pairingDeterminant
    rw [hD₀, hdisc, Int.natAbs_mul]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hdetD : L.pairingMatrix.det.natAbs ∣ D₀ := by
    have hdisc : L.polarGramMatrix.det = 2 ^ 4 * L.pairingMatrix.det := L.polarDeterminant_eq_two_pow_mul_pairingDeterminant
    rw [hD₀, hdisc, Int.natAbs_mul]
    exact Dvd.intro_left _ rfl
  have hgood : ∀ p, p.Prime → ¬ p ∣ D₀ → ¬ p ∣ M.natAbs →
      (∀ j, 2 ≤ j → L.cosetGRCoeff u lam (p ^ j) = 0) ∧
        ‖L.cosetGRCoeff u lam p‖ ≤ 1 / (p : ℝ) ^ 2 := by
    intro p hp hpD hpM
    have hp2 : p ≠ 2 := by rintro rfl; exact hpD h2D
    have hpM' : ¬ (p : ℤ) ∣ M := fun h ↦ hpM (Int.natCast_dvd.1 h)
    have hpdet : ¬ (p : ℤ) ∣ L.pairingMatrix.det := fun h ↦ hpD ((Int.natCast_dvd.1 h).trans hdetD)
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · rw [L.cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient u lam hp hpD j]
      exact L.gaussRamanujanCoefficient_primePow_eq_zero hp hp2 hpM' hj
    · have h := L.cosetGRCoeff_primePow_eq_gaussRamanujanCoefficient u lam hp hpD 1
      rw [pow_one] at h
      rw [h]
      exact L.norm_gaussRamanujanCoefficient_prime_le (by norm_num) hp hp2 hpM' hpdet
  obtain ⟨hsum, hle⟩ := tsum_norm_le_sqrt_of_multiplicative (L.cosetGRCoeff u lam)
    (L.cosetGRCoeff_zero u lam) (L.cosetGRCoeff_one u lam)
    (fun h ↦ L.cosetGRCoeff_mul_of_coprime u lam h) hB
    (fun p hp j ↦ L.norm_cosetGRCoeff_primePow_le u lam hp j)
    (Int.natAbs_ne_zero.2 L.polarGramMatrix_det_ne_zero) hM₀
    (fun p hp hpD j ↦ L.norm_cosetGRCoeff_primePow_le_of_not_dvd u lam hp hpD j) hgood
  refine ⟨hsum, hle.trans (le_of_eq ?_)⟩
  rw [Real.sqrt_mul (by norm_num)]
  ring

end PositiveDefiniteIntegralLattice
