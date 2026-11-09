import SMSFormula.FiniteOrthogonalGroupGoodPrimeOddPositivity

/-!
# Positivity of the non-endpoint even good-prime product

This module proves positivity of the cutoff-removed quadratic Dirichlet
`L`-tail in the absolute-convergence half-plane.  It keeps real-valuedness,
nonnegativity, and nonvanishing as separate inputs before deriving strict
positivity.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- In the active even-rank branch, every value of the chosen quadratic
Dirichlet character is the complex embedding of a real number. -/
lemma goodPrimeEvenDirichletCharacter_apply_exists_ofReal
    (L : PositiveDefiniteIntegralLattice n) (s m : ℕ) (hn : n = 2 * s) :
    ∃ r : ℝ, goodPrimeEvenDirichletCharacter L s m = (r : ℂ) := by
  rw [goodPrimeEvenDirichletCharacter, dif_pos hn]
  let q := goodPrimeEvenDirichletModulus L s
  by_cases hm : IsUnit (m : ZMod q)
  · let u : (ZMod q)ˣ := hm.unit
    refine ⟨jacobiSym (goodPrimeEvenCharacterDiscriminant L s)
      (u : ZMod q).val, ?_⟩
    change goodPrimeEvenJacobiDirichletCharacter L s
        (m : ZMod q) = _
    rw [show (m : ZMod q) = (u : ZMod q) by rfl,
      goodPrimeEvenJacobiDirichletCharacter_apply_unit]
  · refine ⟨0, ?_⟩
    change goodPrimeEvenJacobiDirichletCharacter L s
        (m : ZMod q) = _
    rw [MulChar.map_nonunit _ hm]
    norm_num

/-- One complex quadratic Dirichlet Euler factor is a strictly positive real
number in the half-plane used by the even mass formula. -/
lemma goodPrimeEvenDirichletEulerFactor_exists_pos_real
    (L : PositiveDefiniteIntegralLattice n) (s p : ℕ) (hs : 1 < s) (hp : p.Prime)
    (hn : n = 2 * s) :
    ∃ r : ℝ, 0 < r ∧
      (1 - goodPrimeEvenDirichletCharacter L s p *
        (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹ = (r : ℂ) := by
  rcases goodPrimeEvenDirichletCharacter_apply_exists_ofReal
      L s p hn with ⟨c, hc⟩
  let a : ℝ := (p : ℝ) ^ (-(s : ℝ))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsR : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hs)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_lt : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR
      (neg_neg_iff_pos.mpr hsR)
  have hc_norm :=
    (goodPrimeEvenDirichletCharacter L s).norm_le_one p
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at hc_norm
  have hc_le : c ≤ 1 := (le_abs_self c).trans hc_norm
  have hbase : 0 < 1 - c * a := by
    rw [sub_pos]
    have hca : c * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hc_le ha_pos.le
    exact hca.trans_lt ha_lt
  refine ⟨(1 - c * a)⁻¹, inv_pos.mpr hbase, ?_⟩
  have hpow : ((a : ℝ) : ℂ) = (p : ℂ) ^ (-((s : ℕ) : ℂ)) := by
    dsimp [a]
    rw [Complex.ofReal_cpow]
    · congr 1
      norm_num
    · positivity
  rw [hc, ← hpow]
  norm_cast

/-- Every finite prime prefix of the quadratic Dirichlet Euler product is a
strictly positive real number. -/
lemma goodPrimeEvenDirichletEulerProduct_exists_pos_real
    (L : PositiveDefiniteIntegralLattice n) (s N : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    ∃ r : ℝ, 0 < r ∧
      ((N + 1).primesBelow.prod fun p =>
        (1 - goodPrimeEvenDirichletCharacter L s p *
          (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹) = (r : ℂ) := by
  classical
  have aux : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∃ r : ℝ, 0 < r ∧
        (S.prod fun p =>
          (1 - goodPrimeEvenDirichletCharacter L s p *
            (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹) = (r : ℂ) := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert p S hpS ih =>
        rcases goodPrimeEvenDirichletEulerFactor_exists_pos_real
            L s p hs (hS p (Finset.mem_insert_self p S)) hn with ⟨a, ha, hpa⟩
        rcases ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) with
          ⟨b, hb, hSb⟩
        refine ⟨a * b, mul_pos ha hb, ?_⟩
        rw [Finset.prod_insert hpS, hpa, hSb, Complex.ofReal_mul]
  exact aux (N + 1).primesBelow fun p hp => Nat.prime_of_mem_primesBelow hp

/-- The quadratic Dirichlet `L`-series value is a strictly positive real
number in the half-plane `1 < s`. -/
lemma goodPrimeEvenDirichletLSeries_exists_pos_real
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    ∃ r : ℝ, 0 < r ∧
      LSeries (fun m : ℕ =>
        (goodPrimeEvenDirichletCharacter L s m : ℂ))
        ((s : ℕ) : ℂ) = (r : ℂ) := by
  let χ := goodPrimeEvenDirichletCharacter L s
  let z : ℂ := ((s : ℕ) : ℂ)
  have hz : 1 < z.re := by
    dsimp [z]
    norm_num
    exact_mod_cast hs
  have hprod := (DirichletCharacter.LSeries_eulerProduct (χ := χ) hz).comp
    (Filter.tendsto_add_atTop_nat 1)
  let F : ℕ → ℂ := fun N => (N + 1).primesBelow.prod fun p =>
    (1 - χ p * (p : ℂ) ^ (-z))⁻¹
  have hprod' : Filter.Tendsto F Filter.atTop
      (nhds (LSeries (fun m : ℕ => (χ m : ℂ)) z)) := by
    simpa [F, χ, z] using hprod
  have hre := Complex.continuous_re.tendsto _ |>.comp hprod'
  have hre_nonneg :
      0 ≤ (LSeries (fun m : ℕ => (χ m : ℂ)) z).re := by
    apply ge_of_tendsto' hre
    intro N
    rcases goodPrimeEvenDirichletEulerProduct_exists_pos_real
        L s N hs hn with ⟨r, hr, hFr⟩
    change 0 ≤ (F N).re
    rw [show F N = (r : ℂ) by simpa [F, χ, z] using hFr]
    simpa using hr.le
  have him := Complex.continuous_im.tendsto _ |>.comp hprod'
  have him_zero :
      (LSeries (fun m : ℕ => (χ m : ℂ)) z).im = 0 := by
    have him' : Filter.Tendsto (fun N => (F N).im) Filter.atTop (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with N
      rcases goodPrimeEvenDirichletEulerProduct_exists_pos_real
          L s N hs hn with ⟨r, _hr, hFr⟩
      have hFN : F N = (r : ℂ) := by
        simpa [F, χ, z] using hFr
      rw [hFN]
      simp
    exact tendsto_nhds_unique him him'
  have hne : LSeries (fun m : ℕ => (χ m : ℂ)) z ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hz
  have hre_ne : (LSeries (fun m : ℕ => (χ m : ℂ)) z).re ≠ 0 := by
    intro hre_zero
    apply hne
    apply Complex.ext
    · simpa using hre_zero
    · simpa using him_zero
  have hpos : 0 < (LSeries (fun m : ℕ => (χ m : ℂ)) z).re :=
    lt_of_le_of_ne hre_nonneg (Ne.symm hre_ne)
  have hreal : LSeries (fun m : ℕ => (χ m : ℂ)) z =
      ((LSeries (fun m : ℕ => (χ m : ℂ)) z).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him_zero
  refine ⟨(LSeries (fun m : ℕ => (χ m : ℂ)) z).re, ?_, ?_⟩
  · simpa [χ, z] using hpos
  · simpa [χ, z] using hreal

/-- The cutoff-removed quadratic Dirichlet tail has positive real part in the
absolute-convergence half-plane. -/
lemma goodPrimeEvenDirichletTailFactorOfCharacter_pos
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    0 < goodPrimeEvenDirichletTailFactorOfCharacter L N s := by
  rcases goodPrimeEvenDirichletLSeries_exists_pos_real
      L s hs hn with ⟨a, ha, hLa⟩
  rcases goodPrimeEvenDirichletEulerProduct_exists_pos_real
      L s N hs hn with ⟨b, hb, hPb⟩
  rw [goodPrimeEvenDirichletTailFactorOfCharacter,
    goodPrimeEvenDirichletComplexTailFactor]
  rw [hLa, hPb, ← Complex.ofReal_div]
  simpa using div_pos ha hb

/-- The explicit real expression used as the non-endpoint even-rank mass
inverse-product limit is strictly positive. -/
lemma evenRankOrdinaryMassProductExpression_pos
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hs : 1 < s) (hn : n = 2 * s) :
    0 < massPartialPrimeInverseProduct L N *
      ((Finset.Icc 1 (s - 1)).prod
        (fun j => goodPrimeEulerCoreZetaTailFactor N j) *
          goodPrimeEvenDirichletTailFactorOfCharacter L N s) := by
  exact mul_pos
    (massPartialPrimeInverseProduct_pos L N)
    (mul_pos
      (goodPrimeOddZetaTailProduct_pos N s)
      (goodPrimeEvenDirichletTailFactorOfCharacter_pos
        L N s hs hn))

end PositiveDefiniteIntegralLattice
