import SMSFormula.RationalAdeleFiniteLocalReplacementAssembly
import SMSFormula.RationalAdeleFiniteLocalReplacementGlueRatio
import SMSFormula.RationalAdeleSingularSeriesLocalDensity

/-!
# The finite-place replacement lemma in rank four, as a tube limit

Above rank four the replacement lemma reads `d_fin(1_{U_R})(M) = κ · d_fin(1_Ẑ)(M)` for the
Fourier finite value density.  In rank four the Bruhat coefficient is not integrable, so the finite
value density is the `k!`-TUBE limit (`tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity`).
This file gives the replacement lemma in that form, in every rank `≥ 4`:

* `tendsto_factorial_mul_restrictedCongruenceIntegral_of_eventually_card_eq`: if the restricted
  residue counts at `k!` are eventually `κ` times the unrestricted ones, the tube masses of `1_{U_R}`
  converge to `κ · ∏'_p δ_p(M)`;
* `tendsto_factorial_mul_localRestrictionCongruenceIntegral`: for the CRT product of supplied
  local residue sets with supplied local count ratios `gR_p/gF_p`, the tube masses converge to
  `(∏ gR / ∏ gF) · ∏'_p δ_p(M)`;
* `exists_tendsto_factorial_mul_localRestrictionCongruenceIntegral`: the same with no supplied masses
  (glue-ratio existence), when `M` is integrally represented at every prime of `P`.

Only the rank-free congruence-measure and count identities are used.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
/-- The replacement lemma as a tube limit, counting form, rank at least four. -/
theorem tendsto_factorial_mul_restrictedCongruenceIntegral_of_eventually_card_eq
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) (N₀ : ℕ) [NeZero N₀]
    (R : Set (Fin (n + 1) → ZMod N₀)) {M : ℤ} (hM : M ≠ 0) (κ : ℂ)
    (h : ∀ᶠ k : ℕ in atTop, ∀ hdvd : N₀ ∣ Nat.factorial k,
      (Nat.card {z : Fin (n + 1) → ZMod (Nat.factorial k) //
          L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈ R} : ℂ) =
        κ * (Nat.card {z : Fin (n + 1) → ZMod (Nat.factorial k) //
          L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
          (fun i ↦ ZMod.castHom hdvd (ZMod N₀) (z i)) ∈
            (Set.univ : Set (Fin (n + 1) → ZMod N₀))} : ℂ)) :
    Tendsto (fun k : ℕ ↦ ((Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) N₀ R x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 (κ * ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ))) := by
  have hfull := L.tendsto_factorial_mul_congruenceIntegral_tprod_localResidueDensity hn hM
  refine (tendsto_const_nhds.mul hfull).congr' ?_
  filter_upwards [h, Filter.eventually_ge_atTop N₀] with k hk hkN
  have hdvd : N₀ ∣ Nat.factorial k := Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne N₀)) hkN
  have huniv := L.measure_restrictedCongruenceSet_eq_residueCount (Nat.factorial_ne_zero k) hdvd
    Set.univ M
  rw [residueRestrictedIndicator_univ N₀] at huniv
  rw [huniv, L.measure_restrictedCongruenceSet_eq_residueCount (Nat.factorial_ne_zero k) hdvd R M,
    hk hdvd]
  ring

set_option maxHeartbeats 2000000 in
/-- The finite-place replacement lemma in rank at least four, as a tube limit: for the CRT
product `R` of supplied local residue sets and supplied local count ratios, the `k!`-tube masses of
`1_{U_R}` converge to `(∏_P gR_p / ∏_P gF_p) · ∏'_p δ_p(M)`. -/
theorem tendsto_factorial_mul_localRestrictionCongruenceIntegral (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    Tendsto (fun k : ℕ ↦ ((Nat.factorial k : ℕ) : ℂ) *
        ∫ x : Fin (n + 1) → RationalFiniteAdele,
          residueRestrictedIndicator (n + 1) (localRestrictionLevel P e)
              (localRestrictionSet P e R) x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
      atTop (𝓝 ((((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
        ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ))) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hPF0 : (∏ p ∈ P, gF p) ≠ 0 := Finset.prod_ne_zero_iff.2 hgF0
  have hPFt : (∏ p ∈ P, gF p) ≠ ⊤ := ENNReal.prod_ne_top hgFt
  refine L.tendsto_factorial_mul_restrictedCongruenceIntegral_of_eventually_card_eq hn _ _ hM _ ?_
  filter_upwards [L.eventually_restrictedResidueCount_mul_prod_eq M P e R hP gF gR hloc hFne]
    with k hk hdvd
  have hcardR : Nat.card {z : Fin (n + 1) → ZMod (Nat.factorial k) //
      L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
      (fun i ↦ ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) ∈
        localRestrictionSet P e R} = L.restrictedResidueCount M P e R (Nat.factorial k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦
      and_congr_right' (castHom_mem_localRestrictionSet_iff P e R hdvd z))
  have hcardF : Nat.card {z : Fin (n + 1) → ZMod (Nat.factorial k) //
      L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
      (fun i ↦ ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) ∈
        (Set.univ : Set (Fin (n + 1) → ZMod (localRestrictionLevel P e)))} =
      L.fullResidueCount M (Nat.factorial k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, Set.mem_univ _⟩⟩)
  rw [hcardR, hcardF]
  have hdiv : (L.restrictedResidueCount M P e R (Nat.factorial k) : ℝ≥0∞) =
      (L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * ((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p) := by
    rw [← mul_div_assoc, ENNReal.eq_div_iff hPF0 hPFt, mul_comm, hk]
  have hreal := congrArg ENNReal.toReal hdiv
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  have hc : ((L.restrictedResidueCount M P e R (Nat.factorial k) : ℕ) : ℂ) =
      (((L.restrictedResidueCount M P e R (Nat.factorial k) : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [hc, hreal]
  push_cast
  ring

/-- The replacement lemma in rank at least four with no supplied masses: if `M ≠ 0` is integrally
represented at every prime of `P`, there exist local masses `gF_p ∈ (0, ∞)`, `gR_p` (eventual
count ratios) such that the `k!`-tube masses of `1_{U_R}` converge to `(∏ gR/∏ gF) · ∏'_p δ_p(M)`. -/
theorem exists_tendsto_factorial_mul_localRestrictionCongruenceIntegral
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (hrep : ∀ p (hp : p ∈ P), haveI : Fact p.Prime := ⟨(hP p hp).1⟩;
      ∃ u : Fin (n + 1) → ℚ_[p], ‖u‖ ≤ 1 ∧
        ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
          (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' u =
            (((M : ℤ) : ℤ_[p]) : ℚ_[p])) :
    ∃ gF gR : ℕ → ℝ≥0∞, (∀ p ∈ P, gF p ≠ 0) ∧ (∀ p ∈ P, gF p ≠ ⊤) ∧
      (∀ p ∈ P, ∀ᶠ v : ℕ in atTop, (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) ∧
      haveI : NeZero (localRestrictionLevel P e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
      Tendsto (fun k : ℕ ↦ ((Nat.factorial k : ℕ) : ℂ) *
          ∫ x : Fin (n + 1) → RationalFiniteAdele,
            residueRestrictedIndicator (n + 1) (localRestrictionLevel P e)
                (localRestrictionSet P e R) x *
              rationalFiniteAdeleIntegralIndicator
                (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                  (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                    algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
            ∂rationalFiniteAdeleCoordinateAddHaarMeasure (n + 1))
        atTop (𝓝 ((((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
          ((∏' p : Nat.Primes, L.localResidueDensity M p : ℝ) : ℂ))) := by
  obtain ⟨gF, gR, h0, ht, hloc, hFne⟩ := L.exists_localGlueRatio_family M hM P e R hP hrep
  exact ⟨gF, gR, h0, ht, hloc, hFne,
    L.tendsto_factorial_mul_localRestrictionCongruenceIntegral hn hM P e R hP gF gR h0 ht hloc hFne⟩

end PositiveDefiniteIntegralLattice
