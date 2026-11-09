import SMSFormula.RationalAdeleFiniteLocalRestrictedResidueCount
import SMSFormula.RationalAdeleRestrictedResidueCountMultiplicative

/-!
# The finite-place replacement lemma from local count ratios

For supplied local restriction data `(P, e, R_p)` put `N₀ = ∏_{p∈P} p^{e p}` and let
`R ⊆ (ZMod N₀)^n` be the residues whose reduction modulo each `p^{e p}` lies in `R_p` (the
Chinese remainder product).  At every level `m` divisible by `N₀`, membership of the reduction
modulo `N₀` in `R` is local admissibility.  Suppose that at each `p ∈ P` the local restricted and
full counts are eventually in the ratio of two supplied finite masses,

`f(p^v) · gF_p = F(p^v) · gR_p`, `gF_p ≠ 0`, with `F(p^v) ≠ 0` eventually.

Then the multiplicative factorization of restricted counts and the counting-form replacement
give, above rank four,

`d_fin(1_{U_R})(M) = (∏_P gR_p / ∏_P gF_p) · d_fin(1_Zhat)(M)`.

The local hypotheses are exactly what `PadicInt.exists_card_restricted_mul_glue_eq` supplies with
`gF_p = glue_M(ℤ_p^n)`, `gR_p = glue_M(T_{R_p})`.  No residue set, level or mass is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The level `N₀ = ∏_{p∈P} p^{e p}` of the local restriction data. -/
def localRestrictionLevel (P : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ p ∈ P, p ^ e p

theorem primePow_dvd_localRestrictionLevel {P : Finset ℕ} {e : ℕ → ℕ} {p : ℕ} (hp : p ∈ P) :
    p ^ e p ∣ localRestrictionLevel P e :=
  Finset.dvd_prod_of_mem (fun q ↦ q ^ e q) hp

theorem localRestrictionLevel_ne_zero {P : Finset ℕ} {e : ℕ → ℕ} (hP : ∀ p ∈ P, p.Prime) :
    localRestrictionLevel P e ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun p hp ↦ pow_ne_zero _ (hP p hp).ne_zero

/-- The Chinese remainder product of the local residue sets, at level `N₀`. -/
def localRestrictionSet (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) :
    Set (Fin n → ZMod (localRestrictionLevel P e)) :=
  {w | ∀ (p : ℕ) (hp : p ∈ P),
    (fun i ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) (w i)) ∈ R p}

/-- At every level divisible by `N₀`, membership in the CRT product is local admissibility. -/
theorem castHom_mem_localRestrictionSet_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) {m : ℕ}
    (hdvd : localRestrictionLevel P e ∣ m) (z : Fin n → ZMod m) :
    (fun i ↦ ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) ∈
        localRestrictionSet P e R ↔
      IsLocallyAdmissible P e R m z := by
  have hcomp : ∀ (p : ℕ) (hp : p ∈ P) (h : p ^ e p ∣ m) (i : Fin n),
      ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p))
          (ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) =
        ZMod.castHom h (ZMod (p ^ e p)) (z i) := by
    intro p hp h i
    change ((ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p))).comp
      (ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)))) (z i) = _
    congr 1
    exact Subsingleton.elim _ _
  constructor
  · intro hz p hp h
    have := hz p hp
    simpa only [hcomp p hp h] using this
  · intro hz p hp
    have h : p ^ e p ∣ m := (primePow_dvd_localRestrictionLevel hp).trans hdvd
    have := hz p hp h
    simpa only [← hcomp p hp h] using this

/-- The `p`-adic valuation of `k!` tends to infinity. -/
theorem tendsto_factorization_factorial_of_prime {p : ℕ} (hp : p.Prime) :
    Tendsto (fun k : ℕ ↦ (Nat.factorial k).factorization p) atTop atTop := by
  refine tendsto_atTop.2 fun j ↦ ?_
  filter_upwards [eventually_ge_atTop (p ^ j)] with k hk
  exact (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero k)).1
    (Nat.dvd_factorial (pow_pos hp.pos j) hk)

/-- The count identity at large factorial levels:
`f(k!) · ∏_P gF_p = F(k!) · ∏_P gR_p` eventually. -/
theorem eventually_restrictedResidueCount_mul_prod_eq (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      (L.restrictedResidueCount M P e R (Nat.factorial k) : ℝ≥0∞) * ∏ p ∈ P, gF p =
        (L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * ∏ p ∈ P, gR p := by
  have hall : ∀ᶠ k : ℕ in atTop, ∀ p ∈ P,
      ((L.restrictedResidueCount M P e R (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞) * gR p) ∧
        L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) ≠ 0 :=
    (Filter.eventually_all_finset P).2 fun p hp ↦
      ((tendsto_factorization_factorial_of_prime (hP p hp).1).eventually (hloc p hp)).and
        ((tendsto_factorization_factorial_of_prime (hP p hp).1).eventually (hFne p hp))
  filter_upwards [hall] with k hk
  have hprod := L.restrictedResidueCount_mul_prod_eq M P e R hP (Nat.factorial_ne_zero k)
  have hprodE : (L.restrictedResidueCount M P e R (Nat.factorial k) : ℝ≥0∞) *
      ∏ p ∈ P, (L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞) =
      (L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) *
        ∏ p ∈ P, (L.restrictedResidueCount M P e R (p ^ (Nat.factorial k).factorization p) :
          ℝ≥0∞) := by
    exact_mod_cast hprod
  have hFP0 : (∏ p ∈ P, (L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞))
      ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp ↦ by exact_mod_cast (hk p hp).2
  have hFPt : (∏ p ∈ P, (L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞))
      ≠ ⊤ := ENNReal.prod_ne_top fun p _ ↦ ENNReal.natCast_ne_top _
  refine (ENNReal.mul_left_inj hFP0 hFPt).mp ?_
  set A : ℝ≥0∞ := ∏ p ∈ P, (L.fullResidueCount M (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞)
    with hA
  set Bf : ℝ≥0∞ := ∏ p ∈ P, (L.restrictedResidueCount M P e R
    (p ^ (Nat.factorial k).factorization p) : ℝ≥0∞) with hBf
  have hstep : Bf * ∏ p ∈ P, gF p = A * ∏ p ∈ P, gR p := by
    rw [hBf, hA, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp ↦ (hk p hp).1
  calc ((L.restrictedResidueCount M P e R (Nat.factorial k) : ℝ≥0∞) * ∏ p ∈ P, gF p) * A
      = ((L.restrictedResidueCount M P e R (Nat.factorial k) : ℝ≥0∞) * A) *
          ∏ p ∈ P, gF p := by ring
    _ = ((L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * Bf) * ∏ p ∈ P, gF p := by
        rw [hprodE]
    _ = (L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * (Bf * ∏ p ∈ P, gF p) := by ring
    _ = (L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * (A * ∏ p ∈ P, gR p) := by rw [hstep]
    _ = ((L.fullResidueCount M (Nat.factorial k) : ℝ≥0∞) * ∏ p ∈ P, gR p) * A := by ring

/-- The finite-place replacement lemma from local count ratios: above rank four,
`d_fin(1_{U_R})(M) = (∏_P gR_p / ∏_P gF_p) · d_fin(1_Zhat)(M)` for the CRT product `R`. -/
theorem finiteLocalValueDensity_localRestriction_eq_mul (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
        (residueRestrictedIndicator n (localRestrictionLevel P e) (localRestrictionSet P e R))
        (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
      (((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal : ℂ) *
        L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          rationalFiniteAdeleVectorIntegralIndicator
          (algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hPF0 : (∏ p ∈ P, gF p) ≠ 0 := Finset.prod_ne_zero_iff.2 hgF0
  have hPFt : (∏ p ∈ P, gF p) ≠ ⊤ := ENNReal.prod_ne_top hgFt
  refine L.finiteLocalValueDensity_residueRestricted_eq_mul_of_eventually_card_eq hn _ _ M _ ?_
  filter_upwards [L.eventually_restrictedResidueCount_mul_prod_eq M P e R hP gF gR hloc hFne]
    with k hk hdvd
  have hcardR : Nat.card {z : Fin n → ZMod (Nat.factorial k) //
      L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
      (fun i ↦ ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) ∈
        localRestrictionSet P e R} = L.restrictedResidueCount M P e R (Nat.factorial k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦
      and_congr_right' (castHom_mem_localRestrictionSet_iff P e R hdvd z))
  have hcardF : Nat.card {z : Fin n → ZMod (Nat.factorial k) //
      L.zmodQuadForm (Nat.factorial k) z = ((M : ℤ) : ZMod (Nat.factorial k)) ∧
      (fun i ↦ ZMod.castHom hdvd (ZMod (localRestrictionLevel P e)) (z i)) ∈
        (Set.univ : Set (Fin n → ZMod (localRestrictionLevel P e)))} =
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

end PositiveDefiniteIntegralLattice
