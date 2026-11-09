import SMSFormula.RationalAdeleFiniteLocalReplacementAssembly
import SMSFormula.PadicQuadraticRestrictedLocalDensityCount
import SMSFormula.PadicQuadraticResidueCountStable

/-!
# The local hypotheses of the replacement lemma, from the p-adic tube law

At a prime `p ∈ P`, the lattice counts at levels `p^v` are the `ℤ_p`-matrix counts of the
Gram matrix (`card_residueSet_eq_card_filter_padic`), and at levels `v ≥ e p` local
admissibility is exactly the restriction by `R_p` (no other prime of `P` divides `p^v`).  The
exact local count ratio `PadicInt.exists_card_restricted_mul_glue_eq` therefore gives the local
hypothesis of `finiteLocalValueDensity_localRestriction_eq_mul`:

`f(p^v) · glue_M(ℤ_p^n) = F(p^v) · glue_M(T_{R_p})` for all large `v`,

and a nonzero full glue mass makes `F(p^v) ≠ 0` for all large `v`.  The atlas and Haars at `p` are
supplied.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Matrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance lrPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance lrPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- At `p^v` with `v ≥ e p`, local admissibility is the `R_p` restriction. -/
theorem isLocallyAdmissible_primePow_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    {p : ℕ} (hpP : p ∈ P) {v : ℕ} (hev : e p ≤ v) (z : Fin n → ZMod (p ^ v)) :
    IsLocallyAdmissible P e R (p ^ v) z ↔
      (fun i ↦ ZMod.castHom (pow_dvd_pow p hev) (ZMod (p ^ e p)) (z i)) ∈ R p := by
  constructor
  · intro hz
    exact hz p hpP (pow_dvd_pow p hev)
  · intro hz q hqP hd
    have hqp : q = p := by
      have hq := (hP q hqP).1
      have hqdvd : q ∣ p ^ v := (dvd_pow_self q (by have := (hP q hqP).2; omega)).trans hd
      exact (Nat.prime_dvd_prime_iff_eq hq (hP p hpP).1).1 (hq.dvd_of_dvd_pow hqdvd)
    subst hqp
    exact hz

/-- The restricted count at `p^v` is the `ℤ_p`-matrix restricted count, for `v ≥ e p`. -/
theorem restrictedResidueCount_primePow_eq_card_filter_padic (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) {p : ℕ} [Fact p.Prime] (hpP : p ∈ P) {v : ℕ}
    (hev : e p ≤ v) [DecidablePred (· ∈ R p)] :
    L.restrictedResidueCount M P e R (p ^ v) =
      (Finset.univ.filter (fun r : Fin n → ZMod (p ^ v) ↦
        r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow v)) *ᵥ r =
            PadicInt.toZModPow v ((M : ℤ) : ℤ_[p]) ∧
          (fun i ↦ ZMod.castHom (pow_dvd_pow p hev) (ZMod (p ^ e p)) (r i)) ∈ R p)).card := by
  classical
  rw [restrictedResidueCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun r _ ↦ ?_
  rw [isLocallyAdmissible_primePow_iff P e R hP hpP hev, map_intCast]
  have hform : L.zmodQuadForm (p ^ v) r =
      r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow v)) *ᵥ r := by
    simp only [zmodQuadForm, dotProduct, mulVec, Matrix.map_apply, eq_intCast, map_intCast,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hform]

/-- The local hypothesis of the replacement lemma at `p ∈ P`, from the p-adic tube law. -/
theorem eventually_restrictedResidueCount_primePow_mul_glue_eq (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) {p : ℕ} [Fact p.Prime] (hpP : p ∈ P)
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0) (point : ℕ → Fin n → ℚ_[p])
    (hpoint : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin n → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point hpoint i) :
    ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) *
          (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
            (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) *
          (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
            (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p])
            (Subtype.val ⁻¹' PadicInt.restrictedIntegralVectors (e p) (R p)) := by
  classical
  obtain ⟨k₀, hk⟩ := PadicInt.exists_card_restricted_mul_glue_eq
    (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) ((M : ℤ) : ℤ_[p]) hM point hpoint tH νs νv hcover
    (e p) (R p)
  filter_upwards [eventually_ge_atTop (max k₀ (e p))] with v hv
  have hev : e p ≤ v := le_of_max_le_right hv
  rw [L.restrictedResidueCount_primePow_eq_card_filter_padic M P e R hP hpP hev, fullResidueCount,
    L.card_residueSet_eq_card_filter_padic p M v]
  exact hk v (le_of_max_le_left hv) hev

/-- A nonzero full glue mass makes the full local counts eventually nonzero. -/
theorem eventually_fullResidueCount_primePow_ne_zero (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    {p : ℕ} [Fact p.Prime]
    (hM : (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ≠ 0) (point : ℕ → Fin n → ℚ_[p])
    (hpoint : ∀ i, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin n → ℚ_[p])) [νv.IsAddHaarMeasure]
    (hcover : {w | ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasRegion
          p point hpoint i)
    (hg0 : (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
            (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
            p point hpoint tH νs νv (((M : ℤ) : ℤ_[p]) : ℚ_[p]) {x | ‖x.1‖ ≤ 1} ≠ 0) :
    ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0 := by
  classical
  obtain ⟨k₀, hk⟩ := PadicInt.exists_card_eq_localDensity
    (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) ((M : ℤ) : ℤ_[p]) hM point hpoint tH νs νv hcover
  filter_upwards [eventually_ge_atTop k₀] with v hv
  intro h0
  have h := hk v hv
  rw [fullResidueCount, L.card_residueSet_eq_card_filter_padic p M v] at h0
  rw [h0, Nat.cast_zero, zero_mul] at h
  have hP : ((p ^ v) ^ n : ℝ≥0∞) ≠ 0 := by
    have : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact pow_ne_zero _ (pow_ne_zero _ this)
  have hB : νs (closedBall (((M : ℤ) : ℤ_[p]) : ℚ_[p]) ((p : ℝ) ^ (-(v : ℤ)))) ≠ 0 :=
    (IsUltrametricDist.isOpen_closedBall _
      (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne').measure_ne_zero νs
      ⟨_, mem_closedBall_self (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).le⟩
  exact mul_ne_zero hP (mul_ne_zero hg0 hB) h

end PositiveDefiniteIntegralLattice
