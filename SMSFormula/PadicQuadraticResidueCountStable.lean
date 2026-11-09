import SMSFormula.PadicQuadraticLocalDensityLevelOne
import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar
import SMSFormula.RationalAdeleFiniteLocalResidueCount

/-!
# Residue counts at a unit value are level-stable at every odd prime

For an odd prime `p`, an integral Gram matrix `F` of size `n + 1` and a `p`-adic unit `a`,
the existing local-density identity holds at every level `k ≥ 1`:
`p^{kn} · λ(X_a(ℤ_p)) · ν(ℤ_p) = #R_k · ν_vec(ℤ_p^{n+1})`.  Comparing level `k` with level
one cancels the atlas glue and both auxiliary Haar measures, so

```text
#{r mod p^k : r ⬝ F r = a} = p^{(k-1) n} · #{r mod p : r ⬝ F r = a}      (k ≥ 1).
```

The atlas is the existing countable atlas of the nonisotropic vectors, and the Haar measures
are arbitrary auxiliary ones: none of them appears in the conclusion, which is a statement
about finite counts only.  No unimodularity is needed, only that `a` is a unit and the form
is not identically zero.

For the integral lattice `L` of rank `n + 1` the existing residue count
`#{z mod m : Q_L(z) = M}` at `m = p^k` is the same count for `F = L.pairingMatrix` and
`a = M`, so at every odd prime `p ∤ M` the normalized count
`(p^k)^{-n} #{z mod p^k : Q_L(z) = M}` does not depend on `k ≥ 1`.

Negative scope: nothing is said at `p = 2` or at primes dividing `M`, no limit is formed and
no Euler product is asserted.
-/

noncomputable section

open MeasureTheory Set Metric Matrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

local instance rcsPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance rcsPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Level stability: at an odd prime and a unit value, the level-`k` residue count is
`p^{(k-1) n}` times the level-one count, in dimension `n + 1`. -/
theorem card_residue_pow_eq_pow_mul_card_levelOne (hp : p ≠ 2) {n : ℕ}
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1)
    (hform : ∃ v, (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' v ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) :
    (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card =
      p ^ ((k - 1) * n) * (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card := by
  obtain ⟨point, hpoint, hcover⟩ :=
    ((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').exists_padicSquareBranchAtlas_cover
      p hform
  let tH : ∀ i, Measure (((F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').anisotropicOrthogonal
      (point i)) := fun _ ↦ Measure.addHaar
  haveI : ∀ i, (tH i).IsAddHaarMeasure := fun _ ↦ by simp only [tH]; infer_instance
  let νs : Measure ℚ_[p] := Measure.addHaar
  let νv : Measure (Fin (n + 1) → ℚ_[p]) := Measure.addHaar
  have hk' := card_eq_pow_mul_localDensity hp F a ha point hpoint tH νs νv hcover hk
  have h1 := card_levelOne_eq_localDensity hp F a ha point hpoint tH νs νv hcover
  have hc0 : νv (closedBall 0 1) ≠ 0 :=
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).measure_ne_zero νv
      ⟨0, mem_closedBall_self zero_le_one⟩
  have hctop : νv (closedBall 0 1) ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have key : ((Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ (j + 1)) ↦
        r ⬝ᵥ (F.map (toZModPow (j + 1))) *ᵥ r = toZModPow (j + 1) a)).card : ℝ≥0∞) *
        νv (closedBall 0 1) =
      ((p ^ ((j + 1 - 1) * n) * (Finset.univ.filter (fun r : Fin (n + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℕ) : ℝ≥0∞) *
        νv (closedBall 0 1) := by
    rw [← hk', Nat.cast_mul, mul_assoc (((p ^ ((j + 1 - 1) * n) : ℕ) : ℝ≥0∞)), ← h1,
      Nat.add_sub_cancel]
    push_cast
    rw [pow_succ, mul_pow, ← pow_mul]
    simp only [mul_assoc]
  exact_mod_cast (ENNReal.mul_left_inj hc0 hctop).1 key

end PadicInt

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing residue count of the lattice is the `p`-adic residue count of its
Gram matrix at the integer value. -/
theorem card_residueSet_eq_card_filter_padic (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (M : ℤ) (k : ℕ) :
    Nat.card {z : Fin n → ZMod (p ^ k) // L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} =
      (Finset.univ.filter (fun r : Fin n → ZMod (p ^ k) ↦
        r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow k)) *ᵥ r =
          PadicInt.toZModPow k ((M : ℤ) : ℤ_[p]))).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun r _ ↦ ?_
  rw [map_intCast]
  have hform : L.zmodQuadForm (p ^ k) r =
      r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow k)) *ᵥ r := by
    simp only [zmodQuadForm, dotProduct, mulVec, Matrix.map_apply, eq_intCast, map_intCast,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hform]

/-- The positive-definite form is not identically zero over `ℚ_p` in positive rank. -/
theorem exists_padic_pairingMatrix_ne_zero (L : PositiveDefiniteIntegralLattice (n + 1)) (p : ℕ) [Fact p.Prime] :
    ∃ v, (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap') v ≠ 0 := by
  refine ⟨Pi.single 0 1, ?_⟩
  simp only [Matrix.toQuadraticMap', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  simp only [mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, Matrix.map_apply]
  change ((((L.pairingMatrix 0 0 : ℤ) : ℤ_[p]) : ℚ_[p])) ≠ 0
  have hpos : (0 : ℝ) < (L.pairingMatrix 0 0 : ℝ) := L.form_posDef.diag_pos (i := 0)
  have hne : L.pairingMatrix 0 0 ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hpos
    exact lt_irrefl _ hpos
  rw [PadicInt.coe_intCast]
  exact_mod_cast hne

/-- Level stability of the residue count: at every odd prime `p ∤ M` and every `k ≥ 1`,
`#{z mod p^k : Q_L(z) = M} = p^{(k-1) n} · #{z mod p : Q_L(z) = M}` in rank `n + 1`. -/
theorem card_residueSet_primePow_eq (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card {z : Fin (n + 1) → ZMod (p ^ k) //
        L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} =
      p ^ ((k - 1) * n) * Nat.card {z : Fin (n + 1) → ZMod (p ^ 1) //
        L.zmodQuadForm (p ^ 1) z = ((M : ℤ) : ZMod (p ^ 1))} := by
  rw [L.card_residueSet_eq_card_filter_padic p M k, L.card_residueSet_eq_card_filter_padic p M 1]
  have ha : ‖(((M : ℤ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 fun h ↦ hM ((PadicInt.norm_int_lt_one_iff_dvd M).1 h))
  exact PadicInt.card_residue_pow_eq_pow_mul_card_levelOne hp _ _ ha
    (L.exists_padic_pairingMatrix_ne_zero p) hk

/-- The normalized residue count `(p^k)^{-n} #{z mod p^k : Q_L(z) = M}` is level-independent
for `k ≥ 1` at every odd prime `p ∤ M`, in rank `n + 1`. -/
theorem normalized_card_residueSet_primePow_eq (L : PositiveDefiniteIntegralLattice (n + 1)) {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {M : ℤ} (hM : ¬ (p : ℤ) ∣ M) {k : ℕ} (hk : 1 ≤ k) :
    (((p ^ k : ℕ) : ℝ) ^ n)⁻¹ * (Nat.card {z : Fin (n + 1) → ZMod (p ^ k) //
        L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} : ℝ) =
      (((p : ℕ) : ℝ) ^ n)⁻¹ * (Nat.card {z : Fin (n + 1) → ZMod (p ^ 1) //
        L.zmodQuadForm (p ^ 1) z = ((M : ℤ) : ZMod (p ^ 1))} : ℝ) := by
  rw [L.card_residueSet_primePow_eq hp hM hk]
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  push_cast
  rw [show ((p : ℝ) ^ (j + 1)) ^ n = (p : ℝ) ^ (j * n) * (p : ℝ) ^ n by
    rw [pow_succ, mul_pow, ← pow_mul], mul_inv]
  field_simp

end PositiveDefiniteIntegralLattice

end
