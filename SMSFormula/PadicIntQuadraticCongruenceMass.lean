import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.NumberTheory.Padics.RingHoms

/-! Congruence masses on `ℤ_p^N`. Reduction modulo `p^k` coordinatewise,
`ρ : ℤ_p^N → (ℤ/p^kℤ)^N`, is a surjective additive map whose fibers are the closed
balls of radius `p^{-k}`. For every left-invariant probability measure on `ℤ_p^N`
each fiber therefore has mass `p^{-kN}`, and the preimage of a finite residue set
`R` has mass `#R · p^{-kN}`. For an integral Gram matrix `F` and `a ∈ ℤ_p` the
level-`k` congruence set `{x : ‖xᵀFx − a‖ ≤ p^{-k}}` is the preimage of the
residue solutions of `r ⬝ F̄ r = ā`, so

`p^{kN} · μ{x : ‖xᵀFx − a‖ ≤ p^{-k}} = #{r ∈ (ℤ/p^kℤ)^N : r ⬝ F̄ r = ā}`.

This is the finite-count side of the local density `d_p(a)`. Nothing is chosen
beyond existence of residue lifts. -/
noncomputable section
open MeasureTheory Set Metric Matrix
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

theorem toZModPow_eq_zero_iff (z : ℤ_[p]) (k : ℕ) :
    toZModPow k z = 0 ↔ ‖z‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [← RingHom.mem_ker, ker_toZModPow, norm_le_pow_iff_mem_span_pow]

/-- Coordinatewise reduction modulo `p^k`. -/
def vectorReduction (k : ℕ) : (Fin N → ℤ_[p]) →+ (Fin N → ZMod (p ^ k)) :=
  (toZModPow k).toAddMonoidHom.compLeft (Fin N)

@[simp] theorem vectorReduction_apply (k : ℕ) (x : Fin N → ℤ_[p]) (i : Fin N) :
    vectorReduction k x i = toZModPow k (x i) := rfl

theorem vectorReduction_surjective (k : ℕ) :
    Function.Surjective (vectorReduction (p := p) (N := N) k) := by
  intro r
  choose y hy using fun i ↦ ZMod.ringHom_surjective (toZModPow (p := p) k) (r i)
  exact ⟨y, funext hy⟩

theorem vectorReduction_eq_iff (k : ℕ) (x y : Fin N → ℤ_[p]) :
    vectorReduction k x = vectorReduction k y ↔ ‖x - y‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  constructor
  · intro h i
    have hi := congrFun h i
    simp only [vectorReduction_apply] at hi
    rw [Pi.sub_apply, ← toZModPow_eq_zero_iff, map_sub, hi, sub_self]
  · intro h
    funext i
    have hi := h i
    rw [Pi.sub_apply, ← toZModPow_eq_zero_iff, map_sub, sub_eq_zero] at hi
    exact hi

theorem preimage_vectorReduction_singleton (k : ℕ) (y : Fin N → ℤ_[p]) :
    vectorReduction k ⁻¹' {vectorReduction k y} = closedBall y ((p : ℝ) ^ (-(k : ℤ))) := by
  ext x
  rw [mem_preimage, mem_singleton_iff, vectorReduction_eq_iff, mem_closedBall, dist_eq_norm]

variable [MeasurableSpace (Fin N → ℤ_[p])] [BorelSpace (Fin N → ℤ_[p])]
  [MeasurableAdd (Fin N → ℤ_[p])]

omit [MeasurableAdd (Fin N → ℤ_[p])] in
theorem measurableSet_preimage_vectorReduction (k : ℕ) (R : Set (Fin N → ZMod (p ^ k))) :
    MeasurableSet (vectorReduction (p := p) k ⁻¹' R) := by
  have hR : R = ⋃ r ∈ R, {r} := by ext; simp
  rw [hR, Set.preimage_iUnion₂]
  refine MeasurableSet.biUnion (Set.to_countable R) fun r _ ↦ ?_
  obtain ⟨y, rfl⟩ := vectorReduction_surjective (p := p) (N := N) k r
  rw [preimage_vectorReduction_singleton]
  exact isClosed_closedBall.measurableSet

omit [BorelSpace (Fin N → ℤ_[p])] in
/-- Every reduction fiber has the mass of the kernel. -/
theorem measure_preimage_vectorReduction_singleton (μ : Measure (Fin N → ℤ_[p]))
    [μ.IsAddLeftInvariant] (k : ℕ) (r : Fin N → ZMod (p ^ k)) :
    μ (vectorReduction k ⁻¹' {r}) =
      μ ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) := by
  obtain ⟨y, rfl⟩ := vectorReduction_surjective (p := p) (N := N) k r
  have h : vectorReduction k ⁻¹' {vectorReduction k y} =
      (fun h ↦ -y + h) ⁻¹' ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, SetLike.mem_coe, AddMonoidHom.mem_ker, map_add,
      map_neg, neg_add_eq_zero]
    exact eq_comm
  rw [h, measure_preimage_add]

/-- The kernel has mass `p^{-kN}` of the total. -/
theorem card_mul_measure_ker_vectorReduction (μ : Measure (Fin N → ℤ_[p]))
    [μ.IsAddLeftInvariant] (k : ℕ) :
    ((p ^ k) ^ N : ℝ≥0∞) * μ ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) =
      μ univ := by
  have hker : MeasurableSet ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) := by
    have : ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) =
        vectorReduction k ⁻¹' {0} := by ext; simp
    rw [this]
    exact measurableSet_preimage_vectorReduction k _
  have hindex : (vectorReduction (p := p) (N := N) k).ker.index = (p ^ k) ^ N := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (vectorReduction_surjective k),
      AddSubgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  haveI : (vectorReduction (p := p) (N := N) k).ker.FiniteIndex :=
    ⟨by rw [hindex]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  have h := AddSubgroup.index_mul_measure (vectorReduction (p := p) (N := N) k).ker hker μ
  rw [hindex] at h
  exact_mod_cast h

/-- The preimage of a finite residue set has mass `#R` times the kernel mass. -/
theorem measure_preimage_vectorReduction_finset (μ : Measure (Fin N → ℤ_[p]))
    [μ.IsAddLeftInvariant] (k : ℕ) (R : Finset (Fin N → ZMod (p ^ k))) :
    μ (vectorReduction k ⁻¹' (R : Set (Fin N → ZMod (p ^ k)))) =
      R.card * μ ((vectorReduction (p := p) (N := N) k).ker : Set (Fin N → ℤ_[p])) := by
  have hR : vectorReduction k ⁻¹' (R : Set (Fin N → ZMod (p ^ k))) =
      ⋃ r ∈ R, vectorReduction (p := p) (N := N) k ⁻¹' {r} := by
    ext x; simp
  rw [hR, measure_biUnion_finset]
  · simp_rw [measure_preimage_vectorReduction_singleton μ k]
    rw [Finset.sum_const, nsmul_eq_mul]
  · intro r _ s _ hrs
    exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hrs)
  · exact fun r _ ↦ measurableSet_preimage_vectorReduction k _

/-- Quadratic congruence mass: for an integral Gram matrix and a left-invariant
measure, `p^{kN} · μ{x : ‖xᵀFx − a‖ ≤ p^{-k}} = #{r : r ⬝ F̄ r = ā} · μ(ℤ_p^N)`. -/
theorem card_mul_measure_quadraticCongruence (μ : Measure (Fin N → ℤ_[p]))
    [μ.IsAddLeftInvariant] (F : Matrix (Fin N) (Fin N) ℤ_[p]) (a : ℤ_[p]) (k : ℕ) :
    ((p ^ k) ^ N : ℝ≥0∞) *
        μ {x | ‖x ⬝ᵥ F *ᵥ x - a‖ ≤ (p : ℝ) ^ (-(k : ℤ))} =
      (Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a)).card * μ univ := by
  classical
  have hset : {x : Fin N → ℤ_[p] | ‖x ⬝ᵥ F *ᵥ x - a‖ ≤ (p : ℝ) ^ (-(k : ℤ))} =
      vectorReduction k ⁻¹' ((Finset.univ.filter (fun r : Fin N → ZMod (p ^ k) ↦
        r ⬝ᵥ (F.map (toZModPow k)) *ᵥ r = toZModPow k a) : Finset _) : Set _) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and]
    rw [← toZModPow_eq_zero_iff, map_sub, sub_eq_zero, RingHom.map_dotProduct]
    have hmv : (toZModPow k) ∘ (F *ᵥ x) = F.map (toZModPow k) *ᵥ ((toZModPow k) ∘ x) := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [hmv]
    rfl
  rw [hset, measure_preimage_vectorReduction_finset, ← card_mul_measure_ker_vectorReduction μ k]
  ring

end PadicInt
