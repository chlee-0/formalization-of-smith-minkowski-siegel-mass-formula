import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Directed suprema of measures

This module constructs a measure from a monotone directed family by taking the
pointwise supremum on measurable sets.  The only nonformal input is the
commutation of a directed monotone supremum in `ℝ≥0∞` with a countable sum.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ENNReal

/-- A directed monotone supremum of nonnegative extended-real sequences
commutes with their countable sum. -/
theorem iSup_tsum_of_monotone
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    (f : ι → ℕ → ℝ≥0∞)
    (hf : ∀ n, Monotone fun i => f i n) :
    (⨆ i, ∑' n, f i n) = ∑' n, ⨆ i, f i n := by
  apply le_antisymm
  · exact iSup_le fun i =>
      ENNReal.tsum_le_tsum fun n => le_iSup (fun j => f j n) i
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    have hfinite :
        (∑ n ∈ s, ⨆ i, f i n) = ⨆ i, ∑ n ∈ s, f i n := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert n s hn ih =>
          simp only [Finset.sum_insert hn]
          rw [ih, ENNReal.iSup_add_iSup_of_monotone]
          · exact hf n
          · intro i j hij
            exact Finset.sum_le_sum fun m _ => hf m hij
    rw [hfinite]
    exact iSup_le fun i =>
      le_iSup_of_le i (ENNReal.sum_le_tsum s)

end ENNReal

namespace MeasureTheory.Measure

variable {α ι : Type*} [MeasurableSpace α]
  [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- The measure whose value on every measurable set is the pointwise supremum
of a monotone directed family of measures. -/
def directedSup
    (μ : ι → Measure α)
    (hμ : Monotone μ) :
    Measure α :=
  Measure.ofMeasurable
    (fun s _ => ⨆ i, μ i s)
    (by simp)
    (by
      intro f hf hdisj
      simp_rw [measure_iUnion hdisj hf]
      exact ENNReal.iSup_tsum_of_monotone
        (fun i n => μ i (f n))
        (fun n _ _ hij => hμ hij (f n)))

/-- The directed-sup measure is the literal pointwise supremum on measurable
sets. -/
theorem directedSup_apply
    (μ : ι → Measure α)
    (hμ : Monotone μ)
    {s : Set α}
    (hs : MeasurableSet s) :
    directedSup μ hμ s = ⨆ i, μ i s :=
  Measure.ofMeasurable_apply s hs

end MeasureTheory.Measure
