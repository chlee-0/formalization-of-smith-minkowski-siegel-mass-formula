import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Gluing weighted measure pushforwards over disjoint unions

This small generic interface combines countable additivity with
`Measure.withDensity` and `Measure.map`. It is useful when a nonlinear
pushforward can be proved separately on a countable measurable partition.
-/

noncomputable section

open MeasureTheory

namespace MeasureTheory.Measure

/-- Piecewise weighted pushforwards over pairwise-disjoint measurable source
and target families glue to the corresponding pushforward on their unions. -/
theorem map_withDensity_restrict_iUnion_of_disjoint
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable ι]
    (f : α → β) (μ : Measure α) (ν : Measure β)
    (J : α → ENNReal) (s : ι → Set α) (t : ι → Set β)
    (hf : Measurable f)
    (hs : Pairwise (Function.onFun Disjoint s))
    (ht : Pairwise (Function.onFun Disjoint t))
    (hsm : ∀ i, MeasurableSet (s i))
    (htm : ∀ i, MeasurableSet (t i))
    (hlocal : ∀ i,
      Measure.map f ((μ.restrict (s i)).withDensity J) =
        ν.restrict (t i)) :
    Measure.map f
        ((μ.restrict (⋃ i, s i)).withDensity J) =
      ν.restrict (⋃ i, t i) := by
  rw [Measure.restrict_iUnion hs hsm]
  rw [withDensity_sum]
  rw [Measure.map_sum hf.aemeasurable]
  simp_rw [hlocal]
  rw [← Measure.restrict_iUnion ht htm]

end MeasureTheory.Measure
