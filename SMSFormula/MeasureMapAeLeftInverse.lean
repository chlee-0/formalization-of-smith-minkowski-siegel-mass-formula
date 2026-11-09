import Mathlib.MeasureTheory.Measure.Map

/-!
# Cancelling a measure map with an almost-everywhere left inverse

This small generic interface avoids requiring a globally injective measurable
map. It is useful when a partial chart has a measurable extension whose left
inverse identity holds only on the supports of the two measures.
-/

open MeasureTheory

namespace MeasureTheory.Measure

theorem eq_of_map_eq_of_ae_leftInverse
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {g : β → α}
    (hf : Measurable f) (hg : Measurable g)
    {μ ν : Measure α}
    (hμ : g ∘ f =ᵐ[μ] id)
    (hν : g ∘ f =ᵐ[ν] id)
    (hmap : Measure.map f μ = Measure.map f ν) :
    μ = ν := by
  have hmapμ : Measure.map (g ∘ f) μ = μ := by
    calc
      Measure.map (g ∘ f) μ = Measure.map id μ :=
        Measure.map_congr hμ
      _ = μ := Measure.map_id
  have hmapν : Measure.map (g ∘ f) ν = ν := by
    calc
      Measure.map (g ∘ f) ν = Measure.map id ν :=
        Measure.map_congr hν
      _ = ν := Measure.map_id
  calc
    μ = Measure.map (g ∘ f) μ := hmapμ.symm
    _ = Measure.map g (Measure.map f μ) := by
      symm
      rw [Measure.map_map hg hf]
    _ = Measure.map g (Measure.map f ν) := congrArg (Measure.map g) hmap
    _ = Measure.map (g ∘ f) ν := by
      rw [Measure.map_map hg hf]
    _ = ν := hmapν

end MeasureTheory.Measure
