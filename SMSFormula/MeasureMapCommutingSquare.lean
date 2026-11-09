import Mathlib.MeasureTheory.Measure.Map

/-!
# Measure pushforwards through a commuting square

A small generic interface keeps concrete chart maps and measure identities
opaque when composing a verified source transition with two target maps.
-/

noncomputable section

open MeasureTheory

namespace Measure

/-- A verified source pushforward and a pointwise commuting square identify
the two induced target pushforwards. -/
theorem map_eq_map_of_map_eq_of_forall
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (T : α → β) (L : α → γ) (R : β → γ)
    (μ : Measure α) (ν : Measure β)
    (hT : Measurable T) (hR : Measurable R)
    (hmap : Measure.map T μ = ν)
    (hcomm : ∀ x, R (T x) = L x) :
    Measure.map L μ = Measure.map R ν := by
  rw [← hmap, Measure.map_map hR hT]
  exact Measure.map_congr
    (Filter.Eventually.of_forall fun x => (hcomm x).symm)

end Measure
