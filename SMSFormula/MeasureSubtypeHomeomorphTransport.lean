import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Transporting subtype-comap measures through a homeomorphism

A compact carrier-agnostic interface for transporting measures obtained by
comapping to measurable subtypes.  This keeps large application-specific
carrier terms out of the resulting proof object.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory.Measure

/-- If a homeomorphism transports an ambient measure up to a scalar and a
subtype homeomorphism is its restriction, then it transports the corresponding
subtype-comap measures by the same scalar. -/
theorem map_comap_subtype_of_map_smul
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {s : Set A} {t : Set B} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : A → B) (hf : Measurable f) (E : s ≃ᵐ t)
    (hval : Subtype.val ∘ E = f ∘ Subtype.val)
    (μ : Measure A) (ν : Measure B) (c : ℝ≥0)
    (hmap : Measure.map f μ = c • ν) (hpre : f ⁻¹' t = s) :
    Measure.map E (Measure.comap Subtype.val μ) =
      c • Measure.comap Subtype.val ν := by
  apply (MeasurableEmbedding.subtype_coe ht).map_injective
  calc
    Measure.map Subtype.val
        (Measure.map E (Measure.comap Subtype.val μ)) =
      Measure.map f
        (Measure.map Subtype.val (Measure.comap Subtype.val μ)) := by
      rw [Measure.map_map (MeasurableEmbedding.subtype_coe ht).measurable E.measurable,
        Measure.map_map hf
          (MeasurableEmbedding.subtype_coe hs).measurable,
        hval]
    _ = Measure.map f (μ.restrict s) := by
      rw [map_comap_subtype_coe hs]
    _ = (Measure.map f μ).restrict t := by
      rw [Measure.restrict_map hf ht, hpre]
    _ = (c • ν).restrict t := by rw [hmap]
    _ = c • ν.restrict t := by rw [Measure.restrict_smul]
    _ = c • Measure.map Subtype.val (Measure.comap Subtype.val ν) := by
      rw [map_comap_subtype_coe ht]
    _ = Measure.map Subtype.val (c • Measure.comap Subtype.val ν) := by
      rw [Measure.map_smul]

/-- Pointwise-membership form of `map_comap_subtype_of_map_smul`.  Keeping the
dependent preimage-set extensionality inside this carrier-agnostic theorem
prevents large application-specific subtype terms from being rebuilt in a
specialization proof. -/
theorem map_comap_subtype_of_map_smul_of_mem_iff
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {s : Set A} {t : Set B} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : A → B) (hf : Measurable f) (E : s ≃ᵐ t)
    (hval : Subtype.val ∘ E = f ∘ Subtype.val)
    (μ : Measure A) (ν : Measure B) (c : ℝ≥0)
    (hmap : Measure.map f μ = c • ν)
    (hmem : ∀ x, f x ∈ t ↔ x ∈ s) :
    Measure.map E (Measure.comap Subtype.val μ) =
      c • Measure.comap Subtype.val ν := by
  apply map_comap_subtype_of_map_smul hs ht f hf E hval μ ν c hmap
  ext x
  exact hmem x

/-- Converse carrier-level direction used when the scalar is first known on
exact source and target subtypes. If the subtype measures include as the
ambient restrictions and the restricted map scales them, then the ambient
pushforward has the same scalar after restriction to the target set. -/
theorem restrict_map_eq_smul_restrict_of_map_subtype_of_mem_iff
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {s : Set A} {t : Set B} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : A → B) (hf : Measurable f) (E : s ≃ᵐ t)
    (μ : Measure A) (ν : Measure B)
    (μs : Measure s) (νt : Measure t) (c : ℝ≥0)
    (hμs : Measure.map Subtype.val μs = μ.restrict s)
    (hνt : Measure.map Subtype.val νt = ν.restrict t)
    (hmap : Measure.map E μs = c • νt)
    (hval : ∀ x, f x.1 = (E x).1)
    (hmem : ∀ x, f x ∈ t ↔ x ∈ s) :
    (Measure.map f μ).restrict t = c • ν.restrict t := by
  have hpre : f ⁻¹' t = s := by
    ext x
    exact hmem x
  calc
    (Measure.map f μ).restrict t = Measure.map f (μ.restrict s) := by
      rw [Measure.restrict_map hf ht, hpre]
    _ = Measure.map f (Measure.map Subtype.val μs) := by rw [hμs]
    _ = Measure.map Subtype.val (Measure.map E μs) := by
      rw [Measure.map_map hf (MeasurableEmbedding.subtype_coe hs).measurable,
        Measure.map_map (MeasurableEmbedding.subtype_coe ht).measurable E.measurable]
      apply Measure.map_congr
      filter_upwards with x
      exact hval x
    _ = Measure.map Subtype.val (c • νt) := by rw [hmap]
    _ = c • Measure.map Subtype.val νt := Measure.map_smul c νt Subtype.val
    _ = c • ν.restrict t := by rw [hνt]

end MeasureTheory.Measure
