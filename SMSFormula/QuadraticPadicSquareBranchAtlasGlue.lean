import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import SMSFormula.QuadraticPadicSquareBranchHaarIndependence
import SMSFormula.QuadraticPadicSquareBranchFiberPositive

/-! Countable atlas glue of the normalized square-branch fiber measures. A
generic lemma: pairwise compatible measures on measurable domains glue to one
measure (the sum of the measures restricted to the `disjointed` domains) that
restricts to each of them on its own domain. Applied to the normalized
branch measures at countably many supplied nonisotropic points (pairwise
compatible by the overlap theorem), this gives one measure on the fiber
`{Q = value}` agreeing with every normalized branch measure on its branch range.
The two-chart glue is the special case; no chart, point or Haar
normalization is chosen here: the points and transverse Haars are supplied. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The glue of a sequence of measures along a sequence of domains: sum of the
measures restricted to the `disjointed` domains. -/
def disjointedGlue (μ : ℕ → Measure X) (R : ℕ → Set X) : Measure X :=
  Measure.sum fun i ↦ (μ i).restrict (disjointed R i)

/-- Pairwise compatible measures glue: the disjointed glue restricts to each
measure on its domain. -/
theorem disjointedGlue_restrict (μ : ℕ → Measure X) (R : ℕ → Set X)
    (hR : ∀ i, MeasurableSet (R i))
    (hcompat : ∀ i j, (μ i).restrict (R i ∩ R j) = (μ j).restrict (R i ∩ R j)) (k : ℕ) :
    (disjointedGlue μ R).restrict (R k) = (μ k).restrict (R k) := by
  have hD : ∀ i, MeasurableSet (disjointed R i) := MeasurableSet.disjointed hR
  rw [disjointedGlue, Measure.restrict_sum _ (hR k)]
  have hterm : ∀ i, ((μ i).restrict (disjointed R i)).restrict (R k) =
      (μ k).restrict (R k ∩ disjointed R i) := by
    intro i
    rw [Measure.restrict_restrict (hR k)]
    have hsub : R k ∩ disjointed R i ⊆ R i ∩ R k :=
      fun x hx ↦ ⟨disjointed_subset R i hx.2, hx.1⟩
    rw [← Measure.restrict_restrict_of_subset hsub, hcompat i k,
      Measure.restrict_restrict_of_subset hsub]
  simp_rw [hterm]
  rw [← Measure.restrict_iUnion (s := fun i ↦ R k ∩ disjointed R i)
    (fun i j hij ↦ (disjoint_disjointed R hij).mono Set.inter_subset_right Set.inter_subset_right)
    (fun i ↦ (hR k).inter (hD i)), ← Set.inter_iUnion, iUnion_disjointed]
  congr 1
  exact Set.inter_eq_left.mpr (Set.subset_iUnion R k)

/-- A measure compatible with every glued measure on the domain overlaps agrees with
the glue on the covered part of its own domain. -/
theorem disjointedGlue_restrict_of_compat (μ : ℕ → Measure X) (R : ℕ → Set X)
    (hR : ∀ i, MeasurableSet (R i)) (ν : Measure X) {R' : Set X} (hR' : MeasurableSet R')
    (hc : ∀ i, (μ i).restrict (R i ∩ R') = ν.restrict (R i ∩ R')) :
    (disjointedGlue μ R).restrict (R' ∩ ⋃ i, R i) = ν.restrict (R' ∩ ⋃ i, R i) := by
  have hD : ∀ i, MeasurableSet (disjointed R i) := MeasurableSet.disjointed hR
  have hS : MeasurableSet (R' ∩ ⋃ i, R i) := hR'.inter (MeasurableSet.iUnion hR)
  rw [disjointedGlue, Measure.restrict_sum _ hS]
  have hterm : ∀ i, ((μ i).restrict (disjointed R i)).restrict (R' ∩ ⋃ i, R i) =
      ν.restrict ((R' ∩ ⋃ i, R i) ∩ disjointed R i) := by
    intro i
    rw [Measure.restrict_restrict hS]
    have hsub : (R' ∩ ⋃ i, R i) ∩ disjointed R i ⊆ R i ∩ R' :=
      fun x hx ↦ ⟨disjointed_subset R i hx.2, hx.1.1⟩
    rw [← Measure.restrict_restrict_of_subset hsub, hc i, Measure.restrict_restrict_of_subset hsub]
  simp_rw [hterm]
  rw [← Measure.restrict_iUnion (s := fun i ↦ (R' ∩ ⋃ i, R i) ∩ disjointed R i)
    (fun i j hij ↦ (disjoint_disjointed R hij).mono Set.inter_subset_right Set.inter_subset_right)
    (fun i ↦ hS.inter (hD i)), ← Set.inter_iUnion, iUnion_disjointed, Set.inter_assoc,
    Set.inter_self]

end MeasureTheory.Measure

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicAtlasGlueMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicAtlasGlueBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space] [LocallyCompactSpace space]

/-- The normalized branch measures are pairwise compatible on the overlaps of
their branch ranges. -/
theorem padicSquareBranchFiberMeasure_normalized_restrict_range_inter
    (form : QuadraticForm ℚ_[prime] space) (firstPoint secondPoint : space)
    (hfirst : form firstPoint ≠ 0) (hsecond : form secondPoint ≠ 0)
    (firstHaar : Measure (form.anisotropicOrthogonal firstPoint))
    (secondHaar : Measure (form.anisotropicOrthogonal secondPoint))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [firstHaar.IsAddHaarMeasure] [secondHaar.IsAddHaarMeasure]
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    ((form.anisotropicOrthogonalProductHaarScalar firstPoint hfirst firstHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime firstPoint hfirst firstHaar value).restrict
      (Set.range (form.padicSquareBranchFiberMap prime firstPoint hfirst value) ∩
        Set.range (form.padicSquareBranchFiberMap prime secondPoint hsecond value)) =
    ((form.anisotropicOrthogonalProductHaarScalar secondPoint hsecond secondHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime secondPoint hsecond secondHaar value).restrict
      (Set.range (form.padicSquareBranchFiberMap prime firstPoint hfirst value) ∩
        Set.range (form.padicSquareBranchFiberMap prime secondPoint hsecond value)) := by
  have hregion : Subtype.val ⁻¹' form.padicSquareBranchOverlap prime firstPoint secondPoint hfirst hsecond =
      Set.range (form.padicSquareBranchFiberMap prime firstPoint hfirst value) ∩
        Set.range (form.padicSquareBranchFiberMap prime secondPoint hsecond value) := by
    rw [form.range_padicSquareBranchFiberMap prime firstPoint hfirst value,
      form.range_padicSquareBranchFiberMap prime secondPoint hsecond value]
    rfl
  rw [← hregion]
  exact form.padicSquareBranchFiberMeasure_normalized_restrict_overlap_eq prime firstPoint secondPoint
    hfirst hsecond firstHaar secondHaar scalarHaar vectorHaar value

/-- The atlas glue: one measure on the fiber from the normalized branch
measures at a supplied sequence of nonisotropic points. -/
def padicSquareBranchAtlasGlue (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space)
    (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) :
    Measure {vector : space // form vector = value} :=
  Measure.disjointedGlue
    (fun i ↦ (form.anisotropicOrthogonalProductHaarScalar (point i) (hpoint i) (transverseHaar i)
        scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime (point i) (hpoint i) (transverseHaar i) value)
    (fun i ↦ Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value))

/-- The atlas glue agrees with every normalized branch measure on its branch
range. -/
theorem padicSquareBranchAtlasGlue_restrict (form : QuadraticForm ℚ_[prime] space)
    (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) (k : ℕ) :
    (form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar value).restrict
        (Set.range (form.padicSquareBranchFiberMap prime (point k) (hpoint k) value)) =
      ((form.anisotropicOrthogonalProductHaarScalar (point k) (hpoint k) (transverseHaar k)
          scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime (point k) (hpoint k) (transverseHaar k) value).restrict
        (Set.range (form.padicSquareBranchFiberMap prime (point k) (hpoint k) value)) :=
  Measure.disjointedGlue_restrict _ _
    (fun i ↦ (form.isOpenEmbedding_padicSquareBranchFiberMap prime (point i) (hpoint i)
      value).isOpen_range.measurableSet)
    (fun i j ↦ form.padicSquareBranchFiberMeasure_normalized_restrict_range_inter prime (point i)
      (point j) (hpoint i) (hpoint j) (transverseHaar i) (transverseHaar j) scalarHaar vectorHaar
      value) k

/-- The atlas glue gives every measurable set inside a branch range its
normalized branch mass. -/
theorem padicSquareBranchAtlasGlue_apply_of_subset (form : QuadraticForm ℚ_[prime] space)
    (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) (k : ℕ)
    {T : Set {vector : space // form vector = value}} (hT : MeasurableSet T)
    (hsub : T ⊆ Set.range (form.padicSquareBranchFiberMap prime (point k) (hpoint k) value)) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar value T =
      ((form.anisotropicOrthogonalProductHaarScalar (point k) (hpoint k) (transverseHaar k)
          scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime (point k) (hpoint k) (transverseHaar k) value) T := by
  have h := congrArg (fun m : Measure {vector : space // form vector = value} ↦ m T)
    (form.padicSquareBranchAtlasGlue_restrict prime point hpoint transverseHaar scalarHaar vectorHaar
      value k)
  simp only [Measure.restrict_apply hT, Set.inter_eq_left.mpr hsub] at h
  exact h

/-- The atlas glue agrees with the normalized branch measure at any further
nonisotropic point on the part of its branch range covered by the atlas. -/
theorem padicSquareBranchAtlasGlue_restrict_of_point (form : QuadraticForm ℚ_[prime] space)
    (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime])
    (x₀ : space) (hx₀ : form x₀ ≠ 0) (haar₀ : Measure (form.anisotropicOrthogonal x₀))
    [haar₀.IsAddHaarMeasure] :
    (form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar value).restrict
        (Set.range (form.padicSquareBranchFiberMap prime x₀ hx₀ value) ∩
          ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value)) =
      ((form.anisotropicOrthogonalProductHaarScalar x₀ hx₀ haar₀ scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime x₀ hx₀ haar₀ value).restrict
        (Set.range (form.padicSquareBranchFiberMap prime x₀ hx₀ value) ∩
          ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value)) :=
  Measure.disjointedGlue_restrict_of_compat _ _
    (fun i ↦ (form.isOpenEmbedding_padicSquareBranchFiberMap prime (point i) (hpoint i)
      value).isOpen_range.measurableSet) _
    (form.isOpenEmbedding_padicSquareBranchFiberMap prime x₀ hx₀ value).isOpen_range.measurableSet
    (fun i ↦ form.padicSquareBranchFiberMeasure_normalized_restrict_range_inter prime (point i) x₀
      (hpoint i) hx₀ (transverseHaar i) haar₀ scalarHaar vectorHaar value)

end QuadraticMap
