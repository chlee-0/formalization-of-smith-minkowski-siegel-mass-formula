import SMSFormula.AdelicDoubleCosets
import SMSFormula.MeasureDirectedSup
import Mathlib.Probability.ProductMeasure

/-!
# Transporting inversion-invariant measures

This module records the formal measure-theoretic operations needed to pass
local unimodularity through the finite-adelic construction.  None of the
results uses Haar uniqueness: inversion invariance is transported directly
through inversion-compatible maps, products, scalar multiplication, subgroup
comaps, and directed suprema.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- An inversion-compatible measurable map transports inversion invariance. -/
theorem isInvInvariant_map_of_commutes
    {G H : Type*} [Inv G] [Inv H]
    [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableInv G] [MeasurableInv H]
    (mu : Measure G) [IsInvInvariant mu]
    (f : G → H) (hf : Measurable f)
    (hfinv : ∀ x, f (x⁻¹) = (f x)⁻¹) :
    IsInvInvariant (Measure.map f mu) := by
  constructor
  rw [Measure.inv_def, Measure.map_map measurable_inv hf]
  have hfun : Inv.inv ∘ f = f ∘ Inv.inv := by
    funext x
    exact (hfinv x).symm
  rw [hfun, ← Measure.map_map hf measurable_inv,
    Measure.map_inv_eq_self]

/-- Inversion invariance descends along an inversion-compatible measurable
embedding when the pushed-forward measure is inversion invariant. -/
theorem isInvInvariant_of_map_of_commutes
    {G H : Type*} [Inv G] [Inv H]
    [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableInv G] [MeasurableInv H]
    (mu : Measure G)
    (f : G → H) (hf : MeasurableEmbedding f)
    (hfinv : ∀ x, f (x⁻¹) = (f x)⁻¹)
    (hmap : IsInvInvariant (Measure.map f mu)) :
    IsInvInvariant mu := by
  constructor
  apply hf.map_injective
  rw [Measure.inv_def]
  have hfun : f ∘ Inv.inv = Inv.inv ∘ f := by
    funext x
    exact hfinv x
  calc
    Measure.map f (Measure.map Inv.inv mu) =
        Measure.map (f ∘ Inv.inv) mu :=
      Measure.map_map hf.measurable measurable_inv
    _ = Measure.map (Inv.inv ∘ f) mu := congrArg (fun g => Measure.map g mu) hfun
    _ = Measure.map Inv.inv (Measure.map f mu) :=
      (Measure.map_map measurable_inv hf.measurable).symm
    _ = Measure.map f mu := hmap.inv_eq_self

/-- Scalar multiplication does not change inversion invariance. -/
theorem isInvInvariant_smul
    {G : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G]
    (c : ℝ≥0∞) (mu : Measure G) [IsInvInvariant mu] :
    IsInvInvariant (c • mu) := by
  constructor
  rw [Measure.inv_def, Measure.map_smul, Measure.map_inv_eq_self]

/-- The product of two inversion-invariant s-finite measures is inversion
invariant for the componentwise product-group inversion. -/
theorem isInvInvariant_prod
    {G H : Type*} [Group G] [Group H]
    [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableInv G] [MeasurableInv H]
    (mu : Measure G) (nu : Measure H)
    [SFinite mu] [SFinite nu]
    [IsInvInvariant mu] [IsInvInvariant nu] :
    IsInvInvariant (mu.prod nu) := by
  constructor
  rw [Measure.inv_def]
  change Measure.map (Prod.map Inv.inv Inv.inv) (mu.prod nu) = mu.prod nu
  rw [← Measure.map_prod_map mu nu measurable_inv measurable_inv,
    Measure.map_inv_eq_self, Measure.map_inv_eq_self]

/-- A subgroup comap of an inversion-invariant ambient measure is inversion
invariant when the subgroup carries the ambient subtype measurable space. -/
theorem subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    {G : Type*} [Group G] [mG : MeasurableSpace G] [MeasurableInv G]
    (H : Subgroup G) [mH : MeasurableSpace H] [MeasurableInv H]
    {muG : Measure G} [IsInvInvariant muG]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G ↦ x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G)) :
    IsInvInvariant
      (@Measure.comap H G mH mG (fun h : H ↦ (h : G)) muG) := by
  let val : H → G := fun h ↦ (h : G)
  have hcomap : MeasurableSpace.comap val mG = mH :=
    PositiveDefiniteIntegralLattice.subgroup_comap_mspace_of_subtype_mspace
      H hsub_mspace_default
  have hval : @MeasurableEmbedding H G mH mG val :=
    PositiveDefiniteIntegralLattice.subgroup_val_measurableEmbedding_of_comap H hcomap hH
  constructor
  apply Measure.ext
  intro s hs
  rw [Measure.inv_def, Measure.map_apply measurable_inv hs,
    hval.comap_apply muG (Inv.inv ⁻¹' s), hval.comap_apply muG s]
  have himage : val '' (Inv.inv ⁻¹' s) = Inv.inv ⁻¹' (val '' s) := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h⁻¹, hh, ?_⟩
      exact (H.subtype.map_inv h)
    · rintro ⟨h, hh, hvalh⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · simpa using hh
      · simpa using congrArg Inv.inv hvalh
  rw [himage, ← Measure.map_apply measurable_inv
    (hval.measurableSet_image.mpr hs), Measure.map_inv_eq_self]

/-- A monotone directed supremum of inversion-invariant measures is inversion
invariant. -/
theorem directedSup_isInvInvariant
    {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (mu : ι → Measure G) (hmu : Monotone mu)
    (hinv : ∀ i, IsInvInvariant (mu i)) :
    IsInvInvariant (Measure.directedSup mu hmu) := by
  constructor
  apply Measure.ext
  intro s hs
  rw [Measure.inv_def, Measure.map_apply measurable_inv hs,
    Measure.directedSup_apply mu hmu (measurable_inv hs),
    Measure.directedSup_apply mu hmu hs]
  congr 1
  funext i
  letI : IsInvInvariant (mu i) := hinv i
  rw [← Measure.map_apply measurable_inv hs, Measure.map_inv_eq_self]

end MeasureTheory.Measure
