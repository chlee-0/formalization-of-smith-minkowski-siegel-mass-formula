import SMSFormula.RationalCliffordSpinCandidatePlacewiseTranslatedChartMeasure

/-!
# Gluing the placewise Spin chart measures

The translated real and p-adic Spin chart measures form compatible local
measure data on an open cover.  This file performs the purely
measure-theoretic gluing:

* second countability selects a countable family of translated sources;
* `disjointed` turns it into a measurable pairwise-disjoint cover;
* each local source measure is restricted to its assigned piece and mapped
  into the ambient Spin group;
* the countable sum recovers the prescribed measure on every translated
  chart, including charts not selected by the countable subcover.

The construction is generic for an identity-centered local chart of a
continuous group homomorphism and one left-invariant target measure.  Its real
and p-adic specializations define full measures on the corresponding Spin
candidate groups.

This file does not prove left invariance of the glued measures or package
them as Haar measures.  It also does not identify them analytically with the
absolute-value densities of the chosen Spin top forms.  Those are separate
next layers.
-/

noncomputable section

open MeasureTheory
open Topology

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-! ## Countable translated atlas -/

/-- A countable sequence of centers whose translated chart sources cover the
source group. -/
noncomputable def coverCenter (e : OpenPartialHomeomorph G H) : ℕ → G :=
  Classical.choose (eq_open_union_nat (source e) (isOpen_source e))

/-- The selected countable translated sources cover the source group. -/
theorem iUnion_coverCenter_source (e : OpenPartialHomeomorph G H)
    (hone : (1 : G) ∈ e.source) :
    (⋃ k, source e (coverCenter e k)) = Set.univ := by
  have hcover := Classical.choose_spec
    (eq_open_union_nat (source e) (isOpen_source e))
  change (⋃ k, source e
    (Classical.choose (eq_open_union_nat (source e) (isOpen_source e)) k)) =
      Set.univ
  exact hcover.trans <| by
    apply Set.eq_univ_of_forall
    intro g
    exact Set.mem_iUnion.2 ⟨g, self_mem_source e hone g⟩

/-- The measurable disjoint piece assigned to the `k`-th selected translated
source. -/
def coverPiece (e : OpenPartialHomeomorph G H) (k : ℕ) : Set G :=
  disjointed (fun j ↦ source e (coverCenter e j)) k

theorem measurableSet_coverPiece (e : OpenPartialHomeomorph G H) (k : ℕ) :
    MeasurableSet (coverPiece e k) := by
  apply MeasurableSet.disjointed
  intro j
  exact (isOpen_source e (coverCenter e j)).measurableSet

theorem coverPiece_subset_source (e : OpenPartialHomeomorph G H) (k : ℕ) :
    coverPiece e k ⊆ source e (coverCenter e k) :=
  disjointed_subset _ _

theorem pairwiseDisjoint_coverPiece (e : OpenPartialHomeomorph G H) :
    Pairwise (Function.onFun Disjoint (coverPiece e)) :=
  disjoint_disjointed (fun j ↦ source e (coverCenter e j))

theorem iUnion_coverPiece (e : OpenPartialHomeomorph G H)
    (hone : (1 : G) ∈ e.source) :
    (⋃ k, coverPiece e k) = Set.univ := by
  change (⋃ k, disjointed (fun j ↦ source e (coverCenter e j)) k) = Set.univ
  rw [iUnion_disjointed, iUnion_coverCenter_source e hone]

/-! ## Ambient chart measures and overlap compatibility -/

/-- The measure of one translated source, returned to the ambient source
group. -/
def ambientSourceMeasure (f : G →* H) (e : OpenPartialHomeomorph G H)
    (g : G) (μ : Measure H) : Measure G :=
  Measure.map Subtype.val (sourceMeasure f e g μ)

/-- The same-point overlap viewed inside its left translated source. -/
def overlapWithinLeft (e : OpenPartialHomeomorph G H) (g h : G) :
    Set (source e g) :=
  Subtype.val ⁻¹' source e h

/-- The same-point overlap viewed inside its right translated source. -/
def overlapWithinRight (e : OpenPartialHomeomorph G H) (g h : G) :
    Set (source e h) :=
  Subtype.val ⁻¹' source e g

private def overlapLeftHomeomorph (e : OpenPartialHomeomorph G H)
    (g h : G) : SourceOverlap e g h ≃ₜ overlapWithinLeft e g h where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def overlapRightHomeomorph (e : OpenPartialHomeomorph G H)
    (g h : G) : SourceOverlap e g h ≃ₜ overlapWithinRight e g h where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem measurableEmbedding_sourceOverlapToLeft
    (e : OpenPartialHomeomorph G H) (g h : G) :
    MeasurableEmbedding (sourceOverlapToLeft e g h) := by
  let E := overlapLeftHomeomorph e g h
  have hE : MeasurableEmbedding E := E.toMeasurableEquiv.measurableEmbedding
  have hU : IsOpen (overlapWithinLeft e g h) :=
    (isOpen_source e h).preimage continuous_subtype_val
  have hi : MeasurableEmbedding
      (Subtype.val : overlapWithinLeft e g h → source e g) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  simpa [E, Function.comp_def, overlapLeftHomeomorph,
    sourceOverlapToLeft] using hi.comp hE

theorem measurableEmbedding_sourceOverlapToRight
    (e : OpenPartialHomeomorph G H) (g h : G) :
    MeasurableEmbedding (sourceOverlapToRight e g h) := by
  let E := overlapRightHomeomorph e g h
  have hE : MeasurableEmbedding E := E.toMeasurableEquiv.measurableEmbedding
  have hU : IsOpen (overlapWithinRight e g h) :=
    (isOpen_source e g).preimage continuous_subtype_val
  have hi : MeasurableEmbedding
      (Subtype.val : overlapWithinRight e g h → source e h) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  simpa [E, Function.comp_def, overlapRightHomeomorph,
    sourceOverlapToRight] using hi.comp hE

theorem range_sourceOverlapToLeft (e : OpenPartialHomeomorph G H)
    (g h : G) :
    Set.range (sourceOverlapToLeft e g h) = overlapWithinLeft e g h := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2.2
  · intro hx
    exact ⟨⟨x.1, ⟨x.2, hx⟩⟩, rfl⟩

theorem range_sourceOverlapToRight (e : OpenPartialHomeomorph G H)
    (g h : G) :
    Set.range (sourceOverlapToRight e g h) = overlapWithinRight e g h := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2.1
  · intro hx
    exact ⟨⟨x.1, ⟨hx, x.2⟩⟩, rfl⟩

/-- Two translated charts induce the same ambient measure after restriction
to their same-point overlap. -/
theorem restrict_ambientSourceMeasure_overlap (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (g h : G) (μ : Measure H) :
    (ambientSourceMeasure f e g μ).restrict (source e h) =
      (ambientSourceMeasure f e h μ).restrict (source e g) := by
  let νg := sourceMeasure f e g μ
  let νh := sourceMeasure f e h μ
  let iL := sourceOverlapToLeft e g h
  let iR := sourceOverlapToRight e g h
  let jg : source e g → G := Subtype.val
  let jh : source e h → G := Subtype.val
  let jo : SourceOverlap e g h → G := Subtype.val
  have hiL : MeasurableEmbedding iL :=
    measurableEmbedding_sourceOverlapToLeft e g h
  have hiR : MeasurableEmbedding iR :=
    measurableEmbedding_sourceOverlapToRight e g h
  have hUg : MeasurableSet (source e g) := (isOpen_source e g).measurableSet
  have hUh : MeasurableSet (source e h) := (isOpen_source e h).measurableSet
  change (Measure.map jg νg).restrict (source e h) =
    (Measure.map jh νh).restrict (source e g)
  calc
    (Measure.map jg νg).restrict (source e h) =
        Measure.map jg (νg.restrict (overlapWithinLeft e g h)) :=
      Measure.restrict_map continuous_subtype_val.measurable hUh
    _ = Measure.map jg (Measure.map iL (Measure.comap iL νg)) := by
      rw [hiL.map_comap, range_sourceOverlapToLeft]
    _ = Measure.map jo (Measure.comap iL νg) := by
      rw [Measure.map_map continuous_subtype_val.measurable hiL.measurable]
      congr 1
    _ = Measure.map jo (Measure.comap iR νh) := by
      rw [comap_sourceMeasure_overlap f e hfe g h μ]
    _ = Measure.map jh (Measure.map iR (Measure.comap iR νh)) := by
      rw [Measure.map_map continuous_subtype_val.measurable hiR.measurable]
      congr 1
    _ = Measure.map jh (νh.restrict (overlapWithinRight e g h)) := by
      rw [hiR.map_comap, range_sourceOverlapToRight]
    _ = (Measure.map jh νh).restrict (source e g) :=
      (Measure.restrict_map continuous_subtype_val.measurable hUg).symm

/-! ## Disjoint contributions and the glued measure -/

/-- The assigned disjoint piece viewed inside its selected translated source. -/
def coverPieceWithinSource (e : OpenPartialHomeomorph G H) (k : ℕ) :
    Set (source e (coverCenter e k)) :=
  Subtype.val ⁻¹' coverPiece e k

theorem measurableSet_coverPieceWithinSource
    (e : OpenPartialHomeomorph G H) (k : ℕ) :
    MeasurableSet (coverPieceWithinSource e k) :=
  (measurableSet_coverPiece e k).preimage continuous_subtype_val.measurable

/-- The contribution of one disjoint chart piece, returned to the ambient
source group. -/
def coverPieceMeasure (f : G →* H) (e : OpenPartialHomeomorph G H)
    (μ : Measure H) (k : ℕ) : Measure G :=
  Measure.map Subtype.val
    ((sourceMeasure f e (coverCenter e k) μ).restrict
      (coverPieceWithinSource e k))

theorem coverPieceMeasure_eq_restrict_ambient
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (μ : Measure H) (k : ℕ) :
    coverPieceMeasure f e μ k =
      (ambientSourceMeasure f e (coverCenter e k) μ).restrict
        (coverPiece e k) := by
  symm
  exact Measure.restrict_map continuous_subtype_val.measurable
    (measurableSet_coverPiece e k)

/-- The globally glued source measure. -/
def gluedMeasure (f : G →* H) (e : OpenPartialHomeomorph G H)
    (μ : Measure H) : Measure G :=
  Measure.sum (coverPieceMeasure f e μ)

private theorem measure_eq_sum_restrict_coverPiece
    (e : OpenPartialHomeomorph G H) (hone : (1 : G) ∈ e.source)
    (ν : Measure G) :
    ν = Measure.sum (fun k ↦ ν.restrict (coverPiece e k)) := by
  calc
    ν = ν.restrict Set.univ := Measure.restrict_univ.symm
    _ = ν.restrict (⋃ k, coverPiece e k) := by
      rw [iUnion_coverPiece e hone]
    _ = Measure.sum (fun k ↦ ν.restrict (coverPiece e k)) :=
      Measure.restrict_iUnion (pairwiseDisjoint_coverPiece e)
        (measurableSet_coverPiece e)

theorem restrict_coverPieceMeasure_source
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (μ : Measure H) (k : ℕ) (g : G) :
    (coverPieceMeasure f e μ k).restrict (source e g) =
      (ambientSourceMeasure f e g μ).restrict (coverPiece e k) := by
  let c := coverCenter e k
  let P := coverPiece e k
  let U := source e g
  let W := source e c
  have hP : MeasurableSet P := measurableSet_coverPiece e k
  have hU : MeasurableSet U := (isOpen_source e g).measurableSet
  have hPW : P ⊆ W := coverPiece_subset_source e k
  rw [coverPieceMeasure_eq_restrict_ambient]
  calc
    ((ambientSourceMeasure f e c μ).restrict P).restrict U =
        ((ambientSourceMeasure f e c μ).restrict U).restrict P := by
      rw [Measure.restrict_restrict hU, Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_comm _ _
    _ = ((ambientSourceMeasure f e g μ).restrict W).restrict P := by
      rw [restrict_ambientSourceMeasure_overlap f e hfe c g μ]
    _ = (ambientSourceMeasure f e g μ).restrict P := by
      rw [Measure.restrict_restrict hP]
      congr 1
      exact Set.inter_eq_left.mpr hPW

/-- The glued measure restricts to every translated chart source as the
ambient measure induced by that chart. -/
theorem restrict_gluedMeasure_source (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (hone : (1 : G) ∈ e.source) (μ : Measure H) (g : G) :
    (gluedMeasure f e μ).restrict (source e g) =
      ambientSourceMeasure f e g μ := by
  let U := source e g
  let ν := ambientSourceMeasure f e g μ
  let P := coverPiece e
  calc
    (gluedMeasure f e μ).restrict U =
        Measure.sum (fun k ↦ (coverPieceMeasure f e μ k).restrict U) := by
      ext s hs
      rw [Measure.restrict_apply hs, gluedMeasure,
        Measure.sum_apply _ (hs.inter (isOpen_source e g).measurableSet),
        Measure.sum_apply _ hs]
      congr 1
      funext k
      rw [Measure.restrict_apply hs]
    _ = Measure.sum (fun k ↦ ν.restrict (P k)) := by
      congr 1
      funext k
      exact restrict_coverPieceMeasure_source f e hfe μ k g
    _ = ν := (measure_eq_sum_restrict_coverPiece e hone ν).symm

/-- Pulling the glued measure back through the inclusion of any translated
source recovers its prescribed local source measure. -/
theorem comap_gluedMeasure_source (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (hone : (1 : G) ∈ e.source) (μ : Measure H) (g : G) :
    Measure.comap Subtype.val (gluedMeasure f e μ) =
      sourceMeasure f e g μ := by
  let i : source e g → G := Subtype.val
  have hi : MeasurableEmbedding i :=
    MeasurableEmbedding.subtype_coe (isOpen_source e g).measurableSet
  apply hi.map_injective
  calc
    Measure.map i (Measure.comap i (gluedMeasure f e μ)) =
        (gluedMeasure f e μ).restrict (Set.range i) := hi.map_comap _
    _ = (gluedMeasure f e μ).restrict (source e g) := by
      congr 1
      exact Subtype.range_val
    _ = ambientSourceMeasure f e g μ :=
      restrict_gluedMeasure_source f e hfe hone μ g
    _ = Measure.map i (sourceMeasure f e g μ) := rfl

/-! ## Local finiteness and open positivity -/

private theorem isLocallyFiniteMeasure_map_homeomorph
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (E : X ≃ₜ Y) (ν : Measure X) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (Measure.map E ν) := by
  refine ⟨fun y ↦ ?_⟩
  rcases ν.exists_isOpen_measure_lt_top (E.symm y) with
    ⟨U, hyU, hU, hνU⟩
  refine ⟨E.symm ⁻¹' U,
    (hU.preimage E.symm.continuous).mem_nhds hyU, ?_⟩
  rw [Measure.map_apply E.measurable
    (hU.preimage E.symm.continuous).measurableSet]
  have hpreimage : E ⁻¹' (E.symm ⁻¹' U) = U := by
    ext x
    simp
  rw [hpreimage]
  exact hνU

/-- Local finiteness of the identity source measure propagates to every
translated source. -/
theorem sourceMeasure_isLocallyFinite_of_identity
    (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ]
    [IsLocallyFiniteMeasure (identitySourceMeasure e μ)] :
    IsLocallyFiniteMeasure (sourceMeasure f e g μ) := by
  have hmap : IsLocallyFiniteMeasure
      (Measure.map (sourceLeftHomeomorph e g)
        (identitySourceMeasure e μ)) :=
    isLocallyFiniteMeasure_map_homeomorph
      (sourceLeftHomeomorph e g) (identitySourceMeasure e μ)
  rw [map_identitySourceMeasure_sourceLeftHomeomorph f e g μ] at hmap
  exact hmap

/-- Open positivity of the identity source measure propagates to every
translated source. -/
theorem sourceMeasure_isOpenPosMeasure_of_identity
    (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ]
    [Measure.IsOpenPosMeasure (identitySourceMeasure e μ)] :
    Measure.IsOpenPosMeasure (sourceMeasure f e g μ) := by
  have hmap : Measure.IsOpenPosMeasure
      (Measure.map (sourceLeftHomeomorph e g)
        (identitySourceMeasure e μ)) :=
    (sourceLeftHomeomorph e g).continuous.isOpenPosMeasure_map
      (sourceLeftHomeomorph e g).surjective
  rw [map_identitySourceMeasure_sourceLeftHomeomorph f e g μ] at hmap
  exact hmap

/-- If every translated source measure is locally finite, so is the measure
glued from the countable atlas. -/
theorem gluedMeasure_isLocallyFinite
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (μ : Measure H)
    (hloc : ∀ g, IsLocallyFiniteMeasure (sourceMeasure f e g μ)) :
    IsLocallyFiniteMeasure (gluedMeasure f e μ) := by
  refine ⟨fun x ↦ ?_⟩
  let ν := sourceMeasure f e x μ
  letI : IsLocallyFiniteMeasure ν := hloc x
  let xs : source e x := ⟨x, self_mem_source e hone x⟩
  rcases ν.exists_isOpen_measure_lt_top xs with ⟨U, hxU, hU, hνU⟩
  let j : source e x → G := Subtype.val
  let W := j '' U
  have hj : IsOpenEmbedding j :=
    (isOpen_source e x).isOpenEmbedding_subtypeVal
  have hW : IsOpen W := hj.isOpenMap U hU
  have hxW : x ∈ W := ⟨xs, hxU, rfl⟩
  refine ⟨W, hW.mem_nhds hxW, ?_⟩
  have hWS : W ⊆ source e x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  calc
    gluedMeasure f e μ W =
        (gluedMeasure f e μ).restrict (source e x) W := by
      rw [Measure.restrict_apply hW.measurableSet,
        Set.inter_eq_left.mpr hWS]
    _ = ambientSourceMeasure f e x μ W := by
      rw [restrict_gluedMeasure_source f e hfe hone μ x]
    _ = ν U := by
      rw [ambientSourceMeasure,
        Measure.map_apply continuous_subtype_val.measurable hW.measurableSet]
      congr 1
      exact Set.preimage_image_eq U hj.injective
    _ < (⊤ : ENNReal) := hνU

/-- If every translated source measure is positive on nonempty open sets, so
is the measure glued from the countable atlas. -/
theorem gluedMeasure_isOpenPosMeasure
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (hone : (1 : G) ∈ e.source)
    (μ : Measure H)
    (hpos : ∀ g, Measure.IsOpenPosMeasure (sourceMeasure f e g μ)) :
    Measure.IsOpenPosMeasure (gluedMeasure f e μ) := by
  refine ⟨fun U hU hUne ↦ ?_⟩
  rcases hUne with ⟨x, hxU⟩
  let ν := sourceMeasure f e x μ
  letI : Measure.IsOpenPosMeasure ν := hpos x
  let W : Set (source e x) := Subtype.val ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty :=
    ⟨⟨x, self_mem_source e hone x⟩, hxU⟩
  exact ne_of_gt <| calc
    0 < ν W := hW.measure_pos ν hWne
    _ = ambientSourceMeasure f e x μ U := by
      rw [ambientSourceMeasure,
        Measure.map_apply continuous_subtype_val.measurable hU.measurableSet]
    _ = (gluedMeasure f e μ).restrict (source e x) U := by
      rw [restrict_gluedMeasure_source f e hfe hone μ x]
    _ ≤ gluedMeasure f e μ U := Measure.restrict_apply_le (source e x) U

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

open MeasureTheory.TranslatedHomChart

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance chartGluingRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance chartGluingRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance chartGluingPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance chartGluingPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

local instance chartGluingRealCarrierBorelSpace :
    BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩

local instance chartGluingPadicCarrierBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-! ## Real glued measure -/

/-- The full real Spin measure glued from the translated local chart
measures. -/
noncomputable def realCliffordSpinCandidateChartGluedMeasure :
    Measure V.RealCliffordSpinCandidateGroup :=
  gluedMeasure V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realInvariantDifferentialGroupMeasure

set_option backward.isDefEq.respectTransparency false in
theorem restrict_realCliffordSpinCandidateChartGluedMeasure_source
    (g : V.RealCliffordSpinCandidateGroup) :
    V.realCliffordSpinCandidateChartGluedMeasure.restrict
        (V.RealCliffordSpinCandidateTranslatedChartSource g) =
      Measure.map Subtype.val
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure g) :=
  restrict_gluedMeasure_source
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure g

set_option backward.isDefEq.respectTransparency false in
theorem comap_realCliffordSpinCandidateChartGluedMeasure_source
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure.comap Subtype.val V.realCliffordSpinCandidateChartGluedMeasure =
      V.realCliffordSpinCandidateTranslatedChartSourceMeasure g :=
  comap_gluedMeasure_source
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure g

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateTranslatedChartSourceMeasure_isLocallyFinite
    (g : V.RealCliffordSpinCandidateGroup) :
    IsLocallyFiniteMeasure
      (V.realCliffordSpinCandidateTranslatedChartSourceMeasure g) := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : IsLocallyFiniteMeasure
      (identitySourceMeasure V.realCliffordSpinCandidateIdentityChart
        V.realInvariantDifferentialGroupMeasure) := by
    simpa [identitySourceMeasure, identityTargetMeasure,
      realCliffordSpinCandidateIdentityChartSourceMeasure,
      realCliffordSpinCandidateIdentityChartTargetMeasure] using
      V.realCliffordSpinCandidateIdentityChartSourceMeasure_isLocallyFinite
  exact sourceMeasure_isLocallyFinite_of_identity
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g
    V.realInvariantDifferentialGroupMeasure

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateTranslatedChartSourceMeasure_isOpenPosMeasure
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure.IsOpenPosMeasure
      (V.realCliffordSpinCandidateTranslatedChartSourceMeasure g) := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : Measure.IsOpenPosMeasure
      (identitySourceMeasure V.realCliffordSpinCandidateIdentityChart
        V.realInvariantDifferentialGroupMeasure) := by
    simpa [identitySourceMeasure, identityTargetMeasure,
      realCliffordSpinCandidateIdentityChartSourceMeasure,
      realCliffordSpinCandidateIdentityChartTargetMeasure] using
      V.realCliffordSpinCandidateIdentityChartSourceMeasure_isOpenPosMeasure
  exact sourceMeasure_isOpenPosMeasure_of_identity
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g
    V.realInvariantDifferentialGroupMeasure

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure V.realCliffordSpinCandidateChartGluedMeasure :=
  gluedMeasure_isLocallyFinite
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure
    V.realCliffordSpinCandidateTranslatedChartSourceMeasure_isLocallyFinite

set_option backward.isDefEq.respectTransparency false in
theorem realCliffordSpinCandidateChartGluedMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure V.realCliffordSpinCandidateChartGluedMeasure :=
  gluedMeasure_isOpenPosMeasure
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe
    V.one_mem_realCliffordSpinCandidateIdentityChart_source
    V.realInvariantDifferentialGroupMeasure
    V.realCliffordSpinCandidateTranslatedChartSourceMeasure_isOpenPosMeasure

/-! ## P-adic glued measures -/

/-- The full p-adic Spin measure glued from the translated local chart
measures. -/
noncomputable def padicCliffordSpinCandidateChartGluedMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.PadicCliffordSpinCandidateGroup p) :=
  gluedMeasure (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicInvariantDifferentialGroupMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_padicCliffordSpinCandidateChartGluedMeasure_source
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.PadicCliffordSpinCandidateGroup p) :
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
        (V.PadicCliffordSpinCandidateTranslatedChartSource p g) =
      Measure.map Subtype.val
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g) :=
  restrict_gluedMeasure_source
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p) g

set_option backward.isDefEq.respectTransparency false in
theorem comap_padicCliffordSpinCandidateChartGluedMeasure_source
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure.comap Subtype.val
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
      V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g :=
  comap_gluedMeasure_source
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p) g

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateTranslatedChartSourceMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.PadicCliffordSpinCandidateGroup p) :
    IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  letI : IsLocallyFiniteMeasure
      (identitySourceMeasure (V.padicCliffordSpinCandidateIdentityChart p)
        (V.padicInvariantDifferentialGroupMeasure p)) := by
    simpa [identitySourceMeasure, identityTargetMeasure,
      padicCliffordSpinCandidateIdentityChartSourceMeasure,
      padicCliffordSpinCandidateIdentityChartTargetMeasure] using
      V.padicCliffordSpinCandidateIdentityChartSourceMeasure_isLocallyFinite p
  exact sourceMeasure_isLocallyFinite_of_identity
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g
    (V.padicInvariantDifferentialGroupMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateTranslatedChartSourceMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure.IsOpenPosMeasure
      (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  letI : Measure.IsOpenPosMeasure
      (identitySourceMeasure (V.padicCliffordSpinCandidateIdentityChart p)
        (V.padicInvariantDifferentialGroupMeasure p)) := by
    simpa [identitySourceMeasure, identityTargetMeasure,
      padicCliffordSpinCandidateIdentityChartSourceMeasure,
      padicCliffordSpinCandidateIdentityChartTargetMeasure] using
      V.padicCliffordSpinCandidateIdentityChartSourceMeasure_isOpenPosMeasure p
  exact sourceMeasure_isOpenPosMeasure_of_identity
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g
    (V.padicInvariantDifferentialGroupMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
  gluedMeasure_isLocallyFinite
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p)
    (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure_isLocallyFinite p)

set_option backward.isDefEq.respectTransparency false in
theorem padicCliffordSpinCandidateChartGluedMeasure_isOpenPosMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsOpenPosMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
  gluedMeasure_isOpenPosMeasure
    (G := V.PadicCliffordSpinCandidateGroup p) (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
    (V.padicInvariantDifferentialGroupMeasure p)
    (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure_isOpenPosMeasure p)

end RationalQuadraticSpaceMatrix
