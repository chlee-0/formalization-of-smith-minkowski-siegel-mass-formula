import SMSFormula.AdelicWeilQuotient

/-!
# Adelic left-right double cosets

This module contains the project-local left-right double-coset relation,
double quotient, selected fibers, finite fiber additivity, generic translated
slices, and representative-slice periodization helpers used before the
finite-adelic orthogonal presentation is introduced.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u
universe v
universe w

variable {n : ℕ}

open MeasureTheory
open scoped ENNReal

/-! ## Left-right double cosets -/

/-- The left-right double-coset relation for subgroups `Gamma` and `H` of a group
`G`: two elements are related when they differ by a left factor from `Gamma` and a
right factor from `H`. -/
def IsLeftRightDoubleCosetRelated {G : Type u} [Group G]
    (Gamma H : Subgroup G) (x y : G) : Prop :=
  ∃ gamma : Gamma, ∃ h : H, y = (gamma : G) * x * (h : G)

lemma IsLeftRightDoubleCosetRelated.refl {G : Type u} [Group G]
    (Gamma H : Subgroup G) (x : G) :
    IsLeftRightDoubleCosetRelated Gamma H x x := by
  refine ⟨1, 1, ?_⟩
  simp

lemma IsLeftRightDoubleCosetRelated.symm {G : Type u} [Group G]
    {Gamma H : Subgroup G} {x y : G}
    (hxy : IsLeftRightDoubleCosetRelated Gamma H x y) :
    IsLeftRightDoubleCosetRelated Gamma H y x := by
  rcases hxy with ⟨gamma, h, rfl⟩
  refine ⟨gamma⁻¹, h⁻¹, ?_⟩
  simp [mul_assoc]

lemma IsLeftRightDoubleCosetRelated.trans {G : Type u} [Group G]
    {Gamma H : Subgroup G} {x y z : G}
    (hxy : IsLeftRightDoubleCosetRelated Gamma H x y)
    (hyz : IsLeftRightDoubleCosetRelated Gamma H y z) :
    IsLeftRightDoubleCosetRelated Gamma H x z := by
  rcases hxy with ⟨gamma1, h1, rfl⟩
  rcases hyz with ⟨gamma2, h2, rfl⟩
  refine ⟨gamma2 * gamma1, h1 * h2, ?_⟩
  simp [mul_assoc]

/-- The setoid attached to the left-right double-coset relation. -/
def leftRightDoubleCosetSetoid {G : Type u} [Group G]
    (Gamma H : Subgroup G) : Setoid G where
  r := IsLeftRightDoubleCosetRelated Gamma H
  iseqv := ⟨
    fun x => IsLeftRightDoubleCosetRelated.refl Gamma H x,
    fun {_x _y} h => IsLeftRightDoubleCosetRelated.symm h,
    fun {_x _y _z} hxy hyz => IsLeftRightDoubleCosetRelated.trans hxy hyz⟩

/-- The abstract double-coset set `Gamma \ G / H`. -/
def leftRightDoubleCosetSet {G : Type u} [Group G]
    (Gamma H : Subgroup G) : Type u :=
  Quot (leftRightDoubleCosetSetoid Gamma H)

lemma leftRightDoubleCoset_mk_eq_iff {G : Type u} [Group G]
    (Gamma H : Subgroup G) (x y : G) :
    Quot.mk (leftRightDoubleCosetSetoid Gamma H) x =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) y ↔
      IsLeftRightDoubleCosetRelated Gamma H x y := by
  constructor
  · intro hxy
    simpa [leftRightDoubleCosetSetoid] using Quotient.exact hxy
  · intro hxy
    exact Quotient.sound hxy

/-- The canonical projection from the left quotient `Gamma \ G` to the
left-right double quotient `Gamma \ G / H`. -/
def leftCosetToLeftRightDoubleCoset {G : Type u} [Group G]
    (Gamma H : Subgroup G) :
    leftCosetSet Gamma → leftRightDoubleCosetSet Gamma H :=
  Quot.map id (by
    intro x y hxy
    rcases hxy with ⟨gamma, rfl⟩
    refine ⟨gamma, 1, ?_⟩
    simp)

lemma leftCosetToLeftRightDoubleCoset_mk {G : Type u} [Group G]
    (Gamma H : Subgroup G) (x : G) :
    leftCosetToLeftRightDoubleCoset Gamma H
        (Quot.mk (leftCosetSetoid Gamma) x) =
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) x := by
  rfl

/-- The double-coset projection is measurable for the quotient measurable
space induced as the map of the left-quotient measurable space. -/
theorem leftCosetToLeftRightDoubleCoset_measurable_map {G : Type u} [Group G]
    (Gamma H : Subgroup G) [mX : MeasurableSpace (leftCosetSet Gamma)] :
    @Measurable (leftCosetSet Gamma) (leftRightDoubleCosetSet Gamma H) mX
      (MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
      (leftCosetToLeftRightDoubleCoset Gamma H) := by
  exact measurable_iff_comap_le.2
    (MeasurableSpace.comap_le_iff_le_map.2 le_rfl)

/-- If the double-coset quotient measurable space is the map of the left
quotient measurable space, then the double-coset projection is measurable. -/
theorem leftCosetToLeftRightDoubleCoset_measurable_of_map_mspace
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    (hmap :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX) :
    @Measurable (leftCosetSet Gamma) (leftRightDoubleCosetSet Gamma H)
      mX mC (leftCosetToLeftRightDoubleCoset Gamma H) := by
  rw [hmap]
  exact leftCosetToLeftRightDoubleCoset_measurable_map Gamma H

/-- The piece of the left quotient `Gamma \ G` lying over one double coset in
`Gamma \ G / H`.  This is the quotient-side set whose measure is summed in the
finite-additivity source. -/
def leftRightDoubleCosetPiece {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H) : Type u :=
  { X : leftCosetSet Gamma // leftCosetToLeftRightDoubleCoset Gamma H X = C }

/-- The quotient-side subset of `Gamma \ G` lying over one double coset. -/
def leftRightDoubleCosetPieceSet {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H) :
    Set (leftCosetSet Gamma) :=
  { X | leftCosetToLeftRightDoubleCoset Gamma H X = C }

/-- The double-coset fibers cover the left quotient. -/
theorem leftRightDoubleCosetPieceSet_iUnion {G : Type u} [Group G]
    (Gamma H : Subgroup G) :
    (⋃ C : leftRightDoubleCosetSet Gamma H,
        leftRightDoubleCosetPieceSet Gamma H C) = Set.univ := by
  ext X
  constructor
  · intro _hX
    exact Set.mem_univ X
  · intro _hX
    exact Set.mem_iUnion.2
      ⟨leftCosetToLeftRightDoubleCoset Gamma H X, rfl⟩

/-- Distinct double-coset fibers in the left quotient are disjoint. -/
theorem leftRightDoubleCosetPieceSet_disjoint {G : Type u} [Group G]
    (Gamma H : Subgroup G) {C D : leftRightDoubleCosetSet Gamma H}
    (hCD : C ≠ D) :
    Disjoint (leftRightDoubleCosetPieceSet Gamma H C)
      (leftRightDoubleCosetPieceSet Gamma H D) := by
  rw [Set.disjoint_left]
  intro X hXC hXD
  exact hCD (hXC.symm.trans hXD)

/-- Finite measure additivity over the double-coset fibers of the left
quotient. -/
theorem leftRightDoubleCosetPieceSet_measure_univ_eq_sum
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [Fintype (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSpace (leftCosetSet Gamma)]
    (μ : Measure (leftCosetSet Gamma))
    (hmeas : ∀ C : leftRightDoubleCosetSet Gamma H,
      MeasurableSet (leftRightDoubleCosetPieceSet Gamma H C)) :
    μ Set.univ =
      ∑ C : leftRightDoubleCosetSet Gamma H,
        μ (leftRightDoubleCosetPieceSet Gamma H C) := by
  exact
    measure_univ_eq_sum_of_fintype_iUnion_disjoint μ
      (fun C : leftRightDoubleCosetSet Gamma H =>
        leftRightDoubleCosetPieceSet Gamma H C)
      (leftRightDoubleCosetPieceSet_iUnion Gamma H)
      (by
        intro C D hCD
        exact leftRightDoubleCosetPieceSet_disjoint Gamma H hCD)
      hmeas

/-- Real-valued finite additivity over the double-coset fibers of the left
quotient.

Once the measure of each fiber is identified with `ENNReal.ofReal (v C)`, the
real total mass of the left quotient is the finite sum of the real fiber
volumes.  This is the generic finite-additivity algebra used by the
finite-adelic quotient-volume comparison. -/
theorem leftRightDoubleCosetPieceSet_measure_univ_toReal_eq_sum
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [Fintype (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSpace (leftCosetSet Gamma)]
    (μ : Measure (leftCosetSet Gamma))
    (v : leftRightDoubleCosetSet Gamma H → ℝ)
    (hmeas : ∀ C : leftRightDoubleCosetSet Gamma H,
      MeasurableSet (leftRightDoubleCosetPieceSet Gamma H C))
    (hv_nonneg : ∀ C : leftRightDoubleCosetSet Gamma H, 0 ≤ v C)
    (hpiece : ∀ C : leftRightDoubleCosetSet Gamma H,
      μ (leftRightDoubleCosetPieceSet Gamma H C) = ENNReal.ofReal (v C)) :
    (μ Set.univ).toReal =
      ∑ C : leftRightDoubleCosetSet Gamma H, v C := by
  have hadd :
      μ Set.univ =
        ∑ C : leftRightDoubleCosetSet Gamma H,
          μ (leftRightDoubleCosetPieceSet Gamma H C) :=
    leftRightDoubleCosetPieceSet_measure_univ_eq_sum Gamma H μ hmeas
  have hsum_ofReal :
      ENNReal.ofReal (∑ C : leftRightDoubleCosetSet Gamma H, v C) =
        ∑ C : leftRightDoubleCosetSet Gamma H, ENNReal.ofReal (v C) := by
    exact
      ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (f := v) (by
          intro C _
          exact hv_nonneg C)
  have hsum_nonneg :
      0 ≤ ∑ C : leftRightDoubleCosetSet Gamma H, v C :=
    Finset.sum_nonneg fun C _ => hv_nonneg C
  calc
    (μ Set.univ).toReal =
        (∑ C : leftRightDoubleCosetSet Gamma H,
          μ (leftRightDoubleCosetPieceSet Gamma H C)).toReal := by
          rw [hadd]
    _ =
        (∑ C : leftRightDoubleCosetSet Gamma H,
          ENNReal.ofReal (v C)).toReal := by
          rw [Finset.sum_congr rfl fun C _ => hpiece C]
    _ =
        (ENNReal.ofReal (∑ C : leftRightDoubleCosetSet Gamma H, v C)).toReal := by
          rw [hsum_ofReal]
    _ = ∑ C : leftRightDoubleCosetSet Gamma H, v C := by
          exact ENNReal.toReal_ofReal hsum_nonneg

/-- A double-coset fiber in the left quotient is measurable once the projection
`Gamma \ G → Gamma \ G / H` is measurable and the target singleton is
measurable. -/
theorem leftRightDoubleCosetPieceSet_measurable_of_measurable_projection
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [MeasurableSpace (leftCosetSet Gamma)]
    [MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    (C : leftRightDoubleCosetSet Gamma H)
    (hproj : Measurable (leftCosetToLeftRightDoubleCoset Gamma H))
    (hC : MeasurableSet ({C} : Set (leftRightDoubleCosetSet Gamma H))) :
    MeasurableSet (leftRightDoubleCosetPieceSet Gamma H C) := by
  change
    MeasurableSet
      ((leftCosetToLeftRightDoubleCoset Gamma H) ⁻¹'
        ({C} : Set (leftRightDoubleCosetSet Gamma H)))
  exact hproj hC

/-- A double-coset fiber is measurable for the standard map measurable
structure on `Gamma \ G / H` once singleton double cosets are measurable. -/
theorem leftRightDoubleCosetPieceSet_measurable_of_map_mspace_singleton
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hmap :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    (C : leftRightDoubleCosetSet Gamma H) :
    MeasurableSet (leftRightDoubleCosetPieceSet Gamma H C) := by
  exact
    leftRightDoubleCosetPieceSet_measurable_of_measurable_projection
      Gamma H C
      (leftCosetToLeftRightDoubleCoset_measurable_of_map_mspace Gamma H hmap)
      (measurableSet_singleton C)

/-- Real finite additivity over the double-coset fibers for the standard
map measurable structure on the double quotient.

In this standard setup the fiber measurability needed for finite additivity is
formal from the map measurable structure and measurable singleton double
cosets.  A concrete quotient-volume source only has to identify the real mass
of each fiber. -/
theorem leftRightDoubleCosetPieceSet_measure_univ_toReal_eq_sum_of_map_mspace_singleton
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    [Fintype (leftRightDoubleCosetSet Gamma H)]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hmap :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    (μ : Measure (leftCosetSet Gamma))
    (v : leftRightDoubleCosetSet Gamma H → ℝ)
    (hv_nonneg : ∀ C : leftRightDoubleCosetSet Gamma H, 0 ≤ v C)
    (hpiece : ∀ C : leftRightDoubleCosetSet Gamma H,
      μ (leftRightDoubleCosetPieceSet Gamma H C) = ENNReal.ofReal (v C)) :
    (μ Set.univ).toReal =
      ∑ C : leftRightDoubleCosetSet Gamma H, v C := by
  exact
    leftRightDoubleCosetPieceSet_measure_univ_toReal_eq_sum Gamma H μ v
      (fun C =>
        leftRightDoubleCosetPieceSet_measurable_of_map_mspace_singleton
          Gamma H hmap C)
      hv_nonneg hpiece

/-- The value map from a subtype is injective. -/
theorem subtype_val_injective {α : Type u} {p : α → Prop} :
    Function.Injective (fun x : {x : α // p x} => (x : α)) :=
  fun _ _ h => Subtype.ext h

/-- The range of the value map from a subtype is the defining predicate as an
ambient set. -/
theorem subtype_val_range {α : Type u} {p : α → Prop} :
    Set.range (fun x : {x : α // p x} => (x : α)) = {x | p x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The value map from a selected left-quotient piece has range exactly the
corresponding fiber subset of the ambient left quotient. -/
theorem leftRightDoubleCosetPiece_val_range {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H) :
    Set.range (fun X : leftRightDoubleCosetPiece Gamma H C => X.1) =
      leftRightDoubleCosetPieceSet Gamma H C := by
  exact subtype_val_range

/-- The value map from a selected left-quotient piece is injective. -/
theorem leftRightDoubleCosetPiece_val_injective {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H) :
    Function.Injective (fun X : leftRightDoubleCosetPiece Gamma H C => X.1) :=
  subtype_val_injective

/-- The default subtype measurable-space presentation gives the natural comap
measurable-space field along the subtype inclusion. -/
theorem subtype_comap_mspace_of_subtype_mspace {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα)) :
    MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS := by
  calc
    MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα =
        (@Subtype.instMeasurableSpace α p mα) := rfl
    _ = mS := hsub_mspace_default.symm

/-- The natural comap measurable-space field along a subtype inclusion is the
ordinary subtype measurable space. -/
theorem subtype_mspace_of_comap_mspace {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    (hcomap :
      MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS) :
    mS = (@Subtype.instMeasurableSpace α p mα) := by
  calc
    mS =
        MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα :=
      hcomap.symm
    _ = (@Subtype.instMeasurableSpace α p mα) := rfl

/-- A subtype measure given by the transported default-subtype comap
presentation is the ordinary comap measure for the stored measurable-space
instance. -/
theorem subtype_measure_eq_comap_of_subtype_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α} {μS : @Measure {x : α // p x} mS}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hmeasure_comap_default :
      μS =
        hsub_mspace_default.symm ▸
          (@Measure.comap {x : α // p x} α
            (@Subtype.instMeasurableSpace α p mα)
            mα
            (fun x : {x : α // p x} => (x : α)) μα)) :
    μS =
      @Measure.comap {x : α // p x} α mS mα
        (fun x : {x : α // p x} => (x : α)) μα := by
  exact hmeasure_comap_default.trans
    (measure_comap_congr_source_mspace hsub_mspace_default.symm
      (fun x : {x : α // p x} => (x : α)) μα)

/-- A subtype measure given by the ordinary comap measure for the stored
measurable-space instance is the transported default-subtype comap measure.

This is the converse presentation bridge to
`subtype_measure_eq_comap_of_subtype_comap`: concrete presentations that first
state the natural `Measure.comap` field can recover the exact transported
default-subtype field expected by subtype/comap package constructors. -/
theorem subtype_measure_eq_subtype_comap_of_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α} {μS : @Measure {x : α // p x} mS}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hmeasure_comap :
      μS =
        @Measure.comap {x : α // p x} α mS mα
          (fun x : {x : α // p x} => (x : α)) μα) :
    μS =
      hsub_mspace_default.symm ▸
        (@Measure.comap {x : α // p x} α
          (@Subtype.instMeasurableSpace α p mα)
          mα
          (fun x : {x : α // p x} => (x : α)) μα) := by
  exact hmeasure_comap.trans
    (measure_comap_congr_source_mspace hsub_mspace_default.symm
      (fun x : {x : α // p x} => (x : α)) μα).symm

/-- The value map from a subtype is a measurable embedding when the subtype
has the comap measurable structure from the ambient type and the subtype range
is ambient-measurable. -/
theorem subtype_val_measurableEmbedding_of_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    (hcomap :
      MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS)
    (hp : @MeasurableSet α mα {x | p x}) :
    @MeasurableEmbedding {x : α // p x} α mS mα
      (fun x : {x : α // p x} => (x : α)) := by
  refine
    measurableEmbedding_of_comap_eq_of_injective_of_measurableSet_range
      ?_ hcomap ?_
  · exact subtype_val_injective
  · rw [subtype_val_range]
    exact hp

/-- The actual comap measure on a subtype pushes forward to the ambient measure
restricted to the subtype range. -/
theorem subtype_comap_measure_map_eq_restrict_of_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α}
    (hcomap :
      MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS)
    (hp : @MeasurableSet α mα {x | p x}) :
    @Measure.map {x : α // p x} α mS mα
        (fun x : {x : α // p x} => (x : α))
        (@Measure.comap {x : α // p x} α mS mα
          (fun x : {x : α // p x} => (x : α)) μα) =
      μα.restrict (Set.range (fun x : {x : α // p x} => (x : α))) := by
  let val : {x : α // p x} → α := fun x => (x : α)
  have hval_embedding : @MeasurableEmbedding {x : α // p x} α mS mα val :=
    subtype_val_measurableEmbedding_of_comap hcomap hp
  exact
    map_eq_restrict_of_eq_comap_of_measurableEmbedding
      (@Measure.comap {x : α // p x} α mS mα val μα) μα val
      (Set.range val) hval_embedding rfl rfl

/-- The actual comap measure on a subtype pushes forward to the ambient
measure restricted to the subtype range when the subtype has the default
measurable structure. -/
theorem subtype_comap_measure_map_eq_restrict_of_subtype_mspace {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hp : @MeasurableSet α mα {x | p x}) :
    @Measure.map {x : α // p x} α mS mα
        (fun x : {x : α // p x} => (x : α))
        (@Measure.comap {x : α // p x} α mS mα
          (fun x : {x : α // p x} => (x : α)) μα) =
      μα.restrict (Set.range (fun x : {x : α // p x} => (x : α))) := by
  have hcomap :
      MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS :=
    subtype_comap_mspace_of_subtype_mspace hsub_mspace_default
  exact subtype_comap_measure_map_eq_restrict_of_comap hcomap hp

/-- The actual comap measure on a subtype has total mass equal to the ambient
measure of the subtype range when the subtype has the default measurable
structure. -/
theorem subtype_comap_measure_range_eq_univ_of_subtype_mspace {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hp : @MeasurableSet α mα {x | p x}) :
    μα (Set.range (fun x : {x : α // p x} => (x : α))) =
      (@Measure.comap {x : α // p x} α mS mα
        (fun x : {x : α // p x} => (x : α)) μα) Set.univ := by
  let val : {x : α // p x} → α := fun x => (x : α)
  have hcomap :
      MeasurableSpace.comap val mα = mS :=
    subtype_comap_mspace_of_subtype_mspace hsub_mspace_default
  have hval_meas : @Measurable {x : α // p x} α mS mα val := by
    rw [← hcomap]
    exact comap_measurable val
  have hmap :
      @Measure.map {x : α // p x} α mS mα val
        (@Measure.comap {x : α // p x} α mS mα val μα) =
        μα.restrict (Set.range val) :=
    subtype_comap_measure_map_eq_restrict_of_subtype_mspace
      hsub_mspace_default hp
  exact
    measure_range_eq_univ_of_map_eq_restrict
      (@Measure.comap {x : α // p x} α mS mα val μα) μα val hval_meas hmap

/-- A subtype measure given by the transported default-subtype comap
presentation pushes forward to the ambient measure restricted to the subtype
range. -/
theorem subtype_measure_map_eq_restrict_of_subtype_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α} {μS : @Measure {x : α // p x} mS}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hp : @MeasurableSet α mα {x | p x})
    (hmeasure_comap_default :
      μS =
        hsub_mspace_default.symm ▸
          (@Measure.comap {x : α // p x} α
            (@Subtype.instMeasurableSpace α p mα)
            mα
            (fun x : {x : α // p x} => (x : α)) μα)) :
    @Measure.map {x : α // p x} α mS mα
        (fun x : {x : α // p x} => (x : α)) μS =
      μα.restrict (Set.range (fun x : {x : α // p x} => (x : α))) := by
  have hcomap :
      MeasurableSpace.comap (fun x : {x : α // p x} => (x : α)) mα = mS :=
    subtype_comap_mspace_of_subtype_mspace hsub_mspace_default
  have hmeasure :
      μS =
        @Measure.comap {x : α // p x} α mS mα
          (fun x : {x : α // p x} => (x : α)) μα :=
    subtype_measure_eq_comap_of_subtype_comap
      hsub_mspace_default hmeasure_comap_default
  rw [hmeasure]
  exact subtype_comap_measure_map_eq_restrict_of_comap hcomap hp

/-- A subtype measure given by the transported default-subtype comap
presentation has total mass equal to the ambient measure of the subtype
range. -/
theorem subtype_measure_range_eq_univ_of_subtype_comap {α : Type u}
    [mα : MeasurableSpace α] {p : α → Prop}
    [mS : MeasurableSpace {x : α // p x}]
    {μα : Measure α} {μS : @Measure {x : α // p x} mS}
    (hsub_mspace_default :
      mS = (@Subtype.instMeasurableSpace α p mα))
    (hp : @MeasurableSet α mα {x | p x})
    (hmeasure_comap_default :
      μS =
        hsub_mspace_default.symm ▸
          (@Measure.comap {x : α // p x} α
            (@Subtype.instMeasurableSpace α p mα)
            mα
            (fun x : {x : α // p x} => (x : α)) μα)) :
    μα (Set.range (fun x : {x : α // p x} => (x : α))) =
      μS Set.univ := by
  have hmeasure :
      μS =
        @Measure.comap {x : α // p x} α mS mα
          (fun x : {x : α // p x} => (x : α)) μα :=
    subtype_measure_eq_comap_of_subtype_comap
      hsub_mspace_default hmeasure_comap_default
  rw [hmeasure]
  exact subtype_comap_measure_range_eq_univ_of_subtype_mspace
    hsub_mspace_default hp

/-- For the default subtype measurable structure on a selected left-quotient
piece, the value map carries exactly the comap measurable structure from the
ambient left quotient. -/
theorem leftRightDoubleCosetPiece_val_comap_eq_subtype_default {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H)
    [MeasurableSpace (leftCosetSet Gamma)] :
    MeasurableSpace.comap
        (fun X : leftRightDoubleCosetPiece Gamma H C => X.1)
        (inferInstance : MeasurableSpace (leftCosetSet Gamma)) =
      (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
        (fun X => leftCosetToLeftRightDoubleCoset Gamma H X = C)
        (inferInstance : MeasurableSpace (leftCosetSet Gamma))) := by
  rfl

/-- Measurable-fiber compatibility form of
`leftRightDoubleCosetPiece_val_comap_eq_subtype_default`. -/
theorem leftRightDoubleCosetPiece_val_comap_eq_subtype {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H)
    [MeasurableSpace (leftCosetSet Gamma)]
    (_hpiece :
      MeasurableSet (leftRightDoubleCosetPieceSet Gamma H C)) :
    MeasurableSpace.comap
        (fun X : leftRightDoubleCosetPiece Gamma H C => X.1)
        (inferInstance : MeasurableSpace (leftCosetSet Gamma)) =
      (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
        (fun X => leftCosetToLeftRightDoubleCoset Gamma H X = C)
        (inferInstance : MeasurableSpace (leftCosetSet Gamma))) := by
  exact leftRightDoubleCosetPiece_val_comap_eq_subtype_default Gamma H C

/-- The translated right-`H` slice `gA` attached to a subset `A ⊆ H`. -/
def rightTranslateSliceSet {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (A : Set H) : Set G :=
  { y | ∃ h : H, h ∈ A ∧ y = g * (h : G) }

/-- The translated right-`H` slice is the image of `A` under the
left-translate inclusion `h ↦ gh`. -/
theorem rightTranslateSliceSet_eq_image {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (A : Set H) :
    rightTranslateSliceSet H g A = (fun h : H => g * (h : G)) '' A := by
  ext y
  constructor
  · rintro ⟨h, hhA, rfl⟩
    exact ⟨h, hhA, rfl⟩
  · rintro ⟨h, hhA, rfl⟩
    exact ⟨h, hhA, rfl⟩

/-- Translated slices attached to distinct double-coset representatives are
disjoint.

This is purely set-theoretic: every point of `g_C A_C` has double-coset class
`C`, so a point lying in both `g_C A_C` and `g_D A_D` forces `C = D`. -/
theorem rightTranslateSliceSet_pairwiseDisjoint_of_leftRightDoubleCosetRepresentatives
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (rep : leftRightDoubleCosetSet Gamma H → G)
    (hrep : ∀ C : leftRightDoubleCosetSet Gamma H,
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C) = C)
    (slice : leftRightDoubleCosetSet Gamma H → Set H) :
    Pairwise fun C D =>
      Disjoint (rightTranslateSliceSet H (rep C) (slice C))
        (rightTranslateSliceSet H (rep D) (slice D)) := by
  intro C D hCD
  rw [Set.disjoint_left]
  intro x hxC hxD
  rcases hxC with ⟨hC, _hhC, rfl⟩
  rcases hxD with ⟨hD, _hhD, hxD_eq⟩
  apply hCD
  let q : G → leftRightDoubleCosetSet Gamma H :=
    Quot.mk (leftRightDoubleCosetSetoid Gamma H)
  have hmkC : q (rep C * (hC : G)) = C := by
    have hrelC :
        IsLeftRightDoubleCosetRelated Gamma H (rep C) (rep C * (hC : G)) := by
      refine ⟨1, hC, ?_⟩
      simp
    exact (Quot.sound hrelC).symm.trans (hrep C)
  have hmkD : q (rep D * (hD : G)) = D := by
    have hrelD :
        IsLeftRightDoubleCosetRelated Gamma H (rep D) (rep D * (hD : G)) := by
      refine ⟨1, hD, ?_⟩
      simp
    exact (Quot.sound hrelD).symm.trans (hrep D)
  calc
    C = q (rep C * (hC : G)) := hmkC.symm
    _ = q (rep D * (hD : G)) := by rw [hxD_eq]
    _ = D := hmkD

/-- Measurability of a translated right slice follows from measurability of the
subset of `H` and measurable embedding of the left-translate inclusion. -/
theorem rightTranslateSliceSet_measurable_of_measurableEmbedding {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) (g : G)
    [mH : MeasurableSpace H] {A : Set H}
    (htranslate : @MeasurableEmbedding H G mH mG (fun h : H => g * (h : G)))
    (hA : @MeasurableSet H mH A) :
    @MeasurableSet G mG (rightTranslateSliceSet H g A) := by
  rw [rightTranslateSliceSet_eq_image]
  exact (htranslate.measurableSet_image).2 hA

/-- The finite union `⋃ i, g_i C_i` of translated local-transversal slices.

This is the concrete fundamental-domain candidate produced by the finite
double-coset presentation in the Schulze--Pillot quotient-volume argument. -/
def finiteRightTransversalFundamentalDomain {ι : Type*} {G : Type u}
    [Group G] (H : Subgroup G) (rep : ι → G) (slice : ι → Set H) :
    Set G :=
  ⋃ i : ι, rightTranslateSliceSet H (rep i) (slice i)

/-- Membership in the finite translated-transversal fundamental-domain
candidate. -/
theorem mem_finiteRightTransversalFundamentalDomain {ι : Type*} {G : Type u}
    [Group G] (H : Subgroup G) (rep : ι → G) (slice : ι → Set H)
    (x : G) :
    x ∈ finiteRightTransversalFundamentalDomain H rep slice ↔
      ∃ i : ι, ∃ h : H, h ∈ slice i ∧ x = rep i * (h : G) := by
  simp [finiteRightTransversalFundamentalDomain, rightTranslateSliceSet]

/-- A finite translated-transversal fundamental-domain candidate is measurable
if each translated slice is measurable. -/
theorem finiteRightTransversalFundamentalDomain_measurableSet {ι : Type*}
    {G : Type u} [Group G] [mG : MeasurableSpace G] [Fintype ι]
    (H : Subgroup G) (rep : ι → G) (slice : ι → Set H)
    (hslice : ∀ i : ι,
      @MeasurableSet G mG (rightTranslateSliceSet H (rep i) (slice i))) :
    @MeasurableSet G mG (finiteRightTransversalFundamentalDomain H rep slice) := by
  exact MeasurableSet.iUnion hslice

/-- The translated subgroup inclusion pushes Haar measure to the ambient
measure restricted to `gH`, provided the subgroup inclusion pushes Haar
measure to the ambient restriction to `H` and ambient left translation by `g`
preserves the measure.

This isolates the Haar-normalization input expected from a concrete
finite-adelic group model into the usual subgroup normalization plus left
invariance of Haar measure. -/
theorem map_rightTranslateSliceSet_univ_eq_restrict_of_map_subtype_eq_restrict
    {G : Type u} [Group G] [mG : MeasurableSpace G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hleft :
      @MeasurableEmbedding G G mG mG (fun x : G => g * x))
    (hleft_map : Measure.map (fun x : G => g * x) μG = μG)
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G)) :
    @Measure.map H G mH mG (fun h : H => g * (h : G)) μH =
      μG.restrict (rightTranslateSliceSet H g Set.univ) := by
  let L : G → G := fun x => g * x
  let val : H → G := fun h => (h : G)
  have hval_meas : @Measurable H G mH mG val := by
    exact measurable_iff_comap_le.2 (le_of_eq hsub_comap)
  have hcomp : (fun h : H => g * (h : G)) = L ∘ val := rfl
  have hpre : L ⁻¹' rightTranslateSliceSet H g Set.univ = (H : Set G) := by
    ext x
    simp [L, rightTranslateSliceSet]
  have hrestrict := hleft.restrict_map μG (rightTranslateSliceSet H g Set.univ)
  change
      (Measure.map (fun x : G => g * x) μG).restrict
          (rightTranslateSliceSet H g Set.univ) =
        Measure.map (fun x : G => g * x)
          (μG.restrict
            ((fun x : G => g * x) ⁻¹' rightTranslateSliceSet H g Set.univ)) at hrestrict
  rw [hpre] at hrestrict
  calc
    @Measure.map H G mH mG (fun h : H => g * (h : G)) μH =
        Measure.map L (Measure.map val μH) := by
      rw [hcomp, Measure.map_map hleft.measurable hval_meas]
    _ = Measure.map L (μG.restrict (H : Set G)) := by
      rw [hval]
    _ = (Measure.map L μG).restrict (rightTranslateSliceSet H g Set.univ) :=
      hrestrict.symm
    _ = μG.restrict (rightTranslateSliceSet H g Set.univ) := by
      rw [hleft_map]

/-- A translated-slice pushforward/restriction identity gives the Haar slice
normalization on every measurable translated subset.

This is the measure-theoretic core of the finite-adelic normalization
`μ_G(gA) = μ_H(A)`: once the translated inclusion `h ↦ gh` pushes the Haar
measure on `H` to the ambient measure restricted to `gH`, the equality on
subsets is formal. -/
theorem measure_rightTranslateSliceSet_eq_of_map_eq_restrict {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) (g : G)
    [mH : MeasurableSpace H] {μG : Measure G} {μH : @Measure H mH}
    {A : Set H}
    (htranslate : @Measurable H G mH mG (fun h : H => g * (h : G)))
    (hS : @MeasurableSet G mG (rightTranslateSliceSet H g A))
    (hmap :
      @Measure.map H G mH mG (fun h : H => g * (h : G)) μH =
        μG.restrict (rightTranslateSliceSet H g Set.univ)) :
    μG (rightTranslateSliceSet H g A) = μH A := by
  have hsubset :
      rightTranslateSliceSet H g A ⊆ rightTranslateSliceSet H g Set.univ := by
    intro y hy
    rcases hy with ⟨h, _hhA, rfl⟩
    exact ⟨h, Set.mem_univ h, rfl⟩
  have hpre :
      (fun h : H => g * (h : G)) ⁻¹' rightTranslateSliceSet H g A = A := by
    ext h
    simp [rightTranslateSliceSet]
  calc
    μG (rightTranslateSliceSet H g A) =
        (μG.restrict (rightTranslateSliceSet H g Set.univ))
          (rightTranslateSliceSet H g A) := by
      rw [Measure.restrict_apply hS]
      rw [Set.inter_eq_left.mpr hsubset]
    _ = (@Measure.map H G mH mG (fun h : H => g * (h : G)) μH)
          (rightTranslateSliceSet H g A) := by
      rw [hmap]
    _ = μH ((fun h : H => g * (h : G)) ⁻¹' rightTranslateSliceSet H g A) := by
      rw [Measure.map_apply htranslate hS]
    _ = μH A := by
      rw [hpre]

/-- In a measurable group, subgroup Haar normalization and ambient left
invariance give the Haar measure of every measurable translated slice.

This removes the separate translated-inclusion pushforward input from the
finite-adelic one-piece normalization: it remains only to identify the
subgroup Haar measure with the ambient measure restricted to `H`. -/
theorem measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH} {A : Set H}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hleft_map : Measure.map (fun x : G => g * x) μG = μG)
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G))
    (hS : @MeasurableSet G mG (rightTranslateSliceSet H g A)) :
    μG (rightTranslateSliceSet H g A) = μH A := by
  let val : H → G := fun h => (h : G)
  have hval_meas : @Measurable H G mH mG val := by
    exact measurable_iff_comap_le.2 (le_of_eq hsub_comap)
  exact
    measure_rightTranslateSliceSet_eq_of_map_eq_restrict H g
      ((measurableEmbedding_mulLeft g).measurable.comp hval_meas)
      hS
      (map_rightTranslateSliceSet_univ_eq_restrict_of_map_subtype_eq_restrict
        H g hsub_comap (measurableEmbedding_mulLeft g) hleft_map hval)

/-- The default subtype measurable-space presentation of a subgroup gives the
natural comap measurable-space field along the subgroup inclusion. -/
theorem subgroup_comap_mspace_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG)) :
    MeasurableSpace.comap (fun h : H => (h : G)) mG = mH := by
  exact
    @subtype_comap_mspace_of_subtype_mspace G mG
      (fun x : G => x ∈ (H : Set G)) mH hsub_mspace_default

/-- The natural comap measurable-space field along a subgroup inclusion is
the ordinary subtype measurable space on the subgroup. -/
theorem subgroup_mspace_of_comap_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH) :
    mH = (@Subtype.instMeasurableSpace G
      (fun x : G => x ∈ (H : Set G)) mG) :=
  @subtype_mspace_of_comap_mspace G mG
    (fun x : G => x ∈ (H : Set G)) mH hsub_comap

/-- The range of the subgroup inclusion is the subgroup as an ambient set. -/
theorem subgroup_val_range {G : Type u} [Group G] (H : Subgroup G) :
    Set.range (fun h : H => (h : G)) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact h.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A subgroup inclusion is a measurable embedding once the subgroup carries
the comap measurable structure and its range is measurable in the ambient
space. -/
theorem subgroup_val_measurableEmbedding_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G)) :
    @MeasurableEmbedding H G mH mG (fun h : H => (h : G)) := by
  refine
    measurableEmbedding_of_comap_eq_of_injective_of_measurableSet_range
      ?_ hcomap ?_
  · intro x y hxy
    exact Subtype.ext hxy
  · rw [subgroup_val_range H]
    exact hH

/-- The actual comap subgroup measure pushes forward to the ambient measure
restricted to the subgroup.

This is the generic compact-open subgroup Haar restriction/comap field:
once the subgroup has the ambient comap measurable structure and measurable
ambient range, `map Subtype.val (Measure.comap Subtype.val μG)` is exactly
`μG.restrict H`. -/
theorem subgroup_comap_measure_map_eq_restrict_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G}
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G)) :
    @Measure.map H G mH mG (fun h : H => (h : G))
        (@Measure.comap H G mH mG (fun h : H => (h : G)) μG) =
      μG.restrict (H : Set G) := by
  let val : H → G := fun h => (h : G)
  have hval_embedding : @MeasurableEmbedding H G mH mG val :=
    subgroup_val_measurableEmbedding_of_comap H hcomap hH
  exact
    map_eq_restrict_of_eq_comap_of_measurableEmbedding
      (@Measure.comap H G mH mG val μG) μG val (H : Set G)
      hval_embedding (subgroup_val_range H) rfl

/-- The actual comap subgroup measure pushes forward to the ambient measure
restricted to the subgroup when the subgroup has the default subtype
measurable structure.

This is the default-subtype form of
`subgroup_comap_measure_map_eq_restrict_of_comap`: it packages the reflexive
comap measurable-space field for subtype measurable spaces. -/
theorem subgroup_comap_measure_map_eq_restrict_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G)) :
    @Measure.map H G mH mG (fun h : H => (h : G))
      (@Measure.comap H G mH mG (fun h : H => (h : G)) μG) =
      μG.restrict (H : Set G) := by
  simpa [subgroup_val_range H] using
    (@subtype_comap_measure_map_eq_restrict_of_subtype_mspace G mG
      (fun x : G => x ∈ (H : Set G)) mH μG hsub_mspace_default hH)

/-- A subgroup measure given as the transported default-subtype comap measure
is the actual comap measure for the stored subgroup measurable space. -/
theorem subgroup_measure_eq_comap_of_subtype_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hmeasure_comap_default :
      μH =
        hsub_mspace_default.symm ▸
          (@Measure.comap H G
            (@Subtype.instMeasurableSpace G
              (fun x : G => x ∈ (H : Set G)) mG)
            mG
            (fun h : H => (h : G)) μG)) :
    μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG := by
  exact
    @subtype_measure_eq_comap_of_subtype_comap G mG
      (fun x : G => x ∈ (H : Set G)) mH μG μH
      hsub_mspace_default hmeasure_comap_default

/-- A subgroup measure given by the ordinary comap measure for the stored
subgroup measurable-space instance is the transported default-subtype comap
measure.

This is the subgroup version of
`subtype_measure_eq_subtype_comap_of_comap`, matching compact-open subgroup
presentations that first identify `μ_H` as the natural comap of the ambient
measure. -/
theorem subgroup_measure_eq_subtype_comap_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hmeasure_comap :
      μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG) :
    μH =
      hsub_mspace_default.symm ▸
        (@Measure.comap H G
          (@Subtype.instMeasurableSpace G
            (fun x : G => x ∈ (H : Set G)) mG)
          mG
          (fun h : H => (h : G)) μG) := by
  exact
    @subtype_measure_eq_subtype_comap_of_comap G mG
      (fun x : G => x ∈ (H : Set G)) mH μG μH
      hsub_mspace_default hmeasure_comap

/-- A subgroup measure defined by comap from the ambient measure pushes forward
to the ambient measure restricted to the subgroup.

This is the generic measurable-space part of the compact-open subgroup Haar
presentation: after the subgroup carries the ambient comap measurable
structure and is ambient-measurable, the map/restrict field follows from the
standard measurable-embedding `map_comap` theorem. -/
theorem subgroup_measure_map_eq_restrict_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap :
      μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG) :
    @Measure.map H G mH mG (fun h : H => (h : G)) μH =
      μG.restrict (H : Set G) := by
  rw [hmeasure_comap]
  exact subgroup_comap_measure_map_eq_restrict_of_comap H hcomap hH

/-- A subgroup measure given by the transported default-subtype comap
presentation pushes forward to the ambient measure restricted to the subgroup. -/
theorem subgroup_measure_map_eq_restrict_of_subtype_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap_default :
      μH =
        hsub_mspace_default.symm ▸
          (@Measure.comap H G
            (@Subtype.instMeasurableSpace G
              (fun x : G => x ∈ (H : Set G)) mG)
            mG
            (fun h : H => (h : G)) μG)) :
    @Measure.map H G mH mG (fun h : H => (h : G)) μH =
      μG.restrict (H : Set G) := by
  rw [subgroup_measure_eq_comap_of_subtype_comap
    H hsub_mspace_default hmeasure_comap_default]
  exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
    H hsub_mspace_default hH

/-- A subgroup measure with the pushforward/restriction normalization is the
ambient comap measure along the subgroup inclusion.

This is the converse concrete Haar-restriction field: if
`map Subtype.val μH = μG.restrict H` and the subgroup carries the ambient
comap measurable structure, then `μH` is exactly the comap of the ambient
measure. -/
theorem subgroup_measure_eq_comap_of_map_restrict {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G)) :
    μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG := by
  let val : H → G := fun h => (h : G)
  have hval_emb : @MeasurableEmbedding H G mH mG val :=
    subgroup_val_measurableEmbedding_of_comap H hsub_comap hH
  calc
    μH = @Measure.comap H G mH mG val
        (@Measure.map H G mH mG val μH) := by
          exact (hval_emb.comap_map μH).symm
    _ = @Measure.comap H G mH mG val
        (μG.restrict (H : Set G)) := by
          rw [hval]
    _ = @Measure.comap H G mH mG val μG := by
          ext A hA
          rw [hval_emb.comap_apply, hval_emb.comap_apply]
          rw [Measure.restrict_apply (hval_emb.measurableSet_image.mpr hA)]
          have hsubset : val '' A ⊆ (H : Set G) := by
            rintro x ⟨h, _hhA, rfl⟩
            exact h.2
          rw [Set.inter_eq_left.mpr hsubset]

/-- A subgroup map/restrict normalization identifies subgroup total mass with
the ambient mass of the subgroup.

This is the generic total-mass part of the compact-open subgroup Haar
presentation.  The remaining concrete work is to compute the ambient mass of
the subgroup, for example from the normalization `μG(H) = 1`. -/
theorem subgroup_measure_univ_eq_of_map_restrict {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hmeasure_map :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G)) :
    μH Set.univ = μG (H : Set G) := by
  let val : H → G := fun h => (h : G)
  have hval_meas : @Measurable H G mH mG val := by
    rw [← hsub_comap]
    exact comap_measurable val
  have hmeasure_map_range :
      @Measure.map H G mH mG val μH =
        μG.restrict (Set.range val) := by
    rw [subgroup_val_range H]
    exact hmeasure_map
  have hrange_mass :
      μG (Set.range val) = μH Set.univ :=
    measure_range_eq_univ_of_map_eq_restrict μH μG val
      hval_meas hmeasure_map_range
  simpa [val, subgroup_val_range H] using hrange_mass.symm

/-- The actual comap subgroup measure has total mass equal to the ambient mass
of the subgroup from the raw subgroup-comap measurable-space presentation. -/
theorem subgroup_comap_measure_univ_eq_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G}
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G)) :
    (@Measure.comap H G mH mG (fun h : H => (h : G)) μG) Set.univ =
      μG (H : Set G) :=
  subgroup_measure_univ_eq_of_map_restrict H hcomap
    (subgroup_comap_measure_map_eq_restrict_of_comap H hcomap hH)

/-- A subgroup measure given by the raw comap presentation has total mass equal
to the ambient mass of the subgroup. -/
theorem subgroup_measure_univ_eq_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap :
      μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG) :
    μH Set.univ = μG (H : Set G) := by
  rw [hmeasure_comap]
  exact subgroup_comap_measure_univ_eq_of_comap H hcomap hH

/-- The actual comap subgroup measure has total mass equal to the ambient
mass of the subgroup when the subgroup has the default subtype measurable
structure. -/
theorem subgroup_comap_measure_univ_eq_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G)) :
    (@Measure.comap H G mH mG (fun h : H => (h : G)) μG) Set.univ =
      μG (H : Set G) := by
  simpa [subgroup_val_range H] using
    (@subtype_comap_measure_range_eq_univ_of_subtype_mspace G mG
      (fun x : G => x ∈ (H : Set G)) mH μG
      hsub_mspace_default hH).symm

/-- A subgroup measure given by the transported default-subtype comap
presentation has total mass equal to the ambient mass of the subgroup. -/
theorem subgroup_measure_univ_eq_of_subtype_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap_default :
      μH =
        hsub_mspace_default.symm ▸
          (@Measure.comap H G
            (@Subtype.instMeasurableSpace G
              (fun x : G => x ∈ (H : Set G)) mG)
            mG
            (fun h : H => (h : G)) μG)) :
    μH Set.univ = μG (H : Set G) := by
  simpa [subgroup_val_range H] using
    (@subtype_measure_range_eq_univ_of_subtype_comap G mG
      (fun x : G => x ∈ (H : Set G)) mH μG μH
      hsub_mspace_default hH hmeasure_comap_default).symm

/-- A subgroup with the ambient comap measurable structure has measurable
left and right multiplication when the ambient group does. -/
theorem subgroup_measurableMul_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH) :
    MeasurableMul H := by
  let val : H → G := fun h => (h : G)
  refine ⟨?_, ?_⟩
  · intro c
    rw [← hcomap]
    rw [measurable_comap_iff]
    change @Measurable H G (MeasurableSpace.comap val mG) mG
      (fun x : H => ((c : G) * (x : G)))
    simpa [val] using
      (Measurable.const_mul (comap_measurable val) (c : G))
  · intro c
    rw [← hcomap]
    rw [measurable_comap_iff]
    change @Measurable H G (MeasurableSpace.comap val mG) mG
      (fun x : H => ((x : G) * (c : G)))
    simpa [val] using
      (Measurable.mul_const (comap_measurable val) (c : G))

/-- A subgroup with the default subtype measurable structure has measurable
left and right multiplication when the ambient group does. -/
theorem subgroup_measurableMul_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG)) :
    MeasurableMul H := by
  have hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH :=
    subgroup_comap_mspace_of_subtype_mspace H hsub_mspace_default
  exact subgroup_measurableMul_of_comap H hcomap

/-- A subgroup with the ambient comap measurable structure has measurable
singletons when the ambient space does. -/
theorem subgroup_measurableSingletonClass_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G]
    [@MeasurableSingletonClass G mG]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH) :
    @MeasurableSingletonClass H mH := by
  let val : H → G := fun h => (h : G)
  refine @MeasurableSingletonClass.mk H mH ?_
  intro h
  rw [← hcomap]
  change @MeasurableSet H (MeasurableSpace.comap val mG) ({h} : Set H)
  have hsingleton :
      ({h} : Set H) = val ⁻¹' ({val h} : Set G) := by
    ext x
    constructor
    · intro hx
      subst hx
      rfl
    · intro hx
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp hx
  rw [hsingleton]
  exact (comap_measurable val) (measurableSet_singleton (val h))

/-- A subgroup with the default subtype measurable structure has measurable
singletons when the ambient space does. -/
theorem subgroup_measurableSingletonClass_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G]
    [@MeasurableSingletonClass G mG]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG)) :
    @MeasurableSingletonClass H mH := by
  have hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH :=
    subgroup_comap_mspace_of_subtype_mspace H hsub_mspace_default
  exact subgroup_measurableSingletonClass_of_comap H hcomap

/-- A subgroup with the ambient comap measurable structure is standard Borel
when the ambient space is standard Borel and the subgroup is measurable. -/
theorem subgroup_standardBorel_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] [StandardBorelSpace G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G)) :
    @StandardBorelSpace H mH := by
  rw [← hcomap]
  exact hH.standardBorel

/-- A subgroup with the default subtype measurable structure is standard Borel
when the ambient space is standard Borel and the subgroup is measurable. -/
theorem subgroup_standardBorel_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] [StandardBorelSpace G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G)) :
    @StandardBorelSpace H mH := by
  have hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH :=
    subgroup_comap_mspace_of_subtype_mspace H hsub_mspace_default
  exact subgroup_standardBorel_of_comap H hcomap hH

/-- A subgroup measure inherits left invariance from an ambient
left-invariant measure when its pushforward is the ambient measure restricted
to the subgroup.

This is the standard Haar-restriction consequence needed by the local
stabilizer-slice calculation: once `μH` is characterized by
`map (Subtype.val : H → G) μH = μG.restrict H`, left invariance of `μH`
is formal from left invariance of `μG`. -/
theorem subgroup_measure_isMulLeftInvariant_of_map_subtype_eq_restrict
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} [Measure.IsMulLeftInvariant μG] {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G)) :
    Measure.IsMulLeftInvariant μH := by
  letI : MeasurableMul H := subgroup_measurableMul_of_comap H hsub_comap
  let val : H → G := fun h => (h : G)
  have hval_emb : @MeasurableEmbedding H G mH mG val :=
    subgroup_val_measurableEmbedding_of_comap H hsub_comap hH
  have hμH_eq : μH = @Measure.comap H G mH mG val μG := by
    calc
      μH = @Measure.comap H G mH mG val
          (@Measure.map H G mH mG val μH) := by
            exact (hval_emb.comap_map μH).symm
      _ = @Measure.comap H G mH mG val
          (μG.restrict (H : Set G)) := by
            rw [hval]
      _ = @Measure.comap H G mH mG val μG := by
            ext A hA
            rw [hval_emb.comap_apply, hval_emb.comap_apply]
            rw [Measure.restrict_apply (hval_emb.measurableSet_image.mpr hA)]
            have hsubset : val '' A ⊆ (H : Set G) := by
              rintro x ⟨h, _hhA, rfl⟩
              exact h.2
            rw [Set.inter_eq_left.mpr hsubset]
  have hcomap_left :
      Measure.IsMulLeftInvariant (@Measure.comap H G mH mG val μG) := by
    simpa [val] using
      (Measure.IsMulLeftInvariant.comap μG (f := H.subtype) hval_emb)
  rw [hμH_eq]
  exact hcomap_left

/-- A subgroup measure defined by comap from an ambient left-invariant measure
inherits left invariance.

This is the generic left-invariance part of the compact-open subgroup Haar
presentation: after the subgroup carries the ambient comap measurable
structure, is ambient-measurable, and its measure is the ambient comap
measure, the map/restrict normalization and left-invariance are formal. -/
theorem subgroup_measure_isMulLeftInvariant_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} [Measure.IsMulLeftInvariant μG] {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap :
      μH = @Measure.comap H G mH mG (fun h : H => (h : G)) μG) :
    Measure.IsMulLeftInvariant μH := by
  exact
    subgroup_measure_isMulLeftInvariant_of_map_subtype_eq_restrict
      H hsub_comap hH
      (subgroup_measure_map_eq_restrict_of_comap
        H hsub_comap hH hmeasure_comap)

/-- The actual comap subgroup measure inherits left invariance from an
ambient left-invariant measure when the subgroup has the default subtype
measurable structure. -/
theorem subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} [Measure.IsMulLeftInvariant μG]
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G)) :
    Measure.IsMulLeftInvariant
      (@Measure.comap H G mH mG (fun h : H => (h : G)) μG) := by
  have hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH :=
    subgroup_comap_mspace_of_subtype_mspace H hsub_mspace_default
  exact
    subgroup_measure_isMulLeftInvariant_of_comap H hcomap hH rfl

/-- A subgroup measure given by the transported default-subtype comap
presentation inherits left invariance from an ambient left-invariant measure. -/
theorem subgroup_measure_isMulLeftInvariant_of_subtype_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) [mH : MeasurableSpace H]
    {μG : Measure G} [Measure.IsMulLeftInvariant μG] {μH : @Measure H mH}
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hH : @MeasurableSet G mG (H : Set G))
    (hmeasure_comap_default :
      μH =
        hsub_mspace_default.symm ▸
          (@Measure.comap H G
            (@Subtype.instMeasurableSpace G
              (fun x : G => x ∈ (H : Set G)) mG)
            mG
            (fun h : H => (h : G)) μG)) :
    Measure.IsMulLeftInvariant μH := by
  have hmeasure :
      μH =
        @Measure.comap H G mH mG (fun h : H => (h : G)) μG :=
    subgroup_measure_eq_comap_of_subtype_comap
      H hsub_mspace_default hmeasure_comap_default
  rw [hmeasure]
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    H hsub_mspace_default hH

/-- Measurable embedding of the translated subgroup inclusion follows from the
subgroup comap measurable structure and measurable embedding of ambient left
multiplication. -/
theorem subgroup_leftTranslate_measurableEmbedding_of_comap {G : Type u}
    [Group G] [mG : MeasurableSpace G] (H : Subgroup G) (g : G)
    [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hleft : @MeasurableEmbedding G G mG mG (fun x : G => g * x)) :
    @MeasurableEmbedding H G mH mG (fun h : H => g * (h : G)) := by
  exact
    hleft.comp
      (@subgroup_val_measurableEmbedding_of_comap G _ mG H mH hcomap hH)

/-- In a measurable group, the translated subgroup inclusion is a measurable
embedding once the subgroup carries the comap measurable structure and is
measurable in the ambient space. -/
theorem subgroup_leftTranslate_measurableEmbedding_of_comap_measurableMul {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G)) :
    @MeasurableEmbedding H G mH mG (fun h : H => g * (h : G)) :=
  subgroup_leftTranslate_measurableEmbedding_of_comap H g hcomap hH
    (measurableEmbedding_mulLeft g)

/-- In a measurable group, a translated right slice `gA` is measurable once
`A` is measurable in the subgroup and the subgroup carries the comap
measurable structure with measurable ambient range. -/
theorem rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    {A : Set H} (hA : @MeasurableSet H mH A) :
    @MeasurableSet G mG (rightTranslateSliceSet H g A) :=
  rightTranslateSliceSet_measurable_of_measurableEmbedding H g
    (subgroup_leftTranslate_measurableEmbedding_of_comap_measurableMul H g hcomap hH)
    hA

/-- In a measurable group, the finite translated-transversal
fundamental-domain candidate is measurable once every local transversal is
measurable in the subgroup and the subgroup carries the ambient comap
measurable structure. -/
theorem finiteRightTransversalFundamentalDomain_measurableSet_of_subgroup_comap
    {ι : Type*} {G : Type u} [Group G] [mG : MeasurableSpace G]
    [MeasurableMul G] [Fintype ι]
    (H : Subgroup G) (rep : ι → G) [mH : MeasurableSpace H]
    (slice : ι → Set H)
    (hcomap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hslice : ∀ i : ι, @MeasurableSet H mH (slice i)) :
    @MeasurableSet G mG
      (finiteRightTransversalFundamentalDomain H rep slice) := by
  exact
    finiteRightTransversalFundamentalDomain_measurableSet H rep slice
      (fun i =>
        rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
          H (rep i) hcomap hH (hslice i))

/-- Fully reduced measurable-group Haar slice normalization.

For a measurable subgroup model, the equality `μ_G(gA)=μ_H(A)` only needs
subgroup Haar normalization, ambient left-invariance, and measurability of
`A` in `H`; measurability of the translated ambient slice is then formal. -/
theorem measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict_of_measurable
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    {μG : Measure G} {μH : @Measure H mH} {A : Set H}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hleft_map : Measure.map (fun x : G => g * x) μG = μG)
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G))
    (hA : @MeasurableSet H mH A) :
    μG (rightTranslateSliceSet H g A) = μH A := by
  exact
    measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict H g
      hsub_comap hleft_map hval
      (rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
        H g hsub_comap hH hA)

/-- Fully reduced measurable-group Haar slice normalization from Mathlib's
standard left-invariant measure class. -/
theorem measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict_of_isMulLeftInvariant
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (H : Subgroup G) (g : G) [mH : MeasurableSpace H]
    {μG : Measure G} [Measure.IsMulLeftInvariant μG] {μH : @Measure H mH} {A : Set H}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G))
    (hA : @MeasurableSet H mH A) :
    μG (rightTranslateSliceSet H g A) = μH A := by
  exact
    measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict_of_measurable
      H g hsub_comap hH (map_mul_left_eq_self μG g) hval hA

/-- Finite additivity for the explicit translated-transversal domain
`⋃ i, g_i C_i`.

This isolates the set-theoretic disjointness input in the concrete
Schulze--Pillot presentation from the later Haar-volume computation. -/
theorem finiteRightTransversalFundamentalDomain_measure_eq_sum
    {ι : Type*} {G : Type u} [Group G] [mG : MeasurableSpace G] [Fintype ι]
    (H : Subgroup G) (rep : ι → G) (slice : ι → Set H)
    (μG : Measure G)
    (hdisj : Pairwise fun i j =>
      Disjoint (rightTranslateSliceSet H (rep i) (slice i))
        (rightTranslateSliceSet H (rep j) (slice j)))
    (hmeas : ∀ i : ι,
      @MeasurableSet G mG (rightTranslateSliceSet H (rep i) (slice i))) :
    μG (finiteRightTransversalFundamentalDomain H rep slice) =
      ∑ i : ι, μG (rightTranslateSliceSet H (rep i) (slice i)) := by
  calc
    μG (finiteRightTransversalFundamentalDomain H rep slice) =
        μG (⋃ i : ι, rightTranslateSliceSet H (rep i) (slice i)) := by
          rfl
    _ = ∑' i : ι, μG (rightTranslateSliceSet H (rep i) (slice i)) := by
          exact measure_iUnion (fun i j hij => hdisj hij) hmeas
    _ = ∑ i : ι, μG (rightTranslateSliceSet H (rep i) (slice i)) := by
          rw [tsum_fintype]

/-- Haar-normalized finite additivity for the explicit translated-transversal
domain.

Once the translated slices are disjoint, the subgroup carries the ambient
comap measurable structure, and the subgroup Haar measure pushes forward to
the ambient restriction, the ambient volume of `⋃ i, g_i C_i` is the finite
sum of the local slice volumes. -/
theorem finiteRightTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
    {ι : Type*} {G : Type u} [Group G] [mG : MeasurableSpace G]
    [MeasurableMul G] [Fintype ι]
    (H : Subgroup G) (rep : ι → G) [mH : MeasurableSpace H]
    (slice : ι → Set H)
    {μG : Measure G} [Measure.IsMulLeftInvariant μG] {μH : @Measure H mH}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hval :
      @Measure.map H G mH mG (fun h : H => (h : G)) μH =
        μG.restrict (H : Set G))
    (hslice : ∀ i : ι, @MeasurableSet H mH (slice i))
    (hdisj : Pairwise fun i j =>
      Disjoint (rightTranslateSliceSet H (rep i) (slice i))
        (rightTranslateSliceSet H (rep j) (slice j))) :
    μG (finiteRightTransversalFundamentalDomain H rep slice) =
      ∑ i : ι, μH (slice i) := by
  have hmeas : ∀ i : ι,
      @MeasurableSet G mG (rightTranslateSliceSet H (rep i) (slice i)) :=
    fun i =>
      rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
        H (rep i) hsub_comap hH (hslice i)
  calc
    μG (finiteRightTransversalFundamentalDomain H rep slice) =
        ∑ i : ι, μG (rightTranslateSliceSet H (rep i) (slice i)) := by
          exact
            finiteRightTransversalFundamentalDomain_measure_eq_sum
              H rep slice μG hdisj hmeas
    _ = ∑ i : ι, μH (slice i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact
            measure_rightTranslateSliceSet_eq_of_map_subtype_eq_restrict_of_isMulLeftInvariant
              H (rep i) hsub_comap hH hval (hslice i)

/-- Exact left-translate uniqueness makes the explicit finite-transversal
candidate a Mathlib fundamental domain.

The remaining concrete Schulze--Pillot input can therefore be stated as the
mathematical uniqueness of the representative in `Gamma \ G`, while
measurability of the finite-transversal domain is discharged from the local
transversal measurability fields. -/
theorem finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_unique
    {ι : Type*} {G : Type u} [Group G] [mG : MeasurableSpace G]
    [MeasurableMul G] [Fintype ι]
    (Gamma H : Subgroup G) (rep : ι → G) [mH : MeasurableSpace H]
    (slice : ι → Set H) {μG : Measure G}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hslice : ∀ i : ι, @MeasurableSet H mH (slice i))
    (hunique : ∀ x : G, ∃! gamma : Gamma,
      (gamma : G) * x ∈ finiteRightTransversalFundamentalDomain H rep slice) :
    IsFundamentalDomain Gamma
      (finiteRightTransversalFundamentalDomain H rep slice) μG := by
  have hmeas :
      @MeasurableSet G mG
        (finiteRightTransversalFundamentalDomain H rep slice) :=
    finiteRightTransversalFundamentalDomain_measurableSet_of_subgroup_comap
      H rep slice hsub_comap hH hslice
  exact
    IsFundamentalDomain.mk' hmeas.nullMeasurableSet (by
      simpa using hunique)

/-- Local-witness form of the finite-transversal fundamental-domain
constructor.

To prove the exact `Γ`-representative uniqueness, it is enough to give a
cover by witnesses `(γ, i, h)` with `γ*x = rep_i*h` and show that any two such
witnesses have the same rational factor `γ`.  This is the form closest to a
finite double-coset presentation with local transversals. -/
theorem finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
    {ι : Type*} {G : Type u} [Group G] [mG : MeasurableSpace G]
    [MeasurableMul G] [Fintype ι]
    (Gamma H : Subgroup G) (rep : ι → G) [mH : MeasurableSpace H]
    (slice : ι → Set H) {μG : Measure G}
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hH : @MeasurableSet G mG (H : Set G))
    (hslice : ∀ i : ι, @MeasurableSet H mH (slice i))
    (hcover : ∀ x : G, ∃ gamma : Gamma, ∃ i : ι, ∃ h : H,
      h ∈ slice i ∧ (gamma : G) * x = rep i * (h : G))
    (hgamma_unique : ∀ (x : G) (gamma₁ gamma₂ : Gamma)
        (i₁ i₂ : ι) (h₁ h₂ : H),
      h₁ ∈ slice i₁ →
      h₂ ∈ slice i₂ →
      (gamma₁ : G) * x = rep i₁ * (h₁ : G) →
      (gamma₂ : G) * x = rep i₂ * (h₂ : G) →
      gamma₁ = gamma₂) :
    IsFundamentalDomain Gamma
      (finiteRightTransversalFundamentalDomain H rep slice) μG := by
  refine
    finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_unique
      Gamma H rep slice hsub_comap hH hslice ?_
  intro x
  rcases hcover x with ⟨gamma, i, h, hh, hx⟩
  refine ⟨gamma, ?_, ?_⟩
  · exact
      (mem_finiteRightTransversalFundamentalDomain H rep slice
        ((gamma : G) * x)).2 ⟨i, h, hh, hx⟩
  · intro gamma' hgamma'
    rcases
      (mem_finiteRightTransversalFundamentalDomain H rep slice
        ((gamma' : G) * x)).1 hgamma' with
      ⟨i', h', hh', hx'⟩
    exact (hgamma_unique x gamma gamma' i i' h h' hh hh' hx hx').symm

/-- Double-coset coverage plus local right-transversal coverage gives the
local witness cover needed for the finite-transversal fundamental-domain
constructor.

The raw double-coset representative covers `G` up to `Γ` on the left and `H`
on the right.  Thus the only remaining local input for coverage is the ability
to replace each right `H`-factor by a chosen slice element after adjusting the
left `Γ`-factor. -/
theorem finiteRightTransversalFundamentalDomain_cover_of_local_right_cover
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (rep : leftRightDoubleCosetSet Gamma H → G)
    (hrep : ∀ C : leftRightDoubleCosetSet Gamma H,
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C) = C)
    (slice : leftRightDoubleCosetSet Gamma H → Set H)
    (hlocal : ∀ C : leftRightDoubleCosetSet Gamma H, ∀ h : H,
      ∃ gamma : Gamma, ∃ c : H,
        c ∈ slice C ∧ (gamma : G) * (rep C * (h : G)) = rep C * (c : G)) :
    ∀ x : G, ∃ gamma : Gamma, ∃ C : leftRightDoubleCosetSet Gamma H,
      ∃ c : H, c ∈ slice C ∧ (gamma : G) * x = rep C * (c : G) := by
  intro x
  let C : leftRightDoubleCosetSet Gamma H :=
    Quot.mk (leftRightDoubleCosetSetoid Gamma H) x
  have hmk :
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C) =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) x := by
    simpa [C] using hrep C
  rcases (leftRightDoubleCoset_mk_eq_iff Gamma H (rep C) x).mp hmk with
    ⟨delta, h, hx⟩
  rcases hlocal C h with ⟨eta, c, hc, heta⟩
  refine ⟨eta * delta⁻¹, C, c, hc, ?_⟩
  calc
    ((eta * delta⁻¹ : Gamma) : G) * x =
        (eta : G) * ((delta⁻¹ : Gamma) : G) * x := by
          simp [mul_assoc]
    _ = (eta : G) * (rep C * (h : G)) := by
          rw [hx]
          simp [mul_assoc]
    _ = rep C * (c : G) := heta

/-- A local transversal for the right stabilizer gives the local
right-normalization used in the finite-transversal cover.

Here `K ≤ H` is any subgroup whose elements can be conjugated by `g` into
`Gamma`: for `s ∈ K`, some `γ ∈ Gamma` satisfies `γ*g = g*s`.  If every
`h ∈ H` can be written as `s*c` with `s ∈ K` and `c` in the chosen slice, then
after adjusting the left rational factor one has `γ*(g*h)=g*c`. -/
theorem local_right_cover_of_stabilizer_transversal
    {G : Type u} [Group G] (Gamma H : Subgroup G) (g : G)
    (K : Subgroup H) (slice : Set H)
    (hstabilizer : ∀ s : K,
      ∃ gamma : Gamma, (gamma : G) * g = g * ((s : H) : G))
    (hcover : ∀ h : H, ∃ s : K, ∃ c : H,
      c ∈ slice ∧ h = (s : H) * c) :
    ∀ h : H, ∃ gamma : Gamma, ∃ c : H,
      c ∈ slice ∧ (gamma : G) * (g * (h : G)) = g * (c : G) := by
  intro h
  rcases hcover h with ⟨s, c, hc, hh⟩
  rcases hstabilizer s with ⟨eta, heta⟩
  refine ⟨eta⁻¹, c, hc, ?_⟩
  have hhG : (h : G) = (((s : H) * c : H) : G) :=
    congrArg (fun x : H => (x : G)) hh
  calc
    ((eta⁻¹ : Gamma) : G) * (g * (h : G)) =
        (eta : G)⁻¹ * (g * (((s : H) * c : H) : G)) := by
          rw [hhG]
          simp
    _ = (eta : G)⁻¹ * ((g * ((s : H) : G)) * (c : G)) := by
          simp [mul_assoc]
    _ = (eta : G)⁻¹ * (((eta : G) * g) * (c : G)) := by
          rw [← heta]
    _ = g * (c : G) := by
          simp [mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Local uniqueness in the stabilizer transversal gives same-`Γ` uniqueness
for finite-transversal witnesses.

The remaining local input is internal to each chosen slice: if
`h₂ * h₁⁻¹` lies in the right stabilizer
`H ∩ rep(C)⁻¹ Γ rep(C)` and both `h₁`, `h₂` are in the selected slice over
`C`, then `h₂ = h₁`.  The ambient double-coset relation and group
cancellation then force the two rational factors in any two witnesses for
the same point to be equal. -/
theorem finiteRightTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (rep : leftRightDoubleCosetSet Gamma H → G)
    (hrep : ∀ C : leftRightDoubleCosetSet Gamma H,
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C) = C)
    (slice : leftRightDoubleCosetSet Gamma H → Set H)
    (hlocal_unique : ∀ (C : leftRightDoubleCosetSet Gamma H)
        (h₁ h₂ : H),
      h₁ ∈ slice C →
      h₂ ∈ slice C →
      (∃ gamma : Gamma,
        (((h₂ * h₁⁻¹ : H) : G) =
          (rep C)⁻¹ * (gamma : G) * rep C)) →
      h₂ = h₁) :
    ∀ (x : G) (gamma₁ gamma₂ : Gamma)
        (C₁ C₂ : leftRightDoubleCosetSet Gamma H) (h₁ h₂ : H),
      h₁ ∈ slice C₁ →
      h₂ ∈ slice C₂ →
      (gamma₁ : G) * x = rep C₁ * (h₁ : G) →
      (gamma₂ : G) * x = rep C₂ * (h₂ : G) →
      gamma₁ = gamma₂ := by
  intro x gamma₁ gamma₂ C₁ C₂ h₁ h₂ hh₁ hh₂ hx₁ hx₂
  let delta : Gamma := gamma₂ * gamma₁⁻¹
  have hx₁_inv : ((gamma₁⁻¹ : Gamma) : G) * (rep C₁ * (h₁ : G)) = x := by
    rw [← hx₁]
    simp
  have hdelta :
      (delta : G) * (rep C₁ * (h₁ : G)) = rep C₂ * (h₂ : G) := by
    calc
      (delta : G) * (rep C₁ * (h₁ : G)) =
          (gamma₂ : G) * (((gamma₁⁻¹ : Gamma) : G) *
            (rep C₁ * (h₁ : G))) := by
            simp [delta, mul_assoc]
      _ = (gamma₂ : G) * x := by
            rw [hx₁_inv]
      _ = rep C₂ * (h₂ : G) := hx₂
  have hrel : IsLeftRightDoubleCosetRelated Gamma H (rep C₁) (rep C₂) := by
    refine ⟨delta, h₁ * h₂⁻¹, ?_⟩
    calc
      rep C₂ = (rep C₂ * (h₂ : G)) * (h₂ : G)⁻¹ := by
          simp [mul_assoc]
      _ = ((delta : G) * (rep C₁ * (h₁ : G))) * (h₂ : G)⁻¹ := by
          rw [hdelta]
      _ = (delta : G) * rep C₁ * (((h₁ * h₂⁻¹ : H) : G)) := by
          simp [mul_assoc]
  have hC : C₁ = C₂ := by
    have hmk :
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C₁) =
          Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C₂) :=
      (leftRightDoubleCoset_mk_eq_iff Gamma H (rep C₁) (rep C₂)).mpr hrel
    calc
      C₁ = Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C₁) := (hrep C₁).symm
      _ = Quot.mk (leftRightDoubleCosetSetoid Gamma H) (rep C₂) := hmk
      _ = C₂ := hrep C₂
  subst C₂
  have hstab :
      ∃ gamma : Gamma,
        (((h₂ * h₁⁻¹ : H) : G) =
          (rep C₁)⁻¹ * (gamma : G) * rep C₁) := by
    refine ⟨delta, ?_⟩
    have hdelta_assoc :
        (delta : G) * rep C₁ * (h₁ : G) = rep C₁ * (h₂ : G) := by
      simpa [mul_assoc] using hdelta
    calc
      (((h₂ * h₁⁻¹ : H) : G)) =
          (h₂ : G) * (h₁ : G)⁻¹ := by
            rfl
      _ = ((rep C₁)⁻¹ * (rep C₁ * (h₂ : G))) * (h₁ : G)⁻¹ := by
            simp
      _ = ((rep C₁)⁻¹ * ((delta : G) * rep C₁ * (h₁ : G))) * (h₁ : G)⁻¹ := by
            rw [← hdelta_assoc]
      _ = (rep C₁)⁻¹ * (delta : G) * rep C₁ := by
            simp [mul_assoc]
  have hh_eq : h₂ = h₁ :=
    hlocal_unique C₁ h₁ h₂ hh₁ hh₂ hstab
  have hdelta_one : (delta : G) = 1 := by
    have hfixed :
        (delta : G) * (rep C₁ * (h₁ : G)) = rep C₁ * (h₁ : G) := by
      simpa [hh_eq] using hdelta
    calc
      (delta : G) =
          ((delta : G) * (rep C₁ * (h₁ : G))) *
            (rep C₁ * (h₁ : G))⁻¹ := by
            simp [mul_assoc]
      _ = 1 := by
            rw [hfixed]
            simp [mul_assoc]
  apply Subtype.ext
  symm
  calc
    (gamma₂ : G) = ((gamma₂ : G) * (gamma₁ : G)⁻¹) * (gamma₁ : G) := by
        simp [mul_assoc]
    _ = (gamma₁ : G) := by
        have hdelta_carrier :
            (gamma₂ : G) * (gamma₁ : G)⁻¹ = 1 := by
          simpa [delta] using hdelta_one
        rw [hdelta_carrier]
        simp

/-- The canonical partition of `Gamma \ G` into the fibers of the projection
`Gamma \ G → Gamma \ G / H`.

This is the set-theoretic decomposition underlying the finite-additivity
quotient-volume source: after a quotient measure is constructed, additivity
should be applied over the sigma fibers on the right. -/
def leftCosetSigmaLeftRightDoubleCosetPieceEquiv {G : Type u} [Group G]
    (Gamma H : Subgroup G) :
    leftCosetSet Gamma ≃
      Σ C : leftRightDoubleCosetSet Gamma H, leftRightDoubleCosetPiece Gamma H C where
  toFun X :=
    ⟨leftCosetToLeftRightDoubleCoset Gamma H X, ⟨X, rfl⟩⟩
  invFun Y :=
    Y.2.1
  left_inv X := rfl
  right_inv Y := by
    rcases Y with ⟨C, X, hX⟩
    cases hX
    rfl

lemma leftCosetToLeftRightDoubleCoset_eq_mk_iff {G : Type u} [Group G]
    (Gamma H : Subgroup G) (X : leftCosetSet Gamma) (g : G) :
    leftCosetToLeftRightDoubleCoset Gamma H X =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) g ↔
      ∃ h : H, X = Quot.mk (leftCosetSetoid Gamma) (g * (h : G)) := by
  induction X using Quot.inductionOn with
  | h x =>
      rw [leftCosetToLeftRightDoubleCoset_mk]
      constructor
      · intro hx
        rcases (leftRightDoubleCoset_mk_eq_iff Gamma H x g).mp hx with
          ⟨gamma, h, hg⟩
        refine ⟨h⁻¹, ?_⟩
        apply Quot.sound
        refine ⟨gamma, ?_⟩
        rw [hg]
        simp [mul_assoc]
      · rintro ⟨h, hx⟩
        rcases Quotient.exact hx with ⟨gamma, hxg⟩
        apply (leftRightDoubleCoset_mk_eq_iff Gamma H x g).mpr
        refine ⟨gamma, h⁻¹, ?_⟩
        calc
          g = (g * (h : G)) * (h : G)⁻¹ := by
            simp [mul_assoc]
          _ = ((gamma : G) * x) * (h : G)⁻¹ := by
            rw [hxg]
          _ = (gamma : G) * x * (h : G)⁻¹ := by
            simp [mul_assoc]

lemma leftRightDoubleCosetPiece_mk_mem {G : Type u} [Group G]
    (Gamma H : Subgroup G) (g : G) (h : H) :
    leftCosetToLeftRightDoubleCoset Gamma H
        (Quot.mk (leftCosetSetoid Gamma) (g * (h : G))) =
      Quot.mk (leftRightDoubleCosetSetoid Gamma H) g := by
  exact (leftCosetToLeftRightDoubleCoset_eq_mk_iff Gamma H
    (Quot.mk (leftCosetSetoid Gamma) (g * (h : G))) g).mpr ⟨h, rfl⟩

theorem leftCosetMap_mem_leftRightDoubleCosetPieceSet_of_mem_rightTranslateSliceSet
    {G : Type u} [Group G] (Gamma H : Subgroup G) {g y : G} {A : Set H}
    (hy : y ∈ rightTranslateSliceSet H g A) :
    leftCosetMap Gamma y ∈
      leftRightDoubleCosetPieceSet Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) := by
  rcases hy with ⟨h, _hhA, rfl⟩
  simpa [leftCosetMap, leftRightDoubleCosetPieceSet] using
    leftRightDoubleCosetPiece_mk_mem Gamma H g h

/-- The preimage in `G` of the selected fiber over the double coset of `g`
is the strict set-theoretic double coset `Gamma * g * H`.

This is the set-level input needed when a fundamental-domain construction
computes the measure of a selected quotient fiber by intersecting the chosen
domain with the quotient-map preimage. -/
theorem leftCosetMap_preimage_leftRightDoubleCosetPieceSet_mk
    {G : Type u} [Group G] (Gamma H : Subgroup G) (g : G) :
    (leftCosetMap Gamma) ⁻¹'
        leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =
      { y : G | ∃ gamma : Gamma, ∃ h : H,
        y = (gamma : G) * g * (h : G) } := by
  ext y
  constructor
  · intro hy
    change
      leftCosetToLeftRightDoubleCoset Gamma H (leftCosetMap Gamma y) =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) g at hy
    rw [leftCosetMap, leftCosetToLeftRightDoubleCoset_mk] at hy
    rcases (leftRightDoubleCoset_mk_eq_iff Gamma H y g).mp hy with
      ⟨gamma, h, hg⟩
    refine ⟨gamma⁻¹, h⁻¹, ?_⟩
    calc
      y = (gamma : G)⁻¹ * g * (h : G)⁻¹ := by
        rw [hg]
        simp [mul_assoc]
      _ = ((gamma⁻¹ : Gamma) : G) * g * ((h⁻¹ : H) : G) := rfl
  · rintro ⟨gamma, h, rfl⟩
    change
      leftCosetToLeftRightDoubleCoset Gamma H
          (leftCosetMap Gamma ((gamma : G) * g * (h : G))) =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) g
    rw [leftCosetMap, leftCosetToLeftRightDoubleCoset_mk]
    apply (leftRightDoubleCoset_mk_eq_iff Gamma H
      ((gamma : G) * g * (h : G)) g).mpr
    refine ⟨gamma⁻¹, h⁻¹, ?_⟩
    simp [mul_assoc]

/-- Fundamental-domain pushforward mass of a selected double-coset fiber,
using explicit selected-fiber measurability.

With the standard map measurable structure on `Gamma \ G`, the quotient
measure of a measurable fiber over the double coset of `g` is the ambient
measure of the chosen domain intersected with the strict double-coset set
`Gamma * g * H`. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPieceSet_mk_of_measurable
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} (g : G)
    (hpiece :
      @MeasurableSet (leftCosetSet Gamma) mX
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        y = (gamma : G) * g * (h : G) }) := by
  calc
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) =
        μG (F ∩
          (leftCosetMap Gamma) ⁻¹'
            leftRightDoubleCosetPieceSet Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) := by
          exact
            leftQuotientMapRestrictFundamentalDomain_apply_map_mspace
              (Gamma := Gamma) (hmX := hleft_mspace) hpiece
    _ = μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
          y = (gamma : G) * g * (h : G) }) := by
          rw [leftCosetMap_preimage_leftRightDoubleCosetPieceSet_mk]

/-- Fundamental-domain pushforward mass of a selected double-coset fiber.

With the standard map measurable structures on `Gamma \ G` and
`Gamma \ G / H`, the quotient measure of the fiber over the double coset of
`g` is the ambient measure of the chosen domain intersected with the strict
double-coset set `Gamma * g * H`. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPieceSet_mk
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hquot_mspace :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    {μG : Measure G} {F : Set G} (g : G) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        y = (gamma : G) * g * (h : G) }) := by
  exact
    leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPieceSet_mk_of_measurable
      (Gamma := Gamma) (H := H) (hleft_mspace := hleft_mspace)
      (μG := μG) (F := F) g
      (leftRightDoubleCosetPieceSet_measurable_of_map_mspace_singleton
        Gamma H hquot_mspace (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))

/-- Named fundamental-domain quotient mass of a selected double-coset fiber,
using explicit selected-fiber measurability.

With the standard map measurable structure on `Gamma \ G`, the named quotient
measure attached to a fundamental-domain candidate evaluates on a measurable
fiber over `Gamma * g * H` as the ambient measure of `F` intersected with the
strict double-coset set. -/
theorem leftQuotientFundamentalDomainMeasure_apply_leftRightDoubleCosetPieceSet_mk_of_measurable
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} (g : G)
    (hpiece :
      @MeasurableSet (leftCosetSet Gamma) mX
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))) :
    (leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F)
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        y = (gamma : G) * g * (h : G) }) := by
  simpa [leftQuotientFundamentalDomainMeasure_eq_map_restrict] using
    leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPieceSet_mk_of_measurable
      (Gamma := Gamma) (H := H) (hleft_mspace := hleft_mspace)
      (μG := μG) (F := F) g hpiece

/-- Named fundamental-domain quotient mass of a selected double-coset fiber.

With the standard map measurable structures on `Gamma \ G` and
`Gamma \ G / H`, the named quotient measure attached to a fundamental-domain
candidate evaluates on the fiber over `Gamma * g * H` as the ambient measure
of `F` intersected with the strict double-coset set. -/
theorem leftQuotientFundamentalDomainMeasure_apply_leftRightDoubleCosetPieceSet_mk
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hquot_mspace :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    {μG : Measure G} {F : Set G} (g : G) :
    (leftQuotientFundamentalDomainMeasure Gamma (mX := mX) μG F)
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        y = (gamma : G) * g * (h : G) }) := by
  exact
    leftQuotientFundamentalDomainMeasure_apply_leftRightDoubleCosetPieceSet_mk_of_measurable
      (Gamma := Gamma) (H := H) (hleft_mspace := hleft_mspace)
      (μG := μG) (F := F) g
      (leftRightDoubleCosetPieceSet_measurable_of_map_mspace_singleton
        Gamma H hquot_mspace (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))

/-- The right-`H` orbit map into the selected piece attached to a specific
representative `g`.  Unlike `rightOrbitToLeftRightDoubleCosetPiece`, this
version keeps `g` visible in the ambient slice `gH`, which is the form used by
the fundamental-domain source theorem. -/
def rightOrbitToLeftRightDoubleCosetPieceOfRepresentative {G : Type u} [Group G]
    (Gamma H : Subgroup G) (g : G) (h : H) :
    leftRightDoubleCosetPiece Gamma H
      (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) :=
  ⟨Quot.mk (leftCosetSetoid Gamma) (g * (h : G)),
    leftRightDoubleCosetPiece_mk_mem Gamma H g h⟩

/-- The representative-based right-`H` orbit map is measurable for the
standard quotient/subtype measurable structures. -/
theorem rightOrbitToLeftRightDoubleCosetPieceOfRepresentative_measurable_of_map_subtype_comap
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (Gamma H : Subgroup G) (g : G)
    [mH : MeasurableSpace H] [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mP :
      MeasurableSpace
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))]
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hsub_meas : @MeasurableSet G mG (H : Set G))
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X =>
            leftCosetToLeftRightDoubleCoset Gamma H X =
              Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) mX)) :
    @Measurable H
      (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) mH mP
      (rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g) := by
  rw [hpiece_mspace]
  have htranslate :
      @Measurable H G mH mG (fun h : H => g * (h : G)) :=
    (subgroup_leftTranslate_measurableEmbedding_of_comap_measurableMul
      H g hsub_comap hsub_meas).measurable
  have hleft :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hleft_mspace]
    exact leftCosetMap_measurable_map Gamma
  have hval :
      @Measurable H (leftCosetSet Gamma) mH mX
        (fun h : H =>
          (rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
            Gamma H g h).1) := by
    simpa [rightOrbitToLeftRightDoubleCosetPieceOfRepresentative, leftCosetMap]
      using hleft.comp htranslate
  simpa using hval.subtype_mk

/-- Left saturation of a subset by a subgroup. -/
def leftSubgroupSaturation {G : Type u} [Group G]
    (Gamma : Subgroup G) (S : Set G) : Set G :=
  { y | ∃ gamma : Gamma, ∃ x ∈ S, y = (gamma : G) * x }

theorem leftSubgroupSaturation_eq_iUnion_image {G : Type u} [Group G]
    (Gamma : Subgroup G) (S : Set G) :
    leftSubgroupSaturation Gamma S =
      ⋃ gamma : Gamma, (fun x : G => (gamma : G) * x) '' S := by
  ext y
  constructor
  · rintro ⟨gamma, x, hxS, rfl⟩
    exact Set.mem_iUnion.2 ⟨gamma, ⟨x, hxS, rfl⟩⟩
  · intro hy
    rcases Set.mem_iUnion.1 hy with ⟨gamma, x, hxS, rfl⟩
    exact ⟨gamma, x, hxS, rfl⟩

/-- The support of the set-periodization over a left quotient is exactly the
left saturation of the original ambient set.

This is the support half of the strict fundamental-domain
unfolding: before integrating the positive-support indicator of a periodized
slice over a domain `F`, Lean can identify that support with `F ∩ ΓS`. -/
theorem leftSetPeriodize_leftCosetMap_eq_zero_iff_not_mem_leftSubgroupSaturation
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) (y : G) :
    leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 ↔
      y ∉ leftSubgroupSaturation Gamma S := by
  rw [leftSetPeriodize_leftCosetMap, ENNReal.tsum_eq_zero]
  constructor
  · intro hzero hy
    rcases hy with ⟨gamma, x, hxS, rfl⟩
    have hterm := hzero gamma⁻¹
    simp [hxS] at hterm
  · intro hy gamma
    by_cases hmem : (gamma : G) * y ∈ S
    · have hsat : y ∈ leftSubgroupSaturation Gamma S := by
        refine ⟨gamma⁻¹, (gamma : G) * y, hmem, ?_⟩
        simp
      exact False.elim (hy hsat)
    · simp [hmem]

/-- The finite-cardinality integrand of a set-periodization vanishes outside
the left saturation of the underlying ambient set.

This is the raw-count analogue of
`leftSetPeriodize_leftCosetMap_eq_zero_iff_not_mem_leftSubgroupSaturation` and
keeps the support bookkeeping for the remaining strict-domain counting source
inside Lean. -/
theorem nat_card_leftTranslateSupport_eq_zero_of_not_mem_leftSubgroupSaturation
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) {y : G}
    (hy : y ∉ leftSubgroupSaturation Gamma S) :
    Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } = 0 := by
  let T : Type u := { gamma : Gamma // (gamma : G) * y ∈ S }
  have hT_empty : IsEmpty T := by
    refine ⟨fun gamma => hy ?_⟩
    refine ⟨gamma.1⁻¹, (gamma.1 : G) * y, gamma.2, ?_⟩
    simp
  have hcard : Nat.card T = Nat.card Empty :=
    Nat.card_congr
      { toFun := fun gamma => False.elim (hT_empty.false gamma)
        invFun := fun e => Empty.elim e
        left_inv := by
          intro gamma
          exact False.elim (hT_empty.false gamma)
        right_inv := by
          intro e
          exact Empty.elim e }
  change Nat.card T = 0
  rw [hcard]
  simp

/-- Under local finiteness, the raw finite-cardinality integrand is nonzero
exactly on the left saturation of the ambient set. -/
theorem nat_card_leftTranslateSupport_ne_zero_iff_mem_leftSubgroupSaturation
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) (y : G)
    [Finite { gamma : Gamma // (gamma : G) * y ∈ S }] :
    Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } ≠ 0 ↔
      y ∈ leftSubgroupSaturation Gamma S := by
  constructor
  · intro hne
    by_contra hy
    exact hne
      (nat_card_leftTranslateSupport_eq_zero_of_not_mem_leftSubgroupSaturation
        Gamma S hy)
  · rintro ⟨gamma, x, hxS, rfl⟩
    let T : Type u := { delta : Gamma // (delta : G) * ((gamma : G) * x) ∈ S }
    haveI : Nonempty T := ⟨⟨gamma⁻¹, by simpa [T] using hxS⟩⟩
    have hpos : 0 < Nat.card T := Nat.card_pos
    exact Nat.pos_iff_ne_zero.mp hpos

/-- The strict-domain finite-cardinality integrand is already supported on
the left saturation of the ambient slice.

This support insertion is the raw-count version needed before the
remaining fundamental-domain unfolding source proves the actual value of
`∫_F #{γ | γy ∈ S}`. -/
theorem lintegral_restrict_nat_card_leftTranslateSupport_eq_lintegral_indicator_leftSubgroupSaturation
    {G : Type u} [Group G] [MeasurableSpace G] (Gamma : Subgroup G)
    {μG : Measure G} {F S : Set G} :
    ∫⁻ y,
        (Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } : ℝ≥0∞)
          ∂μG.restrict F =
      ∫⁻ y,
        (leftSubgroupSaturation Gamma S).indicator
          (fun y =>
            (Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } : ℝ≥0∞)) y
          ∂μG.restrict F := by
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ leftSubgroupSaturation Gamma S
    · simp [Set.indicator_of_mem hy]
    · have hzero :
          Nat.card { gamma : Gamma // (gamma : G) * y ∈ S } = 0 :=
        nat_card_leftTranslateSupport_eq_zero_of_not_mem_leftSubgroupSaturation
          Gamma S hy
      simp [Set.indicator_of_notMem hy, hzero]

theorem leftSetPeriodize_leftCosetMap_ne_zero_iff_mem_leftSubgroupSaturation
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) (y : G) :
    leftSetPeriodize Gamma S (leftCosetMap Gamma y) ≠ 0 ↔
      y ∈ leftSubgroupSaturation Gamma S := by
  constructor
  · intro hne
    by_contra hy
    exact hne
      ((leftSetPeriodize_leftCosetMap_eq_zero_iff_not_mem_leftSubgroupSaturation
        Gamma S y).2 hy)
  · intro hy hz
    exact
      ((leftSetPeriodize_leftCosetMap_eq_zero_iff_not_mem_leftSubgroupSaturation
        Gamma S y).1 hz) hy

theorem leftSetPeriodize_leftCosetMap_supportIndicator_eq_leftSubgroupSaturation_indicator
    {G : Type u} [Group G] (Gamma : Subgroup G) (S : Set G) (y : G) :
    (if leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 then
        (0 : ℝ≥0∞) else 1) =
      (leftSubgroupSaturation Gamma S).indicator
        (fun _ : G => (1 : ℝ≥0∞)) y := by
  by_cases hy : y ∈ leftSubgroupSaturation Gamma S
  · have hne :
        leftSetPeriodize Gamma S (leftCosetMap Gamma y) ≠ 0 :=
      (leftSetPeriodize_leftCosetMap_ne_zero_iff_mem_leftSubgroupSaturation
        Gamma S y).2 hy
    simp [hy, hne]
  · have hz :
        leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 :=
      (leftSetPeriodize_leftCosetMap_eq_zero_iff_not_mem_leftSubgroupSaturation
        Gamma S y).2 hy
    simp [hy, hz]

/-- Integrated support form of
`leftSetPeriodize_leftCosetMap_supportIndicator_eq_leftSubgroupSaturation_indicator`.

For a strict domain `F`, the positive-support indicator of the periodized
ambient slice integrates to the ambient measure of `F ∩ ΓS`.  Identifying this
support measure with the appropriate finite-stabilizer quotient volume is not
done here. -/
theorem lintegral_restrict_supportIndicator_leftSetPeriodize_eq_measure_inter_leftSubgroupSaturation
    {G : Type u} [Group G] [MeasurableSpace G] (Gamma : Subgroup G)
    {μG : Measure G} {F S : Set G}
    (hSat : MeasurableSet (leftSubgroupSaturation Gamma S)) :
    ∫⁻ y,
        (if leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 then
          (0 : ℝ≥0∞) else 1) ∂μG.restrict F =
      μG (F ∩ leftSubgroupSaturation Gamma S) := by
  calc
    ∫⁻ y,
        (if leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 then
          (0 : ℝ≥0∞) else 1) ∂μG.restrict F =
        ∫⁻ y,
          (leftSubgroupSaturation Gamma S).indicator
            (fun _ : G => (1 : ℝ≥0∞)) y ∂μG.restrict F := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun y =>
            leftSetPeriodize_leftCosetMap_supportIndicator_eq_leftSubgroupSaturation_indicator
              Gamma S y
    _ = (μG.restrict F) (leftSubgroupSaturation Gamma S) := by
          rw [lintegral_indicator_const hSat]
          simp
    _ = μG (F ∩ leftSubgroupSaturation Gamma S) := by
          rw [Measure.restrict_apply hSat]
          rw [Set.inter_comm]

/-- Countable left saturations of measurable sets are measurable in a
measurable group. -/
theorem leftSubgroupSaturation_measurable_of_countable {G : Type u}
    [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G) [Countable Gamma] {S : Set G}
    (hS : @MeasurableSet G mG S) :
    @MeasurableSet G mG (leftSubgroupSaturation Gamma S) := by
  rw [leftSubgroupSaturation_eq_iUnion_image]
  exact MeasurableSet.iUnion fun gamma : Gamma =>
    (measurableEmbedding_mulLeft (gamma : G)).measurableSet_image.2 hS

/-- Countable-subgroup version of the integrated support form. -/
theorem lintegral_restrict_supportIndicator_leftSetPeriodize_eq_measure_inter_leftSubgroupSaturation_of_countable
    {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Gamma : Subgroup G) [Countable Gamma]
    {μG : Measure G} {F S : Set G} (hS : MeasurableSet S) :
    ∫⁻ y,
        (if leftSetPeriodize Gamma S (leftCosetMap Gamma y) = 0 then
          (0 : ℝ≥0∞) else 1) ∂μG.restrict F =
      μG (F ∩ leftSubgroupSaturation Gamma S) :=
  lintegral_restrict_supportIndicator_leftSetPeriodize_eq_measure_inter_leftSubgroupSaturation
    Gamma (leftSubgroupSaturation_measurable_of_countable Gamma hS)

/-- The explicit selected orbit-preimage set is the left saturation of the
translated right-`H` slice attached to the orbit-map preimage in `H`. -/
theorem leftSubgroupSaturation_rightTranslateSliceSet_orbitPreimage_eq
    {G : Type u} [Group G] (Gamma H : Subgroup G) (g : G)
    (B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))) :
    leftSubgroupSaturation Gamma
        (rightTranslateSliceSet H g
          { h : H |
            rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
              Gamma H g h ∈ B }) =
      { y : G | ∃ gamma : Gamma, ∃ h : H,
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
          y = (gamma : G) * g * (h : G) } := by
  ext y
  constructor
  · rintro ⟨gamma, x, ⟨h, hhB, rfl⟩, rfl⟩
    exact ⟨gamma, h, hhB, by simp [mul_assoc]⟩
  · rintro ⟨gamma, h, hhB, rfl⟩
    refine ⟨gamma, g * (h : G), ?_, by simp [mul_assoc]⟩
    exact ⟨h, hhB, rfl⟩

/-- Measurability of the explicit saturated translated orbit-preimage set
from the standard quotient/subtype/subgroup measurable-space setup. -/
theorem selectedOrbitPreimageSaturation_measurable_of_map_subtype_comap
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    {Gamma H : Subgroup G} [Countable Gamma]
    [mH : MeasurableSpace H] [mX : MeasurableSpace (leftCosetSet Gamma)]
    {g : G}
    [mP :
      MeasurableSpace
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))]
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hsub_meas : @MeasurableSet G mG (H : Set G))
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X =>
            leftCosetToLeftRightDoubleCoset Gamma H X =
              Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) mX))
    {B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))}
    (hB :
      @MeasurableSet
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) mP B) :
    @MeasurableSet G mG
      { y : G | ∃ gamma : Gamma, ∃ h : H,
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
          y = (gamma : G) * g * (h : G) } := by
  let A : Set H :=
    { h : H |
      rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B }
  have horbit :
      @Measurable H
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) mH mP
        (rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g) :=
    rightOrbitToLeftRightDoubleCosetPieceOfRepresentative_measurable_of_map_subtype_comap
      Gamma H g hsub_comap hsub_meas hleft_mspace hpiece_mspace
  have hA : @MeasurableSet H mH A := horbit hB
  have hS :
      @MeasurableSet G mG (rightTranslateSliceSet H g A) :=
    rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
      H g hsub_comap hsub_meas hA
  have hsat :
      @MeasurableSet G mG
        (leftSubgroupSaturation Gamma (rightTranslateSliceSet H g A)) :=
    leftSubgroupSaturation_measurable_of_countable Gamma hS
  simpa [A, leftSubgroupSaturation_rightTranslateSliceSet_orbitPreimage_eq]
    using hsat

/-- Preimage in `G` of a selected subset of one double-coset fiber.

For a subset `B` of the selected quotient piece over the representative `g`,
the preimage of its value-map image under `leftCosetMap` is the strict
left-`Gamma` saturation of the translated orbit-map preimage in `gH`. -/
theorem leftCosetMap_preimage_leftRightDoubleCosetPiece_val_image_mk
    {G : Type u} [Group G] (Gamma H : Subgroup G) (g : G)
    (B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))) :
    (leftCosetMap Gamma) ⁻¹' ((fun X :
        leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
        X.1) '' B) =
      { y : G | ∃ gamma : Gamma, ∃ h : H,
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
          y = (gamma : G) * g * (h : G) } := by
  ext y
  constructor
  · rintro ⟨X, hXB, hXeq⟩
    rcases X with ⟨Xval, hXpiece⟩
    change Xval = leftCosetMap Gamma y at hXeq
    have hYeq : leftCosetMap Gamma y = Xval := hXeq.symm
    have hXrep :
        leftCosetToLeftRightDoubleCoset Gamma H Xval =
          Quot.mk (leftRightDoubleCosetSetoid Gamma H) g := hXpiece
    rcases (leftCosetToLeftRightDoubleCoset_eq_mk_iff Gamma H Xval g).mp hXrep with
      ⟨h, hXval⟩
    have hOrbit_mem :
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B := by
      have hSubtype :
          rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h =
            ⟨Xval, hXpiece⟩ := by
        apply Subtype.ext
        exact hXval.symm
      simpa [hSubtype] using hXB
    rw [leftCosetMap] at hYeq
    have hYg :
        Quot.mk (leftCosetSetoid Gamma) y =
          Quot.mk (leftCosetSetoid Gamma) (g * (h : G)) :=
      hYeq.trans hXval
    rcases Quotient.exact hYg with ⟨gamma, hy⟩
    refine ⟨gamma⁻¹, h, hOrbit_mem, ?_⟩
    calc
      y = (gamma : G)⁻¹ * (g * (h : G)) := by
        rw [hy]
        simp
      _ = ((gamma⁻¹ : Gamma) : G) * g * (h : G) := by
        simp [mul_assoc]
  · rintro ⟨gamma, h, hB, rfl⟩
    refine ⟨rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h, hB, ?_⟩
    apply Quot.sound
    exact ⟨gamma, by simp [mul_assoc]⟩

/-- Fundamental-domain pushforward mass of a selected subset of one
double-coset fiber.

This is the selected-subset version of
`leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPieceSet_mk`:
the quotient mass of the value-map image of `B ⊆ X_g` is the ambient measure
of the chosen domain intersected with the strict left-`Gamma` saturation of the
translated orbit-map preimage in `gH`. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {g : G}
    {B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))}
    (hBimage :
      @MeasurableSet (leftCosetSet Gamma) mX
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B)) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
          y = (gamma : G) * g * (h : G) }) := by
  calc
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B) =
        μG (F ∩ (leftCosetMap Gamma) ⁻¹'
          ((fun X :
              leftRightDoubleCosetPiece Gamma H
                (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
              X.1) '' B)) := by
          exact
            leftQuotientMapRestrictFundamentalDomain_apply_map_mspace
              (Gamma := Gamma) (hmX := hleft_mspace) hBimage
    _ = μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
          rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
            y = (gamma : G) * g * (h : G) }) := by
          rw [leftCosetMap_preimage_leftRightDoubleCosetPiece_val_image_mk]

/-- Images of measurable subsets of a selected piece are measurable in the
ambient left quotient for the standard quotient/subtype measurable-space
construction. -/
theorem leftRightDoubleCosetPiece_val_image_measurable_of_map_mspace_singleton
    {G : Type u} [Group G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hquot_mspace :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    (C : leftRightDoubleCosetSet Gamma H)
    [mP : MeasurableSpace (leftRightDoubleCosetPiece Gamma H C)]
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X => leftCosetToLeftRightDoubleCoset Gamma H X = C) mX))
    {B : Set (leftRightDoubleCosetPiece Gamma H C)}
    (hB : @MeasurableSet (leftRightDoubleCosetPiece Gamma H C) mP B) :
    @MeasurableSet (leftCosetSet Gamma) mX
      ((fun X : leftRightDoubleCosetPiece Gamma H C => X.1) '' B) := by
  have hpiece :
      @MeasurableSet (leftCosetSet Gamma) mX
        (leftRightDoubleCosetPieceSet Gamma H C) :=
    leftRightDoubleCosetPieceSet_measurable_of_map_mspace_singleton
      Gamma H hquot_mspace C
  have hval :
      @MeasurableEmbedding (leftRightDoubleCosetPiece Gamma H C)
        (leftCosetSet Gamma) mP mX (fun X => X.1) := by
    rw [hpiece_mspace]
    exact
      (MeasurableEmbedding.subtype_coe
        (s := leftRightDoubleCosetPieceSet Gamma H C) hpiece)
  exact (hval.measurableSet_image).2 hB

/-- Fundamental-domain pushforward mass of a measurable selected subset in the
standard quotient/subtype measurable-space setup.

This discharges the image-measurability hypothesis in
`leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk`
from the standard map measurable structure on `Γ \ G / H` and the selected
piece's subtype measurable structure. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk_of_map_mspace_singleton
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hquot_mspace :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    {μG : Measure G} {F : Set G} {g : G}
    [mP :
      MeasurableSpace
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))]
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X =>
            leftCosetToLeftRightDoubleCoset Gamma H X =
              Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) mX))
    {B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))}
    (hB :
      @MeasurableSet
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) mP B) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B) =
      μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
        rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
          y = (gamma : G) * g * (h : G) }) := by
  exact
    leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk
      (Gamma := Gamma) (H := H) hleft_mspace
      (B := B)
      (leftRightDoubleCosetPiece_val_image_measurable_of_map_mspace_singleton
        (Gamma := Gamma) (H := H) hquot_mspace
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)
        hpiece_mspace hB)

/-- Selected-subset quotient mass from the two remaining analytic inputs.

Once the fundamental-domain source proves that the chosen domain intersects
the left saturation of `gA_B` with the same ambient mass as `gA_B`, and the
subgroup Haar normalization identifies the ambient mass of `gA_B` with the
Haar mass of `A_B`, the quotient-mass statement for the selected subset
`B ⊆ X_g` is completely formal. -/
theorem leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk_of_saturation_slice_eq
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma H : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mC : MeasurableSpace (leftRightDoubleCosetSet Gamma H)]
    [MeasurableSingletonClass (leftRightDoubleCosetSet Gamma H)]
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hquot_mspace :
      mC = MeasurableSpace.map (leftCosetToLeftRightDoubleCoset Gamma H) mX)
    {μG : Measure G} {μH : Measure H} {F : Set G} {g : G}
    [mP :
      MeasurableSpace
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))]
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X =>
            leftCosetToLeftRightDoubleCoset Gamma H X =
              Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) mX))
    {B :
      Set (leftRightDoubleCosetPiece Gamma H
        (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g))}
    (hB :
      @MeasurableSet
        (leftRightDoubleCosetPiece Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)) mP B)
    (hfund_saturation :
      μG (F ∩
          leftSubgroupSaturation Gamma
            (rightTranslateSliceSet H g
              { h : H |
                rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
                  Gamma H g h ∈ B })) =
        μG
          (rightTranslateSliceSet H g
            { h : H |
              rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
                Gamma H g h ∈ B }))
    (hhaar_slice :
      μG
          (rightTranslateSliceSet H g
            { h : H |
              rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
                Gamma H g h ∈ B }) =
        μH
          { h : H |
            rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
              Gamma H g h ∈ B }) :
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B) =
      μH
        { h : H |
          rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
            Gamma H g h ∈ B } := by
  calc
    (Measure.map (leftCosetMap Gamma) (μG.restrict F))
        ((fun X :
            leftRightDoubleCosetPiece Gamma H
              (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g) =>
            X.1) '' B) =
        μG (F ∩ { y : G | ∃ gamma : Gamma, ∃ h : H,
          rightOrbitToLeftRightDoubleCosetPieceOfRepresentative Gamma H g h ∈ B ∧
            y = (gamma : G) * g * (h : G) }) := by
          exact
            leftQuotientMapRestrictFundamentalDomain_apply_leftRightDoubleCosetPiece_val_image_mk_of_map_mspace_singleton
              (Gamma := Gamma) (H := H) hleft_mspace hquot_mspace
              hpiece_mspace hB
    _ =
        μG (F ∩
          leftSubgroupSaturation Gamma
            (rightTranslateSliceSet H g
              { h : H |
                rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
                  Gamma H g h ∈ B })) := by
          rw [leftSubgroupSaturation_rightTranslateSliceSet_orbitPreimage_eq]
    _ =
        μG
          (rightTranslateSliceSet H g
            { h : H |
              rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
                Gamma H g h ∈ B }) := hfund_saturation
    _ =
        μH
          { h : H |
            rightOrbitToLeftRightDoubleCosetPieceOfRepresentative
              Gamma H g h ∈ B } := hhaar_slice

theorem IsLeftWeilQuotientMeasure.lintegral_indicator_leftSetPeriodize_rightTranslateSliceSet_eq
    {G : Type u} [Group G] [MeasurableSpace G] {Gamma H : Subgroup G}
    [MeasurableSpace (leftCosetSet Gamma)] {μG : Measure G}
    {μX : Measure (leftCosetSet Gamma)}
    (hWeil : IsLeftWeilQuotientMeasure Gamma μG μX)
    {g : G} {A : Set H}
    (hSmeas : MeasurableSet (rightTranslateSliceSet H g A)) :
    ∫⁻ X,
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)).indicator
          (leftSetPeriodize Gamma (rightTranslateSliceSet H g A)) X ∂μX =
      μG (rightTranslateSliceSet H g A) := by
  exact hWeil.lintegral_indicator_leftSetPeriodize_eq hSmeas
    (fun {y} hy =>
      leftCosetMap_mem_leftRightDoubleCosetPieceSet_of_mem_rightTranslateSliceSet
        Gamma H hy)

/-- Strict fundamental-domain lintegral transfer for one measurable
periodized function.

This is the single-function form needed for compact-slice indicators: with
the standard map measurable space on `Gamma \ G`, the quotient-side integral
against `Measure.map (leftCosetMap Gamma) (μG.restrict F)` follows from the
strict-domain integral identity over `F`. -/
theorem lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_map_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] {Gamma : Subgroup G}
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {f : G → ℝ≥0∞}
    (hf : Measurable (leftPreperiodize Gamma f))
    (hfund :
      ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
        ∫⁻ y, f y ∂μG) :
    ∫⁻ X, leftPeriodize Gamma f X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
      ∫⁻ y, f y ∂μG := by
  have hmap :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hmX]
    exact leftCosetMap_measurable_map Gamma
  have hperiodize :
      @Measurable (leftCosetSet Gamma) ℝ≥0∞ mX inferInstance
        (leftPeriodize Gamma f) := by
    rw [hmX]
    exact leftPeriodize_measurable_map_of_leftPreperiodize Gamma hf
  calc
    ∫⁻ X, leftPeriodize Gamma f X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
        ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F := by
          exact MeasureTheory.lintegral_map hperiodize hmap
    _ = ∫⁻ y, f y ∂μG := hfund

/-- Countable-subgroup version of the strict fundamental-domain transfer for
one measurable function.

The countability and measurable-multiplication hypotheses discharge the
ambient preperiodization measurability input. -/
theorem lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_countable
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Countable Gamma]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {f : G → ℝ≥0∞}
    (hf : Measurable f)
    (hfund :
      ∫⁻ y, leftPeriodize Gamma f (leftCosetMap Gamma y) ∂μG.restrict F =
        ∫⁻ y, f y ∂μG) :
    ∫⁻ X, leftPeriodize Gamma f X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
      ∫⁻ y, f y ∂μG :=
  lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_map_mspace
    (Gamma := Gamma) (μG := μG) (F := F) hmX
    (leftPreperiodize_measurable_of_countable Gamma hf) hfund

/-- Indicator-slice specialization of the countable strict fundamental-domain
transfer. -/
theorem lintegral_leftSetPeriodize_eq_of_map_restrict_fundamentalDomain_countable
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Countable Gamma]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {S : Set G}
    (hSmeas : MeasurableSet S)
    (hfund :
      ∫⁻ y, leftSetPeriodize Gamma S (leftCosetMap Gamma y) ∂μG.restrict F =
        μG S) :
    ∫⁻ X, leftSetPeriodize Gamma S X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
      μG S := by
  have hf : Measurable (S.indicator (fun _ : G => (1 : ℝ≥0∞))) :=
    (measurable_const : Measurable fun _ : G => (1 : ℝ≥0∞)).indicator hSmeas
  have hind :
      ∫⁻ y, S.indicator (fun _ : G => (1 : ℝ≥0∞)) y ∂μG = μG S := by
    rw [lintegral_indicator_const hSmeas]
    simp
  have hfund' :
      ∫⁻ y,
          leftPeriodize Gamma (S.indicator (fun _ : G => (1 : ℝ≥0∞)))
            (leftCosetMap Gamma y) ∂μG.restrict F =
        ∫⁻ y, S.indicator (fun _ : G => (1 : ℝ≥0∞)) y ∂μG := by
    calc
      ∫⁻ y,
          leftPeriodize Gamma (S.indicator (fun _ : G => (1 : ℝ≥0∞)))
            (leftCosetMap Gamma y) ∂μG.restrict F =
          μG S := by
            simpa [leftSetPeriodize] using hfund
      _ = ∫⁻ y, S.indicator (fun _ : G => (1 : ℝ≥0∞)) y ∂μG := hind.symm
  calc
    ∫⁻ X, leftSetPeriodize Gamma S X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
        ∫⁻ y, S.indicator (fun _ : G => (1 : ℝ≥0∞)) y ∂μG := by
          simpa [leftSetPeriodize] using
            (lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_countable
              (Gamma := Gamma) (μG := μG) (F := F) hmX hf hfund')
    _ = μG S := hind

/-- Support-restricted indicator form of the countable strict
fundamental-domain transfer. -/
theorem lintegral_indicator_leftSetPeriodize_eq_of_map_restrict_fundamentalDomain_countable
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    {Gamma : Subgroup G} [Countable Gamma]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {S : Set G}
    (hSmeas : MeasurableSet S)
    {Y : Set (leftCosetSet Gamma)}
    (hS_sub : ∀ ⦃y : G⦄, y ∈ S → leftCosetMap Gamma y ∈ Y)
    (hfund :
      ∫⁻ y, leftSetPeriodize Gamma S (leftCosetMap Gamma y) ∂μG.restrict F =
        μG S) :
    ∫⁻ X, Y.indicator (leftSetPeriodize Gamma S) X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
      μG S := by
  let μX : Measure (leftCosetSet Gamma) :=
    Measure.map (leftCosetMap Gamma) (μG.restrict F)
  have hsupport :
      leftSetPeriodize Gamma S =ᵐ[μX]
        Y.indicator (leftSetPeriodize Gamma S) := by
    exact Filter.Eventually.of_forall (by
      intro X
      by_cases hX : X ∈ Y
      · simp [Set.indicator_of_mem hX]
      · rw [Set.indicator_of_notMem hX]
        exact leftSetPeriodize_eq_zero_of_not_mem Gamma hS_sub hX)
  calc
    ∫⁻ X, Y.indicator (leftSetPeriodize Gamma S) X ∂μX =
        ∫⁻ X, leftSetPeriodize Gamma S X ∂μX := by
          exact (lintegral_congr_ae hsupport).symm
    _ = μG S :=
        lintegral_leftSetPeriodize_eq_of_map_restrict_fundamentalDomain_countable
          (Gamma := Gamma) (μG := μG) (F := F) hmX hSmeas hfund

/-- Translated right-slice specialization of the countable strict
fundamental-domain transfer. -/
theorem lintegral_indicator_leftSetPeriodize_rightTranslateSliceSet_eq_of_map_restrict_fundamentalDomain_countable
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    {Gamma H : Subgroup G} [Countable Gamma]
    [mX : MeasurableSpace (leftCosetSet Gamma)]
    (hmX : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    {μG : Measure G} {F : Set G} {g : G} {A : Set H}
    (hSmeas : MeasurableSet (rightTranslateSliceSet H g A))
    (hfund :
      ∫⁻ y,
          leftSetPeriodize Gamma (rightTranslateSliceSet H g A)
            (leftCosetMap Gamma y) ∂μG.restrict F =
        μG (rightTranslateSliceSet H g A)) :
    ∫⁻ X,
        (leftRightDoubleCosetPieceSet Gamma H
          (Quot.mk (leftRightDoubleCosetSetoid Gamma H) g)).indicator
          (leftSetPeriodize Gamma (rightTranslateSliceSet H g A)) X
        ∂Measure.map (leftCosetMap Gamma) (μG.restrict F) =
      μG (rightTranslateSliceSet H g A) := by
  exact
    lintegral_indicator_leftSetPeriodize_eq_of_map_restrict_fundamentalDomain_countable
      (Gamma := Gamma) (μG := μG) (F := F) hmX hSmeas
      (fun {y} hy =>
        leftCosetMap_mem_leftRightDoubleCosetPieceSet_of_mem_rightTranslateSliceSet
          Gamma H hy)
      hfund

/-- The selected right-`H` orbit map from the compact-open factor to the
left-quotient piece over a double coset.  This generic version is available
early enough to be used in finite-adelic presentation data. -/
def rightOrbitToLeftRightDoubleCosetPiece {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H)
    (h : H) : leftRightDoubleCosetPiece Gamma H C :=
  ⟨Quot.mk (leftCosetSetoid Gamma) (Quot.out C * (h : G)), by
    exact (leftRightDoubleCosetPiece_mk_mem Gamma H (Quot.out C) h).trans
      (Quot.out_eq C)⟩

/-- The selected right-`H` orbit map into a double-coset fiber is measurable
for the standard quotient/subtype measurable structures.

This discharges the corresponding finite-adelic presentation field once
`H` carries the comap measurable structure from the ambient group, the left
quotient carries the map measurable structure from `G`, and the selected
piece carries the subtype measurable structure from `Gamma \ G`. -/
theorem rightOrbitToLeftRightDoubleCosetPiece_measurable_of_map_subtype_comap
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H)
    [mH : MeasurableSpace H] [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mP : MeasurableSpace (leftRightDoubleCosetPiece Gamma H C)]
    (hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH)
    (hsub_meas : @MeasurableSet G mG (H : Set G))
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X => leftCosetToLeftRightDoubleCoset Gamma H X = C) mX)) :
    @Measurable H (leftRightDoubleCosetPiece Gamma H C) mH mP
      (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) := by
  rw [hpiece_mspace]
  have htranslate :
      @Measurable H G mH mG (fun h : H => Quot.out C * (h : G)) :=
    (subgroup_leftTranslate_measurableEmbedding_of_comap_measurableMul
      H (Quot.out C) hsub_comap hsub_meas).measurable
  have hleft :
      @Measurable G (leftCosetSet Gamma) mG mX (leftCosetMap Gamma) := by
    rw [hleft_mspace]
    exact leftCosetMap_measurable_map Gamma
  have hval :
      @Measurable H (leftCosetSet Gamma) mH mX
        (fun h : H => (rightOrbitToLeftRightDoubleCosetPiece Gamma H C h).1) := by
    simpa [rightOrbitToLeftRightDoubleCosetPiece, leftCosetMap] using
      hleft.comp htranslate
  simpa using hval.subtype_mk

/-- The selected right-`H` orbit map is measurable for the standard
quotient/subtype measurable structures when `H` carries the default subtype
measurable space.

This is the common concrete compact-open presentation: the subgroup
measurable space is inherited from the ambient finite-adelic group, and the
selected quotient piece uses the ordinary subtype measurable space over
`Gamma \ G`. -/
theorem rightOrbitToLeftRightDoubleCosetPiece_measurable_of_map_subtype_mspace
    {G : Type u} [Group G] [mG : MeasurableSpace G] [MeasurableMul G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H)
    [mH : MeasurableSpace H] [mX : MeasurableSpace (leftCosetSet Gamma)]
    [mP : MeasurableSpace (leftRightDoubleCosetPiece Gamma H C)]
    (hsub_meas : @MeasurableSet G mG (H : Set G))
    (hsub_mspace_default :
      mH = (@Subtype.instMeasurableSpace G
        (fun x : G => x ∈ (H : Set G)) mG))
    (hleft_mspace : mX = MeasurableSpace.map (leftCosetMap Gamma) mG)
    (hpiece_mspace :
      mP =
        (@Subtype.instMeasurableSpace (leftCosetSet Gamma)
          (fun X => leftCosetToLeftRightDoubleCoset Gamma H X = C) mX)) :
    @Measurable H (leftRightDoubleCosetPiece Gamma H C) mH mP
      (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) := by
  have hsub_comap :
      MeasurableSpace.comap (fun h : H => (h : G)) mG = mH :=
    subgroup_comap_mspace_of_subtype_mspace H hsub_mspace_default
  exact
    rightOrbitToLeftRightDoubleCosetPiece_measurable_of_map_subtype_comap
      Gamma H C hsub_comap hsub_meas hleft_mspace hpiece_mspace

theorem rightOrbitToLeftRightDoubleCosetPiece_surjective {G : Type u} [Group G]
    (Gamma H : Subgroup G) (C : leftRightDoubleCosetSet Gamma H) :
    Function.Surjective (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) := by
  intro X
  rcases X with ⟨X, hX⟩
  have hXrep :
      leftCosetToLeftRightDoubleCoset Gamma H X =
        Quot.mk (leftRightDoubleCosetSetoid Gamma H) (Quot.out C) :=
    hX.trans (Quot.out_eq C).symm
  rcases (leftCosetToLeftRightDoubleCoset_eq_mk_iff Gamma H X
      (Quot.out C)).mp hXrep with ⟨h, hXeq⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  exact hXeq.symm

/-- A chosen right-`H` coordinate for a point in a generic selected
left-quotient piece.  This generic version is available inside the abstract
finite-adelic presentation fields. -/
noncomputable def leftRightDoubleCosetPieceRightTranslateRepresentative
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (X : leftRightDoubleCosetPiece Gamma H C) :
    H :=
  Classical.choose (rightOrbitToLeftRightDoubleCosetPiece_surjective Gamma H C X)

lemma rightOrbitToLeftRightDoubleCosetPiece_rightTranslateRepresentative
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (X : leftRightDoubleCosetPiece Gamma H C) :
    rightOrbitToLeftRightDoubleCosetPiece Gamma H C
        (leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X) = X :=
  Classical.choose_spec (rightOrbitToLeftRightDoubleCosetPiece_surjective Gamma H C X)

/-- Generic periodized-indicator count attached to the chosen representative
of a point in one selected left-quotient piece. -/
noncomputable def leftRightDoubleCosetPiecePeriodizedIndicatorCount
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (X : leftRightDoubleCosetPiece Gamma H C) :
    ℝ≥0∞ :=
  let g := Quot.out C
  let h₀ := leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X
  (Nat.card
      { gamma : Gamma //
        ∃ h : H, (gamma : G) * g * (h₀ : G) = g * (h : G) } : ℝ≥0∞)

/-- Generic representative-slice periodization on a translated compact-open
slice.  For `A = orbit ⁻¹' B`, this rewrites to the selected-piece
indicator. -/
noncomputable def doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (A : Set H)
    (X : leftRightDoubleCosetPiece Gamma H C) : ℝ≥0∞ :=
  A.indicator
      (fun _ => leftRightDoubleCosetPiecePeriodizedIndicatorCount Gamma H C X)
      (leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X)

/-- On an orbit-map preimage, actual translated-slice periodization agrees
pointwise with the canonical representative-slice count, provided the raw
rational support at each chosen representative is finite. -/
theorem leftSetPeriodize_rightTranslateSliceSet_orbitPreimage_eq_representativeCore
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H)
    (B : Set (leftRightDoubleCosetPiece Gamma H C))
    (hfinite : ∀ X : leftRightDoubleCosetPiece Gamma H C,
      Finite
        { gamma : Gamma //
          ∃ h : H,
            (gamma : G) * Quot.out C *
                (leftRightDoubleCosetPieceRightTranslateRepresentative
                  Gamma H C X : G) =
              Quot.out C * (h : G) }) :
    (fun X : leftRightDoubleCosetPiece Gamma H C =>
      leftSetPeriodize Gamma
        (rightTranslateSliceSet H (Quot.out C)
          ((rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B)) X.1) =
      doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore Gamma H C
        ((rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B) := by
  funext X
  let h₀ := leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X
  let support : Type u :=
    { gamma : Gamma //
      (gamma : G) * (Quot.out C * (h₀ : G)) ∈
        rightTranslateSliceSet H (Quot.out C)
          ((rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B) }
  let raw : Type u :=
    { gamma : Gamma //
      ∃ h : H,
        (gamma : G) * Quot.out C * (h₀ : G) = Quot.out C * (h : G) }
  have hrep : rightOrbitToLeftRightDoubleCosetPiece Gamma H C h₀ = X :=
    rightOrbitToLeftRightDoubleCosetPiece_rightTranslateRepresentative Gamma H C X
  have hval : X.1 = leftCosetMap Gamma (Quot.out C * (h₀ : G)) := by
    exact congrArg Subtype.val hrep.symm
  have horbit_of_raw : ∀ gamma : raw, ∀ h : H,
      (gamma : Gamma) * Quot.out C * (h₀ : G) = Quot.out C * (h : G) →
        rightOrbitToLeftRightDoubleCosetPiece Gamma H C h = X := by
    intro gamma h hgamma
    calc
      rightOrbitToLeftRightDoubleCosetPiece Gamma H C h =
          rightOrbitToLeftRightDoubleCosetPiece Gamma H C h₀ := by
        apply Subtype.ext
        change leftCosetMap Gamma (Quot.out C * (h : G)) =
          leftCosetMap Gamma (Quot.out C * (h₀ : G))
        rw [← hgamma]
        simpa [mul_assoc] using
          leftCosetMap_gamma_mul Gamma gamma.1
            (Quot.out C * (h₀ : G))
      _ = X := hrep
  rw [hval]
  by_cases hX : X ∈ B
  · let e : support ≃ raw :=
      { toFun := fun gamma => by
          refine ⟨gamma.1, ?_⟩
          rcases gamma.2 with ⟨h, _hhB, hgamma⟩
          exact ⟨h, by simpa [mul_assoc] using hgamma⟩
        invFun := fun gamma => by
          refine ⟨gamma.1, ?_⟩
          rcases gamma.2 with ⟨h, hgamma⟩
          refine ⟨h, ?_, by simpa [mul_assoc] using hgamma⟩
          change rightOrbitToLeftRightDoubleCosetPiece Gamma H C h ∈ B
          rw [horbit_of_raw gamma h hgamma]
          exact hX
        left_inv := by intro gamma; rfl
        right_inv := by intro gamma; rfl }
    haveI : Finite raw := hfinite X
    haveI : Finite support := Finite.of_equiv raw e.symm
    rw [leftSetPeriodize_leftCosetMap_eq_nat_card_of_finite]
    change (Nat.card support : ℝ≥0∞) = _
    have hh₀ : h₀ ∈
        (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B := by
      change rightOrbitToLeftRightDoubleCosetPiece Gamma H C h₀ ∈ B
      rw [hrep]
      exact hX
    rw [doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore,
      Set.indicator_of_mem hh₀]
    change (Nat.card support : ℝ≥0∞) = (Nat.card raw : ℝ≥0∞)
    exact_mod_cast Nat.card_congr e
  · haveI : IsEmpty support := ⟨fun gamma => by
      apply hX
      rcases gamma.2 with ⟨h, hhB, hgamma⟩
      have horbit : rightOrbitToLeftRightDoubleCosetPiece Gamma H C h = X :=
        horbit_of_raw
          ⟨gamma.1, ⟨h, by simpa [mul_assoc] using hgamma⟩⟩ h
          (by simpa [mul_assoc] using hgamma)
      rw [← horbit]
      exact hhB⟩
    haveI : Finite support := inferInstance
    rw [leftSetPeriodize_leftCosetMap_eq_nat_card_of_finite]
    change (Nat.card support : ℝ≥0∞) = _
    have hh₀ : h₀ ∉
        (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B := by
      intro hh₀
      apply hX
      change rightOrbitToLeftRightDoubleCosetPiece Gamma H C h₀ ∈ B at hh₀
      rwa [hrep] at hh₀
    have hhrep :
        leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X ∉
          (rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B := by
      simpa [h₀] using hh₀
    simp [doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore, hhrep]

theorem doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore_preimage_eq_indicator
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (B : Set (leftRightDoubleCosetPiece Gamma H C)) :
    doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore Gamma H C
        ((rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B) =
      B.indicator (leftRightDoubleCosetPiecePeriodizedIndicatorCount Gamma H C) := by
  funext X
  have hrep :
      rightOrbitToLeftRightDoubleCosetPiece Gamma H C
          (leftRightDoubleCosetPieceRightTranslateRepresentative Gamma H C X) = X :=
    rightOrbitToLeftRightDoubleCosetPiece_rightTranslateRepresentative Gamma H C X
  by_cases hX : X ∈ B
  · simp [doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore, hrep, hX]
  · simp [doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore, hrep, hX]

theorem doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore_preimage_ae_eq_indicator
    {G : Type u} [Group G] (Gamma H : Subgroup G)
    (C : leftRightDoubleCosetSet Gamma H) (B : Set (leftRightDoubleCosetPiece Gamma H C))
    (mX : MeasurableSpace (leftRightDoubleCosetPiece Gamma H C))
    (μ : @Measure (leftRightDoubleCosetPiece Gamma H C) mX) :
    doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore Gamma H C
        ((rightOrbitToLeftRightDoubleCosetPiece Gamma H C) ⁻¹' B) =ᵐ[μ]
      B.indicator (leftRightDoubleCosetPiecePeriodizedIndicatorCount Gamma H C) :=
  Filter.Eventually.of_forall (by
    intro X
    exact congrFun
      (doubleCosetPieceRepresentativeSlicePeriodizedIndicatorCore_preimage_eq_indicator
        Gamma H C B) X)

/-- Conjugation of a subgroup by an element of the ambient group.  This
standalone version is used in the finite-adelic presentation fields before
the namespace-local version is introduced. -/
def conjugateSubgroupCore {G : Type u} [Group G]
    (H : Subgroup G) (g : G) : Subgroup G where
  carrier := { x | ∃ h : H, x = g * (h : G) * g⁻¹ }
  one_mem' := by
    refine ⟨1, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hx, rfl⟩ ⟨hy, rfl⟩
    refine ⟨hx * hy, ?_⟩
    simp [mul_assoc]
  inv_mem' := by
    rintro x ⟨h, rfl⟩
    refine ⟨h⁻¹, ?_⟩
    simp [mul_assoc]


end PositiveDefiniteIntegralLattice

end
