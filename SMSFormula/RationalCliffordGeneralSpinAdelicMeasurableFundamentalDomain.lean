import SMSFormula.RationalCliffordGeneralSpinAdelicCountableSliceAtlas

/-!
# A measurable fundamental domain for the rational adelic general-Spin quotient

The countable quotient-slice atlas is recursively disjointified on the
quotient.  Pulling each disjoint quotient piece back inside its assigned open
source slice gives a measurable subset of full-adelic intrinsic `GSpin` which
meets every rational left coset exactly once.

This is a carrier-level measurable fundamental domain.  No quotient measure,
crossed disintegration, or differential normalization is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Disjoint quotient pieces -/

/-- The recursively disjoint part of the `m`-th quotient base. -/
def fullAdelicCliffordGeneralSpinLeftQuotientPiece (m : ℕ) :
    Set V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  disjointed V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m

theorem measurableSet_fullAdelicCliffordGeneralSpinLeftQuotientPiece
    (m : ℕ) :
    MeasurableSet (V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m) := by
  apply MeasurableSet.disjointed
  intro k
  exact
    (V.isOpen_fullAdelicCliffordGeneralSpinLeftQuotientSliceBase k).measurableSet

theorem fullAdelicCliffordGeneralSpinLeftQuotientPiece_subset_sliceBase
    (m : ℕ) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m ⊆
      V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m :=
  disjointed_subset _ _

theorem pairwiseDisjoint_fullAdelicCliffordGeneralSpinLeftQuotientPiece :
    Pairwise (Function.onFun Disjoint
      V.fullAdelicCliffordGeneralSpinLeftQuotientPiece) :=
  disjoint_disjointed V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase

theorem iUnion_fullAdelicCliffordGeneralSpinLeftQuotientPiece :
    ⋃ m, V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m = Set.univ := by
  change ⋃ m, disjointed
    V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m = Set.univ
  rw [iUnion_disjointed,
    V.iUnion_fullAdelicCliffordGeneralSpinLeftQuotientSliceBase]

/-! ## Sections over the disjoint pieces -/

/-- The inclusion of a disjoint quotient piece into its assigned atlas base.
-/
def fullAdelicCliffordGeneralSpinLeftQuotientPieceToSliceBase (m : ℕ) :
    C(V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m,
      V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m) where
  toFun y :=
    ⟨y, V.fullAdelicCliffordGeneralSpinLeftQuotientPiece_subset_sliceBase m
      y.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The local section restricted to the `m`-th disjoint quotient piece. -/
def fullAdelicCliffordGeneralSpinLeftQuotientPieceSection (m : ℕ) :
    C(V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m,
      V.FullAdelicCliffordGeneralSpinGroup) :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSection m).comp
    (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceToSliceBase m)

theorem measurable_fullAdelicCliffordGeneralSpinLeftQuotientPieceSection
    (m : ℕ) :
    Measurable (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m) :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m).continuous.measurable

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_pieceSection
    (m : ℕ)
    (y : V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m y) = y :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientMap_sliceSection m
    (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceToSliceBase m y)

/-- The source representative piece assigned to the `m`-th disjoint quotient
piece. -/
def fullAdelicCliffordGeneralSpinFundamentalSourcePiece (m : ℕ) :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientMap ⁻¹'
      V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m ∩
    V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSource m

theorem measurableSet_fullAdelicCliffordGeneralSpinFundamentalSourcePiece
    (m : ℕ) :
    MeasurableSet (V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece m) :=
  (V.measurableSet_fullAdelicCliffordGeneralSpinLeftQuotientPiece m).preimage
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_measurable |>.inter
    (V.isOpen_fullAdelicCliffordGeneralSpinLeftQuotientSliceSource m).measurableSet

theorem pairwiseDisjoint_fullAdelicCliffordGeneralSpinFundamentalSourcePiece :
    Pairwise (Function.onFun Disjoint
      V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece) := by
  intro m k hmk
  change Disjoint
    (V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece m)
    (V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece k)
  rw [Set.disjoint_left]
  intro x hxm hxk
  exact
    Set.disjoint_left.mp
      (V.pairwiseDisjoint_fullAdelicCliffordGeneralSpinLeftQuotientPiece hmk)
      hxm.1 hxk.1

theorem range_fullAdelicCliffordGeneralSpinLeftQuotientPieceSection
    (m : ℕ) :
    Set.range (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m) =
      V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m y) ∈
        V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m
      rw [V.fullAdelicCliffordGeneralSpinLeftQuotientMap_pieceSection]
      exact y.2
    · rw [← V.range_fullAdelicCliffordGeneralSpinLeftQuotientSliceSection m]
      exact
        ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientPieceToSliceBase m y, rfl⟩
  · rintro ⟨hxpiece, hxsource⟩
    let y : V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m :=
      ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientMap x, hxpiece⟩
    refine ⟨y, ?_⟩
    apply V.fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_sliceSource m
    · rw [← V.range_fullAdelicCliffordGeneralSpinLeftQuotientSliceSection m]
      exact
        ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientPieceToSliceBase m y, rfl⟩
    · exact hxsource
    · exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_pieceSection m y

/-! ## The global measurable fundamental domain -/

/-- The countable union of the disjoint source representative pieces. -/
def fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  ⋃ m, V.fullAdelicCliffordGeneralSpinFundamentalSourcePiece m

theorem measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :
    MeasurableSet V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
  MeasurableSet.iUnion
    V.measurableSet_fullAdelicCliffordGeneralSpinFundamentalSourcePiece

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_image_fundamentalDomain :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap ''
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hyUnion :
      y ∈ ⋃ m, V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m := by
    rw [V.iUnion_fullAdelicCliffordGeneralSpinLeftQuotientPiece]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hyUnion with ⟨m, hym⟩
  let ym : V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m := ⟨y, hym⟩
  refine
    ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m ym,
      Set.mem_iUnion.mpr ⟨m, ?_⟩, ?_⟩
  · rw [← V.range_fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m]
    exact ⟨ym, rfl⟩
  · exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_pieceSection m ym

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_fundamentalDomain :
    Set.InjOn V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  intro x hx y hy hxy
  rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
  rcases Set.mem_iUnion.mp hy with ⟨k, hyk⟩
  have hmk : m = k := by
    by_contra hne
    exact
      Set.disjoint_left.mp
        (V.pairwiseDisjoint_fullAdelicCliffordGeneralSpinLeftQuotientPiece hne)
        hxm.1 (by simpa [hxy] using hyk.1)
  subst k
  exact
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_sliceSource m
      hxm.2 hyk.2 hxy

theorem existsUnique_mem_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    ∃! x : V.FullAdelicCliffordGeneralSpinGroup,
      x ∈ V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain ∧
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap x = y := by
  have hy := Set.mem_univ y
  rw [← V.fullAdelicCliffordGeneralSpinLeftQuotientMap_image_fundamentalDomain]
    at hy
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_fundamentalDomain
      hz.1 hx (hz.2.trans hxy.symm)

theorem existsUnique_fullAdelicCliffordGeneralSpinFundamentalDomainRepresentative
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    ∃! z : V.FullAdelicCliffordGeneralSpinGroup,
      z ∈ V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain ∧
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap z =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap x :=
  V.existsUnique_mem_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
    (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x)

end RationalQuadraticSpaceMatrix
