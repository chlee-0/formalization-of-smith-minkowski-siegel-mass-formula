import SMSFormula.RationalCliffordSpinCandidateAdelicCountableSliceAtlas

/-!
# A measurable fundamental domain for the rational adelic Spin quotient

The countable quotient-slice atlas is recursively disjointified on the
quotient.  Pulling each disjoint quotient piece back inside its assigned open
source slice gives a measurable subset of the full-adelic Spin candidate.
Their countable union meets every rational left coset exactly once.

This is a carrier-level measurable fundamental domain.  No periodization
identity, quotient-measure formula, invariant-differential normalization,
condition (K), Ono comparison, or Spin Tamagawa volume is proved here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Disjoint quotient pieces -/

/-- The recursively disjoint part of the `m`-th quotient base. -/
def fullAdelicCliffordSpinCandidateLeftQuotientPiece (m : ℕ) :
    Set V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  disjointed V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m

/-- Every disjoint quotient piece is measurable for the existing
map-generated quotient measurable structure. -/
theorem measurableSet_fullAdelicCliffordSpinCandidateLeftQuotientPiece
    (m : ℕ) :
    MeasurableSet (V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m) := by
  apply MeasurableSet.disjointed
  intro k
  exact
    (V.isOpen_fullAdelicCliffordSpinCandidateLeftQuotientSliceBase k).measurableSet

/-- The `m`-th disjoint piece remains in the `m`-th quotient base. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientPiece_subset_sliceBase
    (m : ℕ) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m ⊆
      V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m :=
  disjointed_subset _ _

/-- The recursively disjoint quotient pieces are pairwise disjoint. -/
theorem pairwiseDisjoint_fullAdelicCliffordSpinCandidateLeftQuotientPiece :
    Pairwise (Function.onFun Disjoint
      V.fullAdelicCliffordSpinCandidateLeftQuotientPiece) :=
  disjoint_disjointed V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase

/-- The recursively disjoint quotient pieces still cover the whole
quotient. -/
theorem iUnion_fullAdelicCliffordSpinCandidateLeftQuotientPiece :
    ⋃ m, V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m = Set.univ := by
  change ⋃ m, disjointed
    V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m = Set.univ
  rw [iUnion_disjointed,
    V.iUnion_fullAdelicCliffordSpinCandidateLeftQuotientSliceBase]

/-! ## Sections restricted to the disjoint pieces -/

/-- The canonical continuous inclusion of a disjoint quotient piece into its
assigned open atlas base. -/
def fullAdelicCliffordSpinCandidateLeftQuotientPieceToSliceBase (m : ℕ) :
    C(V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m,
      V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m) where
  toFun y :=
    ⟨y, V.fullAdelicCliffordSpinCandidateLeftQuotientPiece_subset_sliceBase m
      y.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The continuous local section restricted to the `m`-th disjoint quotient
piece. -/
def fullAdelicCliffordSpinCandidateLeftQuotientPieceSection (m : ℕ) :
    C(V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m,
      V.FullAdelicCliffordSpinCandidateGroup) :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSection m).comp
    (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceToSliceBase m)

/-- The restricted section is measurable for the inherited measurable
structures. -/
theorem measurable_fullAdelicCliffordSpinCandidateLeftQuotientPieceSection
    (m : ℕ) :
    Measurable
      (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m) :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m).continuous.measurable

@[simp]
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_pieceSection
    (m : ℕ)
    (y : V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m y) = y :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_sliceSection m
    (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceToSliceBase m y)

/-- The source representative piece assigned to the `m`-th disjoint quotient
piece.  The intersection with the selected source slice fixes one lift in
each fiber. -/
def fullAdelicCliffordSpinCandidateFundamentalSourcePiece (m : ℕ) :
    Set V.FullAdelicCliffordSpinCandidateGroup :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap ⁻¹'
      V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m ∩
    V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m

/-- Every source representative piece is measurable in the Borel full-adelic
carrier. -/
theorem measurableSet_fullAdelicCliffordSpinCandidateFundamentalSourcePiece
    (m : ℕ) :
    MeasurableSet
      (V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece m) :=
  (V.measurableSet_fullAdelicCliffordSpinCandidateLeftQuotientPiece m).preimage
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap_measurable |>.inter
    (V.isOpen_fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m).measurableSet

/-- The source representative pieces are pairwise disjoint. -/
theorem pairwiseDisjoint_fullAdelicCliffordSpinCandidateFundamentalSourcePiece :
    Pairwise (Function.onFun Disjoint
      V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece) := by
  intro m k hmk
  change Disjoint
    (V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece m)
    (V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece k)
  rw [Set.disjoint_left]
  intro x hxm hxk
  exact
    Set.disjoint_left.mp
      (V.pairwiseDisjoint_fullAdelicCliffordSpinCandidateLeftQuotientPiece hmk)
      hxm.1 hxk.1

/-- The source piece is exactly the range of the restricted local section. -/
theorem range_fullAdelicCliffordSpinCandidateLeftQuotientPieceSection
    (m : ℕ) :
    Set.range
        (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m) =
      V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · change V.fullAdelicCliffordSpinCandidateLeftQuotientMap
          (V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m y) ∈
        V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m
      rw [V.fullAdelicCliffordSpinCandidateLeftQuotientMap_pieceSection]
      exact y.2
    · rw [← V.range_fullAdelicCliffordSpinCandidateLeftQuotientSliceSection m]
      exact ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientPieceToSliceBase m y,
        rfl⟩
  · rintro ⟨hxpiece, hxsource⟩
    let y : V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m :=
      ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientMap x, hxpiece⟩
    refine ⟨y, ?_⟩
    apply V.fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_sliceSource m
    · rw [← V.range_fullAdelicCliffordSpinCandidateLeftQuotientSliceSection m]
      exact ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientPieceToSliceBase m y,
        rfl⟩
    · exact hxsource
    · exact
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap_pieceSection m y

/-! ## The global measurable fundamental domain -/

/-- The countable union of the disjoint source representative pieces. -/
def fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain :
    Set V.FullAdelicCliffordSpinCandidateGroup :=
  ⋃ m, V.fullAdelicCliffordSpinCandidateFundamentalSourcePiece m

/-- The chosen full-adelic fundamental domain is measurable. -/
theorem measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain :
    MeasurableSet V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain :=
  MeasurableSet.iUnion
    V.measurableSet_fullAdelicCliffordSpinCandidateFundamentalSourcePiece

/-- Every quotient point has a representative in the measurable fundamental
domain. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_image_fundamentalDomain :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap ''
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hyUnion :
      y ∈ ⋃ m, V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m := by
    rw [V.iUnion_fullAdelicCliffordSpinCandidateLeftQuotientPiece]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hyUnion with ⟨m, hym⟩
  let ym : V.fullAdelicCliffordSpinCandidateLeftQuotientPiece m := ⟨y, hym⟩
  refine ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m ym,
    Set.mem_iUnion.mpr ⟨m, ?_⟩, ?_⟩
  · rw [← V.range_fullAdelicCliffordSpinCandidateLeftQuotientPieceSection m]
    exact ⟨ym, rfl⟩
  · exact
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap_pieceSection m ym

/-- The quotient map is injective on the measurable fundamental domain. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_fundamentalDomain :
    Set.InjOn V.fullAdelicCliffordSpinCandidateLeftQuotientMap
      V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  intro x hx y hy hxy
  rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
  rcases Set.mem_iUnion.mp hy with ⟨k, hyk⟩
  have hmk : m = k := by
    by_contra hne
    exact
      Set.disjoint_left.mp
        (V.pairwiseDisjoint_fullAdelicCliffordSpinCandidateLeftQuotientPiece hne)
        hxm.1 (by simpa [hxy] using hyk.1)
  subst k
  exact
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_sliceSource m
      hxm.2 hyk.2 hxy

/-- Every rational left coset meets the measurable fundamental domain in
exactly one point. -/
theorem existsUnique_mem_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    ∃! x : V.FullAdelicCliffordSpinCandidateGroup,
      x ∈ V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain ∧
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap x = y := by
  have hy := Set.mem_univ y
  rw [← V.fullAdelicCliffordSpinCandidateLeftQuotientMap_image_fundamentalDomain]
    at hy
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_fundamentalDomain
      hz.1 hx (hz.2.trans hxy.symm)

/-- Equivalently, every full-adelic point has a unique representative of its
rational orbit in the measurable fundamental domain. -/
theorem existsUnique_fundamentalDomainRepresentative
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    ∃! z : V.FullAdelicCliffordSpinCandidateGroup,
      z ∈ V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain ∧
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap z =
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap x :=
  V.existsUnique_mem_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
    (V.fullAdelicCliffordSpinCandidateLeftQuotientMap x)

end RationalQuadraticSpaceMatrix
