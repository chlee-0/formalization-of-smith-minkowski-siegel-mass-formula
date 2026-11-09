import SMSFormula.RationalIdeleClassCountableSliceAtlas

/-!
# A measurable fundamental domain for rational idele classes

The countable covering atlas is disjointified on the quotient.  Restricting
each local section to its disjoint base produces a measurable subset of the
idele group meeting every rational diagonal coset exactly once.  Its total
Haar mass is not asserted finite.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Set

namespace RationalQuadraticSpaceMatrix

/-- The recursively disjoint part of the `m`-th idele-class base. -/
def rationalIdeleClassPiece (m : ℕ) : Set RationalIdeleClassGroup :=
  disjointed rationalIdeleClassSliceBase m

theorem measurableSet_rationalIdeleClassPiece (m : ℕ) :
    MeasurableSet (rationalIdeleClassPiece m) := by
  apply MeasurableSet.disjointed
  intro k
  exact (isOpen_rationalIdeleClassSliceBase k).measurableSet

theorem rationalIdeleClassPiece_subset_sliceBase (m : ℕ) :
    rationalIdeleClassPiece m ⊆ rationalIdeleClassSliceBase m :=
  disjointed_subset _ _

theorem pairwiseDisjoint_rationalIdeleClassPiece :
    Pairwise (Function.onFun Disjoint rationalIdeleClassPiece) :=
  disjoint_disjointed rationalIdeleClassSliceBase

theorem iUnion_rationalIdeleClassPiece :
    ⋃ m, rationalIdeleClassPiece m = Set.univ := by
  change ⋃ m, disjointed rationalIdeleClassSliceBase m = Set.univ
  rw [iUnion_disjointed, iUnion_rationalIdeleClassSliceBase]

/-- Inclusion of a disjoint quotient piece into its atlas base. -/
def rationalIdeleClassPieceToSliceBase (m : ℕ) :
    C(rationalIdeleClassPiece m, rationalIdeleClassSliceBase m) where
  toFun y := ⟨y, rationalIdeleClassPiece_subset_sliceBase m y.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The local section restricted to the `m`-th disjoint quotient piece. -/
def rationalIdeleClassPieceSection (m : ℕ) :
    C(rationalIdeleClassPiece m, RationalAdeleˣ) :=
  (rationalIdeleClassSliceSection m).comp
    (rationalIdeleClassPieceToSliceBase m)

theorem measurable_rationalIdeleClassPieceSection (m : ℕ) :
    Measurable (rationalIdeleClassPieceSection m) :=
  (rationalIdeleClassPieceSection m).continuous.measurable

@[simp]
theorem rationalIdeleClassQuotientMap_pieceSection
    (m : ℕ) (y : rationalIdeleClassPiece m) :
    rationalIdeleClassQuotientMap (rationalIdeleClassPieceSection m y) = y :=
  rationalIdeleClassQuotientMap_sliceSection m
    (rationalIdeleClassPieceToSliceBase m y)

/-- The source representative piece assigned to the `m`-th quotient piece. -/
def rationalIdeleFundamentalSourcePiece (m : ℕ) : Set RationalAdeleˣ :=
  rationalIdeleClassQuotientMap ⁻¹' rationalIdeleClassPiece m ∩
    rationalIdeleClassSliceSource m

theorem measurableSet_rationalIdeleFundamentalSourcePiece (m : ℕ) :
    MeasurableSet (rationalIdeleFundamentalSourcePiece m) :=
  (measurableSet_rationalIdeleClassPiece m).preimage
      (rationalIdeleClassQuotientMap_isCoveringMap.continuous.measurable) |>.inter
    (isOpen_rationalIdeleClassSliceSource m).measurableSet

theorem pairwiseDisjoint_rationalIdeleFundamentalSourcePiece :
    Pairwise (Function.onFun Disjoint rationalIdeleFundamentalSourcePiece) := by
  intro m k hmk
  change Disjoint (rationalIdeleFundamentalSourcePiece m)
    (rationalIdeleFundamentalSourcePiece k)
  rw [Set.disjoint_left]
  intro x hxm hxk
  exact Set.disjoint_left.mp
    (pairwiseDisjoint_rationalIdeleClassPiece hmk) hxm.1 hxk.1

theorem range_rationalIdeleClassPieceSection (m : ℕ) :
    Set.range (rationalIdeleClassPieceSection m) =
      rationalIdeleFundamentalSourcePiece m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · change rationalIdeleClassQuotientMap
          (rationalIdeleClassPieceSection m y) ∈ rationalIdeleClassPiece m
      rw [rationalIdeleClassQuotientMap_pieceSection]
      exact y.2
    · rw [← range_rationalIdeleClassSliceSection m]
      exact ⟨rationalIdeleClassPieceToSliceBase m y, rfl⟩
  · rintro ⟨hxpiece, hxsource⟩
    let y : rationalIdeleClassPiece m :=
      ⟨rationalIdeleClassQuotientMap x, hxpiece⟩
    refine ⟨y, ?_⟩
    apply rationalIdeleClassQuotientMap_injOn_sliceSource m
    · rw [← range_rationalIdeleClassSliceSection m]
      exact ⟨rationalIdeleClassPieceToSliceBase m y, rfl⟩
    · exact hxsource
    · exact rationalIdeleClassQuotientMap_pieceSection m y

/-- The exact measurable fundamental domain for the rational diagonal in the
idele group. -/
def rationalIdeleMeasurableFundamentalDomain : Set RationalAdeleˣ :=
  ⋃ m, rationalIdeleFundamentalSourcePiece m

theorem measurableSet_rationalIdeleMeasurableFundamentalDomain :
    MeasurableSet rationalIdeleMeasurableFundamentalDomain :=
  MeasurableSet.iUnion measurableSet_rationalIdeleFundamentalSourcePiece

theorem rationalIdeleClassQuotientMap_image_fundamentalDomain :
    rationalIdeleClassQuotientMap '' rationalIdeleMeasurableFundamentalDomain =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hyUnion : y ∈ ⋃ m, rationalIdeleClassPiece m := by
    rw [iUnion_rationalIdeleClassPiece]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hyUnion with ⟨m, hym⟩
  let ym : rationalIdeleClassPiece m := ⟨y, hym⟩
  refine ⟨rationalIdeleClassPieceSection m ym,
    Set.mem_iUnion.mpr ⟨m, ?_⟩, ?_⟩
  · rw [← range_rationalIdeleClassPieceSection m]
    exact ⟨ym, rfl⟩
  · exact rationalIdeleClassQuotientMap_pieceSection m ym

theorem rationalIdeleClassQuotientMap_injOn_fundamentalDomain :
    Set.InjOn rationalIdeleClassQuotientMap
      rationalIdeleMeasurableFundamentalDomain := by
  intro x hx y hy hxy
  rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
  rcases Set.mem_iUnion.mp hy with ⟨k, hyk⟩
  have hmk : m = k := by
    by_contra hne
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_rationalIdeleClassPiece hne)
      hxm.1 (by simpa [hxy] using hyk.1)
  subst k
  exact rationalIdeleClassQuotientMap_injOn_sliceSource m
    hxm.2 hyk.2 hxy

theorem existsUnique_mem_rationalIdeleMeasurableFundamentalDomain
    (y : RationalIdeleClassGroup) :
    ∃! x : RationalAdeleˣ,
      x ∈ rationalIdeleMeasurableFundamentalDomain ∧
        rationalIdeleClassQuotientMap x = y := by
  have hy := Set.mem_univ y
  rw [← rationalIdeleClassQuotientMap_image_fundamentalDomain] at hy
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact rationalIdeleClassQuotientMap_injOn_fundamentalDomain
    hz.1 hx (hz.2.trans hxy.symm)

theorem existsUnique_rationalIdeleFundamentalDomainRepresentative
    (x : RationalAdeleˣ) :
    ∃! z : RationalAdeleˣ,
      z ∈ rationalIdeleMeasurableFundamentalDomain ∧
        rationalIdeleClassQuotientMap z = rationalIdeleClassQuotientMap x :=
  existsUnique_mem_rationalIdeleMeasurableFundamentalDomain
    (rationalIdeleClassQuotientMap x)

end RationalQuadraticSpaceMatrix
