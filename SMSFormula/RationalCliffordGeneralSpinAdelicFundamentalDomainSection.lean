import SMSFormula.RationalCliffordGeneralSpinAdelicMeasurableFundamentalDomain
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# A measurable global section of the rational adelic GSpin quotient

The disjoint quotient pieces used to construct the exact measurable
fundamental domain also give a canonical measurable representative of every
left coset. This module builds that representative explicitly by taking the
first disjoint piece containing the quotient point. It then packages the
section as a measurable equivalence with the fundamental-domain subtype.

This is a carrier prerequisite for periodizing an arbitrary quotient measure
back to the ambient adelic group. No quotient disintegration, Haar
proportionality, or normalization scalar is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Every quotient point belongs to one of the disjoint atlas pieces. -/
theorem exists_fullAdelicCliffordGeneralSpinLeftQuotientPiece
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    ∃ m : ℕ, y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m := by
  have hy : y ∈ ⋃ m, V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m := by
    rw [V.iUnion_fullAdelicCliffordGeneralSpinLeftQuotientPiece]
    exact Set.mem_univ y
  simpa only [Set.mem_iUnion] using hy

/-- The first disjoint quotient piece containing a given quotient point. -/
def fullAdelicCliffordGeneralSpinFundamentalPieceIndex
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) : ℕ :=
  by
    classical
    exact Nat.find (V.exists_fullAdelicCliffordGeneralSpinLeftQuotientPiece y)

@[simp]
theorem mem_fullAdelicCliffordGeneralSpinLeftQuotientPiece_fundamentalPieceIndex
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece
      (V.fullAdelicCliffordGeneralSpinFundamentalPieceIndex y) :=
  by
    classical
    exact Nat.find_spec
      (V.exists_fullAdelicCliffordGeneralSpinLeftQuotientPiece y)

/-- Extend the section on one disjoint piece by the ambient identity. Only
its value on the piece is used by the global representative. -/
def fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative
    (m : ℕ)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinGroup := by
  classical
  exact if hy : y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m then
      V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m ⟨y, hy⟩
    else 1

theorem measurable_fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative
    (m : ℕ) :
    Measurable
      (V.fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative m) := by
  classical
  have h := Measurable.dite
    (s := V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m)
    (f := V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m)
    (g := fun _ : {y : V.FullAdelicCliffordGeneralSpinLeftQuotient //
      y ∉ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m} =>
        (1 : V.FullAdelicCliffordGeneralSpinGroup))
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m)
    measurable_const
    (V.measurableSet_fullAdelicCliffordGeneralSpinLeftQuotientPiece m)
  simpa only [fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative]
    using h

theorem fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative_of_mem
    (m : ℕ)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (hy : y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m) :
    V.fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative m y =
      V.fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m ⟨y, hy⟩ := by
  classical
  simp [fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative, hy]

/-- The measurable representative of a rational adelic GSpin left coset in
the fixed exact fundamental domain. -/
def fullAdelicCliffordGeneralSpinFundamentalDomainSection
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative
    (V.fullAdelicCliffordGeneralSpinFundamentalPieceIndex y) y

theorem measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection :
    Measurable V.fullAdelicCliffordGeneralSpinFundamentalDomainSection := by
  classical
  unfold fullAdelicCliffordGeneralSpinFundamentalDomainSection
  unfold fullAdelicCliffordGeneralSpinFundamentalPieceIndex
  exact Measurable.find
    V.measurable_fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative
    V.measurableSet_fullAdelicCliffordGeneralSpinLeftQuotientPiece
    V.exists_fullAdelicCliffordGeneralSpinLeftQuotientPiece

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) = y := by
  let m := V.fullAdelicCliffordGeneralSpinFundamentalPieceIndex y
  let hy : y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m :=
    V.mem_fullAdelicCliffordGeneralSpinLeftQuotientPiece_fundamentalPieceIndex y
  rw [fullAdelicCliffordGeneralSpinFundamentalDomainSection,
    V.fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative_of_mem m y hy]
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_pieceSection m ⟨y, hy⟩

theorem fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y ∈
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  let m := V.fullAdelicCliffordGeneralSpinFundamentalPieceIndex y
  let hy : y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientPiece m :=
    V.mem_fullAdelicCliffordGeneralSpinLeftQuotientPiece_fundamentalPieceIndex y
  rw [fullAdelicCliffordGeneralSpinFundamentalDomainSection,
    V.fullAdelicCliffordGeneralSpinFundamentalPieceRepresentative_of_mem m y hy]
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  rw [← V.range_fullAdelicCliffordGeneralSpinLeftQuotientPieceSection m]
  exact ⟨⟨y, hy⟩, rfl⟩

theorem injective_fullAdelicCliffordGeneralSpinFundamentalDomainSection :
    Function.Injective V.fullAdelicCliffordGeneralSpinFundamentalDomainSection := by
  intro y z hyz
  have := congrArg V.fullAdelicCliffordGeneralSpinLeftQuotientMap hyz
  simpa using this

/-- The global section with its fundamental-domain membership bundled. -/
def fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
  ⟨V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y,
    V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem y⟩

theorem measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype :
    Measurable V.fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype :=
  V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection.subtype_mk

/-- The quotient is equivalent to the fixed exact fundamental-domain subtype
through the explicit global section. -/
def fullAdelicCliffordGeneralSpinFundamentalDomainEquiv :
    V.FullAdelicCliffordGeneralSpinLeftQuotient ≃
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain where
  toFun := V.fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype
  invFun x := V.fullAdelicCliffordGeneralSpinLeftQuotientMap x
  left_inv y :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection y
  right_inv x := by
    apply Subtype.ext
    apply V.fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_fundamentalDomain
    · exact V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem _
    · exact x.2
    · exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection _

theorem measurable_fullAdelicCliffordGeneralSpinFundamentalDomainEquiv :
    Measurable V.fullAdelicCliffordGeneralSpinFundamentalDomainEquiv := by
  change Measurable
    V.fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype
  exact
    V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSectionSubtype

theorem measurable_fullAdelicCliffordGeneralSpinFundamentalDomainEquiv_symm :
    Measurable V.fullAdelicCliffordGeneralSpinFundamentalDomainEquiv.symm :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_measurable.comp
      measurable_subtype_coe

/-- The quotient is measurably equivalent to the fixed exact fundamental-
domain subtype through the explicit global section. -/
def fullAdelicCliffordGeneralSpinFundamentalDomainMeasurableEquiv :
    V.FullAdelicCliffordGeneralSpinLeftQuotient ≃ᵐ
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain where
  toEquiv := V.fullAdelicCliffordGeneralSpinFundamentalDomainEquiv
  measurable_toFun :=
    V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainEquiv
  measurable_invFun :=
    V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainEquiv_symm

@[simp]
theorem coe_fullAdelicCliffordGeneralSpinFundamentalDomainMeasurableEquiv_apply
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (V.fullAdelicCliffordGeneralSpinFundamentalDomainMeasurableEquiv y :
      V.FullAdelicCliffordGeneralSpinGroup) =
      V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y :=
  rfl

end RationalQuadraticSpaceMatrix
