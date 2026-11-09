import Mathlib.Topology.Compactness.Lindelof
import SMSFormula.RationalCliffordSpinCandidateAdelicLocalQuotientSlice

/-!
# A countable local-section atlas for the rational adelic Spin quotient

The rational quotient map is a local homeomorphism and its target is second
countable.  This file chooses one local chart over every quotient point and
uses hereditary Lindelöfness to extract a countable subcover.  The resulting
atlas has continuous local sections whose ranges are open source slices and
whose nontrivial rational translates are disjoint.

No global selector or measurable fundamental domain is constructed.  In
particular, the countable charts are not recursively disjointified here and no
periodization or quotient-measure statement is made.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## A local chart and section at every quotient point -/

/-- A chosen full-adelic lift of a rational quotient point. -/
noncomputable def fullAdelicCliffordSpinCandidateLeftQuotientLocalLift
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.FullAdelicCliffordSpinCandidateGroup :=
  Function.surjInv
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap.surjective y

@[simp]
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_localLift
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalLift y) = y :=
  Function.rightInverse_surjInv
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap.surjective y

/-- A chosen local-homeomorphism chart around a chosen lift of each quotient
point. -/
noncomputable def fullAdelicCliffordSpinCandidateLeftQuotientLocalChart
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    OpenPartialHomeomorph V.FullAdelicCliffordSpinCandidateGroup
      V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  Classical.choose
    (V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isLocalHomeomorph
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalLift y))

theorem fullAdelicCliffordSpinCandidateLeftQuotientLocalChart_spec
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientLocalLift y ∈
        (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).source ∧
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap =
        V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y :=
  Classical.choose_spec
    (V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isLocalHomeomorph
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalLift y))

/-- The open quotient neighborhood of the chosen chart. -/
def fullAdelicCliffordSpinCandidateLeftQuotientLocalBase
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    Set V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).target

theorem isOpen_fullAdelicCliffordSpinCandidateLeftQuotientLocalBase
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    IsOpen (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y) :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).open_target

theorem mem_fullAdelicCliffordSpinCandidateLeftQuotientLocalBase
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    y ∈ V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y := by
  have hsource :=
    (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).map_source
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart_spec y).1
  rw [← V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart_spec y |>.2]
    at hsource
  simpa using hsource

/-- The continuous inverse section of the chosen local chart. -/
noncomputable def fullAdelicCliffordSpinCandidateLeftQuotientLocalSection
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    C(V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y,
      V.FullAdelicCliffordSpinCandidateGroup) where
  toFun z :=
    (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).symm z
  continuous_toFun :=
    continuousOn_iff_continuous_restrict.mp
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).continuousOn_symm

theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_localSection
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient)
    (z : V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalSection y z) = z := by
  rw [V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart_spec y |>.2]
  exact
    (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).right_inv z.2

theorem range_fullAdelicCliffordSpinCandidateLeftQuotientLocalSection
    (y : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    Set.range (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalSection y) =
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).source := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).map_target z.2
  · intro hx
    refine ⟨⟨
      V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y x,
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).map_source hx⟩, ?_⟩
    exact
      (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart y).left_inv hx

/-! ## Countable extraction -/

private theorem exists_countable_fullAdelicCliffordSpinCandidateLeftQuotientSliceCenters :
    ∃ k : ℕ → V.FullAdelicCliffordSpinCandidateLeftQuotient,
      ⋃ m, V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase (k m) = Set.univ := by
  letI : Nonempty V.FullAdelicCliffordSpinCandidateLeftQuotient :=
    ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientMap 1⟩
  obtain ⟨k, hk⟩ := eq_open_union_nat
    (fun y : V.FullAdelicCliffordSpinCandidateLeftQuotient =>
      V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y)
    V.isOpen_fullAdelicCliffordSpinCandidateLeftQuotientLocalBase
  refine ⟨k, hk.trans ?_⟩
  exact Set.eq_univ_of_forall fun y =>
    Set.mem_iUnion.mpr
      ⟨y, V.mem_fullAdelicCliffordSpinCandidateLeftQuotientLocalBase y⟩

/-- Centers of a countable subfamily of the local charts covering the entire
rational quotient. -/
noncomputable def fullAdelicCliffordSpinCandidateLeftQuotientSliceCenter
    (m : ℕ) : V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  Classical.choose
    V.exists_countable_fullAdelicCliffordSpinCandidateLeftQuotientSliceCenters m

/-- The `m`-th open base in the countable quotient slice atlas. -/
def fullAdelicCliffordSpinCandidateLeftQuotientSliceBase (m : ℕ) :
    Set V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientLocalBase
    (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceCenter m)

/-- The `m`-th open source slice in the full-adelic Spin carrier. -/
def fullAdelicCliffordSpinCandidateLeftQuotientSliceSource (m : ℕ) :
    Set V.FullAdelicCliffordSpinCandidateGroup :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart
    (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceCenter m)).source

/-- The continuous section over the `m`-th countable quotient base. -/
noncomputable def fullAdelicCliffordSpinCandidateLeftQuotientSliceSection
    (m : ℕ) :
    C(V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m,
      V.FullAdelicCliffordSpinCandidateGroup) :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientLocalSection
    (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceCenter m)

theorem iUnion_fullAdelicCliffordSpinCandidateLeftQuotientSliceBase :
    ⋃ m, V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m = Set.univ :=
  Classical.choose_spec
    V.exists_countable_fullAdelicCliffordSpinCandidateLeftQuotientSliceCenters

theorem isOpen_fullAdelicCliffordSpinCandidateLeftQuotientSliceBase (m : ℕ) :
    IsOpen (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m) :=
  V.isOpen_fullAdelicCliffordSpinCandidateLeftQuotientLocalBase _

theorem isOpen_fullAdelicCliffordSpinCandidateLeftQuotientSliceSource (m : ℕ) :
    IsOpen (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m) :=
  (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart _).open_source

theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_sliceSection
    (m : ℕ)
    (z : V.fullAdelicCliffordSpinCandidateLeftQuotientSliceBase m) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSection m z) = z :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_localSection _ z

theorem range_fullAdelicCliffordSpinCandidateLeftQuotientSliceSection (m : ℕ) :
    Set.range (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSection m) =
      V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m :=
  V.range_fullAdelicCliffordSpinCandidateLeftQuotientLocalSection _

theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_sliceSource
    (m : ℕ) :
    Set.InjOn V.fullAdelicCliffordSpinCandidateLeftQuotientMap
      (V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m) := by
  intro x hx y hy hxy
  rw [V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart_spec _ |>.2]
    at hxy
  exact
    (V.fullAdelicCliffordSpinCandidateLeftQuotientLocalChart _).injOn hx hy hxy

/-- Distinct rational translates of every selected source slice are
disjoint. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientSliceSource_translate_disjoint
    (m : ℕ)
    (gamma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup) :
    (((fun x : V.FullAdelicCliffordSpinCandidateGroup =>
        (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x) ''
          V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m) ∩
        V.fullAdelicCliffordSpinCandidateLeftQuotientSliceSource m).Nonempty →
      gamma = 1 := by
  rintro ⟨z, ⟨x, hx, rfl⟩, hgammax⟩
  have hfixed :
      (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x = x :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_sliceSource m
      hgammax hx
      (leftCosetMap_gamma_mul
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup gamma x)
  apply Subtype.ext
  have h := congrArg
    (fun z : V.FullAdelicCliffordSpinCandidateGroup => z * x⁻¹) hfixed
  simpa [mul_assoc] using h

end RationalQuadraticSpaceMatrix
