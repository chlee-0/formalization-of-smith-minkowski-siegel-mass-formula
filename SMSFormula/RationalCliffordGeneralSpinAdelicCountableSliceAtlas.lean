import Mathlib.Topology.Compactness.Lindelof
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalBorel

/-!
# A countable local-section atlas for the rational adelic general-Spin quotient

The rational `GSpin` quotient map is a covering map and its quotient topology
is second countable.  Local inverse charts therefore have a countable
subcover with continuous sections.  This is the source-facing atlas used to
construct an exact measurable fundamental domain; no quotient measure or
crossed disintegration is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Local quotient slices -/

/-- The rational adelic general-Spin quotient map is a local homeomorphism. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_isLocalHomeomorph :
    IsLocalHomeomorph V.fullAdelicCliffordGeneralSpinLeftQuotientMap :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isCoveringMap.isLocalHomeomorph

/-- A chosen full-adelic lift of a rational quotient point. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientLocalLift
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  Function.surjInv
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap.surjective y

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_localLift
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalLift y) = y :=
  Function.rightInverse_surjInv
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap.surjective y

/-- A chosen local-homeomorphism chart around each chosen quotient lift. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientLocalChart
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    OpenPartialHomeomorph V.FullAdelicCliffordGeneralSpinGroup
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Classical.choose
    (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isLocalHomeomorph
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalLift y))

theorem fullAdelicCliffordGeneralSpinLeftQuotientLocalChart_spec
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLocalLift y ∈
        (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).source ∧
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap =
        V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y :=
  Classical.choose_spec
    (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isLocalHomeomorph
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalLift y))

/-- The open quotient base of the chosen chart. -/
def fullAdelicCliffordGeneralSpinLeftQuotientLocalBase
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Set V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).target

theorem isOpen_fullAdelicCliffordGeneralSpinLeftQuotientLocalBase
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    IsOpen (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y) :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).open_target

theorem mem_fullAdelicCliffordGeneralSpinLeftQuotientLocalBase
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    y ∈ V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y := by
  have hsource :=
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).map_source
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart_spec y).1
  rw [← V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart_spec y |>.2]
    at hsource
  simpa using hsource

/-- The continuous inverse section over a chosen local base. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientLocalSection
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    C(V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y,
      V.FullAdelicCliffordGeneralSpinGroup) where
  toFun z :=
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).symm z
  continuous_toFun :=
    continuousOn_iff_continuous_restrict.mp
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).continuousOn_symm

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_localSection
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (z : V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalSection y z) = z := by
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart_spec y |>.2]
  exact
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).right_inv z.2

theorem range_fullAdelicCliffordGeneralSpinLeftQuotientLocalSection
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Set.range (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalSection y) =
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).source := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).map_target z.2
  · intro hx
    refine ⟨⟨
      V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y x,
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).map_source hx⟩,
      ?_⟩
    exact
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart y).left_inv hx

/-! ## Countable extraction -/

private theorem exists_countable_fullAdelicCliffordGeneralSpinLeftQuotientSliceCenters :
    ∃ k : ℕ → V.FullAdelicCliffordGeneralSpinLeftQuotient,
      ⋃ m, V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase (k m) =
        Set.univ := by
  letI : SecondCountableTopology
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology
  letI : Nonempty V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    ⟨V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1⟩
  obtain ⟨k, hk⟩ := eq_open_union_nat
    (fun y : V.FullAdelicCliffordGeneralSpinLeftQuotient =>
      V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y)
    V.isOpen_fullAdelicCliffordGeneralSpinLeftQuotientLocalBase
  refine ⟨k, hk.trans ?_⟩
  exact Set.eq_univ_of_forall fun y =>
    Set.mem_iUnion.mpr
      ⟨y, V.mem_fullAdelicCliffordGeneralSpinLeftQuotientLocalBase y⟩

/-- Centers of a countable local-section atlas covering the quotient. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientSliceCenter
    (m : ℕ) : V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Classical.choose
    V.exists_countable_fullAdelicCliffordGeneralSpinLeftQuotientSliceCenters m

/-- The `m`-th open quotient base. -/
def fullAdelicCliffordGeneralSpinLeftQuotientSliceBase (m : ℕ) :
    Set V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientLocalBase
    (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceCenter m)

/-- The `m`-th open source slice. -/
def fullAdelicCliffordGeneralSpinLeftQuotientSliceSource (m : ℕ) :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart
    (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceCenter m)).source

/-- The continuous section over the `m`-th quotient base. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientSliceSection
    (m : ℕ) :
    C(V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m,
      V.FullAdelicCliffordGeneralSpinGroup) :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientLocalSection
    (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceCenter m)

theorem iUnion_fullAdelicCliffordGeneralSpinLeftQuotientSliceBase :
    ⋃ m, V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m = Set.univ :=
  Classical.choose_spec
    V.exists_countable_fullAdelicCliffordGeneralSpinLeftQuotientSliceCenters

theorem isOpen_fullAdelicCliffordGeneralSpinLeftQuotientSliceBase (m : ℕ) :
    IsOpen (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m) :=
  V.isOpen_fullAdelicCliffordGeneralSpinLeftQuotientLocalBase _

theorem isOpen_fullAdelicCliffordGeneralSpinLeftQuotientSliceSource (m : ℕ) :
    IsOpen (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSource m) :=
  (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart _).open_source

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_sliceSection
    (m : ℕ)
    (z : V.fullAdelicCliffordGeneralSpinLeftQuotientSliceBase m) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSection m z) = z :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientMap_localSection _ z

theorem range_fullAdelicCliffordGeneralSpinLeftQuotientSliceSection (m : ℕ) :
    Set.range (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSection m) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSource m :=
  V.range_fullAdelicCliffordGeneralSpinLeftQuotientLocalSection _

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_sliceSource
    (m : ℕ) :
    Set.InjOn V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (V.fullAdelicCliffordGeneralSpinLeftQuotientSliceSource m) := by
  intro x hx y hy hxy
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart_spec _ |>.2]
    at hxy
  exact
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLocalChart _).injOn hx hy hxy

end RationalQuadraticSpaceMatrix
