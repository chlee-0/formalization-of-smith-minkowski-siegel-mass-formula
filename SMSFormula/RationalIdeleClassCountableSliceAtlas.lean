import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Covering.Quotient
import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalIdeleClassTopology

/-!
# A countable local-section atlas for rational idele classes

The rational diagonal is discrete and the idele group is commutative, so the
literal quotient map to rational idele classes is a covering map.  Second
countability of the quotient then extracts a countable family of open local
sections.  This is the topological input for constructing the non-finite
idele-class Weil quotient at a prescribed ambient Haar scale.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Set Topology

namespace RationalQuadraticSpaceMatrix

/-- Rational ideles inherit second countability from their closed-coordinate
embedding into the adele ring and its opposite. -/
noncomputable instance rationalIdeleSecondCountableTopology :
    SecondCountableTopology RationalAdeleˣ := by
  letI : SecondCountableTopology RationalAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- Rational ideles are locally compact in their intrinsic unit topology. -/
noncomputable instance rationalIdeleLocallyCompactSpace :
    LocallyCompactSpace RationalAdeleˣ := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  infer_instance

local instance : MulAction RationalAdeleˣ RationalAdeleˣ :=
  Monoid.toMulAction RationalAdeleˣ

local instance : MulAction rationalIdeleDiagonalSubgroup RationalAdeleˣ :=
  Subgroup.instMulAction

/-- The rational diagonal is countable because it is the image of the
countable group of rational units. -/
theorem rationalIdeleDiagonalSubgroup_countable :
    Countable rationalIdeleDiagonalSubgroup := by
  letI : Countable ℚˣ :=
    Function.Injective.countable (f := fun q : ℚˣ ↦ (q : ℚ)) Units.val_injective
  let diagonalLift : ℚˣ → rationalIdeleDiagonalSubgroup :=
    fun q ↦
      ⟨rationalUnitFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
  apply Function.Surjective.countable (f := diagonalLift)
  intro gamma
  rcases gamma.2 with ⟨q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

/-- The literal rational-idele quotient map is a local homeomorphism. -/
theorem rationalIdeleClassQuotientMap_isLocalHomeomorph :
    IsLocalHomeomorph rationalIdeleClassQuotientMap :=
  rationalIdeleClassQuotientMap_isCoveringMap.isLocalHomeomorph

/-- A chosen idele representative of an idele class. -/
noncomputable def rationalIdeleClassLocalLift
    (y : RationalIdeleClassGroup) : RationalAdeleˣ :=
  Function.surjInv (QuotientGroup.mk'_surjective rationalIdeleDiagonalSubgroup) y

@[simp]
theorem rationalIdeleClassQuotientMap_localLift
    (y : RationalIdeleClassGroup) :
    rationalIdeleClassQuotientMap (rationalIdeleClassLocalLift y) = y :=
  Function.rightInverse_surjInv
    (QuotientGroup.mk'_surjective rationalIdeleDiagonalSubgroup) y

/-- A chosen local-homeomorphism chart around each chosen idele lift. -/
noncomputable def rationalIdeleClassLocalChart
    (y : RationalIdeleClassGroup) :
    OpenPartialHomeomorph RationalAdeleˣ RationalIdeleClassGroup :=
  Classical.choose
    (rationalIdeleClassQuotientMap_isLocalHomeomorph
      (rationalIdeleClassLocalLift y))

theorem rationalIdeleClassLocalChart_spec
    (y : RationalIdeleClassGroup) :
    rationalIdeleClassLocalLift y ∈ (rationalIdeleClassLocalChart y).source ∧
      rationalIdeleClassQuotientMap = rationalIdeleClassLocalChart y :=
  Classical.choose_spec
    (rationalIdeleClassQuotientMap_isLocalHomeomorph
      (rationalIdeleClassLocalLift y))

/-- The open quotient base of a chosen local chart. -/
def rationalIdeleClassLocalBase (y : RationalIdeleClassGroup) :
    Set RationalIdeleClassGroup :=
  (rationalIdeleClassLocalChart y).target

theorem isOpen_rationalIdeleClassLocalBase (y : RationalIdeleClassGroup) :
    IsOpen (rationalIdeleClassLocalBase y) :=
  (rationalIdeleClassLocalChart y).open_target

theorem mem_rationalIdeleClassLocalBase (y : RationalIdeleClassGroup) :
    y ∈ rationalIdeleClassLocalBase y := by
  have hsource :=
    (rationalIdeleClassLocalChart y).map_source
      (rationalIdeleClassLocalChart_spec y).1
  rw [← rationalIdeleClassLocalChart_spec y |>.2] at hsource
  simpa using hsource

/-- The continuous inverse section over a chosen local base. -/
noncomputable def rationalIdeleClassLocalSection
    (y : RationalIdeleClassGroup) :
    C(rationalIdeleClassLocalBase y, RationalAdeleˣ) where
  toFun z := (rationalIdeleClassLocalChart y).symm z
  continuous_toFun :=
    continuousOn_iff_continuous_restrict.mp
      (rationalIdeleClassLocalChart y).continuousOn_symm

theorem rationalIdeleClassQuotientMap_localSection
    (y : RationalIdeleClassGroup) (z : rationalIdeleClassLocalBase y) :
    rationalIdeleClassQuotientMap (rationalIdeleClassLocalSection y z) = z := by
  rw [rationalIdeleClassLocalChart_spec y |>.2]
  exact (rationalIdeleClassLocalChart y).right_inv z.2

theorem range_rationalIdeleClassLocalSection (y : RationalIdeleClassGroup) :
    Set.range (rationalIdeleClassLocalSection y) =
      (rationalIdeleClassLocalChart y).source := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (rationalIdeleClassLocalChart y).map_target z.2
  · intro hx
    refine ⟨⟨rationalIdeleClassLocalChart y x,
      (rationalIdeleClassLocalChart y).map_source hx⟩, ?_⟩
    exact (rationalIdeleClassLocalChart y).left_inv hx

private theorem exists_countable_rationalIdeleClassSliceCenters :
    ∃ k : ℕ → RationalIdeleClassGroup,
      ⋃ m, rationalIdeleClassLocalBase (k m) = Set.univ := by
  letI : Nonempty RationalIdeleClassGroup :=
    ⟨rationalIdeleClassQuotientMap 1⟩
  obtain ⟨k, hk⟩ := eq_open_union_nat
    (fun y : RationalIdeleClassGroup ↦ rationalIdeleClassLocalBase y)
    isOpen_rationalIdeleClassLocalBase
  refine ⟨k, hk.trans ?_⟩
  exact Set.eq_univ_of_forall fun y ↦
    Set.mem_iUnion.mpr ⟨y, mem_rationalIdeleClassLocalBase y⟩

/-- Centers of a countable local-section atlas covering idele classes. -/
noncomputable def rationalIdeleClassSliceCenter (m : ℕ) :
    RationalIdeleClassGroup :=
  Classical.choose exists_countable_rationalIdeleClassSliceCenters m

/-- The `m`-th open idele-class base. -/
def rationalIdeleClassSliceBase (m : ℕ) : Set RationalIdeleClassGroup :=
  rationalIdeleClassLocalBase (rationalIdeleClassSliceCenter m)

/-- The `m`-th open idele source slice. -/
def rationalIdeleClassSliceSource (m : ℕ) : Set RationalAdeleˣ :=
  (rationalIdeleClassLocalChart (rationalIdeleClassSliceCenter m)).source

/-- The continuous section over the `m`-th idele-class base. -/
noncomputable def rationalIdeleClassSliceSection (m : ℕ) :
    C(rationalIdeleClassSliceBase m, RationalAdeleˣ) :=
  rationalIdeleClassLocalSection (rationalIdeleClassSliceCenter m)

theorem iUnion_rationalIdeleClassSliceBase :
    ⋃ m, rationalIdeleClassSliceBase m = Set.univ :=
  Classical.choose_spec exists_countable_rationalIdeleClassSliceCenters

theorem isOpen_rationalIdeleClassSliceBase (m : ℕ) :
    IsOpen (rationalIdeleClassSliceBase m) :=
  isOpen_rationalIdeleClassLocalBase _

theorem isOpen_rationalIdeleClassSliceSource (m : ℕ) :
    IsOpen (rationalIdeleClassSliceSource m) :=
  (rationalIdeleClassLocalChart _).open_source

theorem rationalIdeleClassQuotientMap_sliceSection
    (m : ℕ) (z : rationalIdeleClassSliceBase m) :
    rationalIdeleClassQuotientMap (rationalIdeleClassSliceSection m z) = z :=
  rationalIdeleClassQuotientMap_localSection _ z

theorem range_rationalIdeleClassSliceSection (m : ℕ) :
    Set.range (rationalIdeleClassSliceSection m) =
      rationalIdeleClassSliceSource m :=
  range_rationalIdeleClassLocalSection _

theorem rationalIdeleClassQuotientMap_injOn_sliceSource (m : ℕ) :
    Set.InjOn rationalIdeleClassQuotientMap
      (rationalIdeleClassSliceSource m) := by
  intro x hx y hy hxy
  rw [rationalIdeleClassLocalChart_spec _ |>.2] at hxy
  exact (rationalIdeleClassLocalChart _).injOn hx hy hxy

end RationalQuadraticSpaceMatrix
