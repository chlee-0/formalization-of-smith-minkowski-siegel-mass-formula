import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteDifferentialStabilizerMeasure
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The real/finite lattice stabilizer as an open full-adelic subgroup

The natural full-adelic stabilizer has unrestricted real component and the
compact-open integral stabilizer as its finite component.  Hence it is an
open subgroup.  This module packages the open embedding and the literal
partition of the ambient group by open measurable left cosets.

These are the inputs for a later extension of the subgroup
differential measure by a sum of translated measures.  Merely mapping the
subgroup measure through the subtype inclusion is deliberately not done.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The integral finite-adelic special stabilizer as an open subgroup. -/
def finiteSpecialOrthogonalLatticeOpenSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    OpenSubgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup where
  toSubgroup := L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
  isOpen' := L.isOpen_finiteSpecialOrthogonalLatticeStabilizerSubgroup

/-- The unrestricted-real/integral-finite product as an open subgroup. -/
def realFiniteLatticeStabilizerOpenSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    OpenSubgroup
      (L.ConcreteRealSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :=
  (⊤ : OpenSubgroup L.ConcreteRealSpecialOrthogonalGroup).prod
    L.finiteSpecialOrthogonalLatticeOpenSubgroup

/-- The natural lattice stabilizer as an open subgroup of the concrete
full-adelic special orthogonal group. -/
def fullAdelicRealFiniteLatticeStabilizerOpenSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    OpenSubgroup L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.realFiniteLatticeStabilizerOpenSubgroup.comap
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toMonoidHom
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous

/-- The open subgroup has exactly the full-adelic
stabilizer as its underlying subgroup. -/
@[simp]
theorem fullAdelicRealFiniteLatticeStabilizerOpenSubgroup_toSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    (L.fullAdelicRealFiniteLatticeStabilizerOpenSubgroup :
      Subgroup L.ConcreteFullAdelicSpecialOrthogonalGroup) =
        L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
  rfl

/-- The natural full-adelic real/finite lattice stabilizer is open. -/
theorem isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsOpen
      (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
  change IsOpen
    (L.fullAdelicRealFiniteLatticeStabilizerOpenSubgroup :
      Set L.ConcreteFullAdelicSpecialOrthogonalGroup)
  exact L.fullAdelicRealFiniteLatticeStabilizerOpenSubgroup.isOpen

/-- The natural stabilizer is also closed, as every open subgroup of a
topological group is closed. -/
theorem isClosed_fullAdelicRealFiniteLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsClosed
      (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
  rw [← L.fullAdelicRealFiniteLatticeStabilizerOpenSubgroup_toSubgroup]
  exact L.fullAdelicRealFiniteLatticeStabilizerOpenSubgroup.isClosed

/-- The subtype inclusion of the open stabilizer is an open embedding. -/
theorem fullAdelicRealFiniteLatticeStabilizerSubtype_isOpenEmbedding
    (L : PositiveDefiniteIntegralLattice n) :
    Topology.IsOpenEmbedding
      ((↑) :
        L.fullAdelicRealFiniteLatticeStabilizerSubgroup →
          L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
  L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup.isOpenEmbedding_subtypeVal

/-- The subtype inclusion of the open stabilizer is an open map. -/
theorem fullAdelicRealFiniteLatticeStabilizerSubtype_isOpenMap
    (L : PositiveDefiniteIntegralLattice n) :
    IsOpenMap
      ((↑) :
        L.fullAdelicRealFiniteLatticeStabilizerSubgroup →
          L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
  L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup.isOpenMap_subtype_val

/-- Every left coset of the natural stabilizer is open. -/
theorem isOpen_fullAdelicRealFiniteLatticeStabilizer_leftCoset
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    IsOpen
      ((fun h : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * h) ''
        (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
          Set L.ConcreteFullAdelicSpecialOrthogonalGroup)) := by
  rw [Set.image_mul_left]
  exact
    L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup.preimage
      (continuous_const.mul continuous_id)

/-- Every left coset of the natural stabilizer is measurable. -/
theorem measurableSet_fullAdelicRealFiniteLatticeStabilizer_leftCoset
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    MeasurableSet
      ((fun h : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * h) ''
        (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
          Set L.ConcreteFullAdelicSpecialOrthogonalGroup)) :=
  (L.isOpen_fullAdelicRealFiniteLatticeStabilizer_leftCoset g).measurableSet

/-- The discrete right-quotient index for the ambient partition into left
cosets of the open stabilizer. -/
abbrev FullAdelicRealFiniteLatticeStabilizerCosetIndex
    (L : PositiveDefiniteIntegralLattice n) :=
  L.ConcreteFullAdelicSpecialOrthogonalGroup ⧸
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup

/-- The left coset represented by the canonical quotient representative. -/
def fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    Set L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  (fun h => Quotient.out C * h) ''
    (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
      Set L.ConcreteFullAdelicSpecialOrthogonalGroup)

/-- Membership in the chosen coset is equality with its quotient index. -/
@[simp]
theorem mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.fullAdelicRealFiniteLatticeStabilizerCoset C ↔
      (g :
        L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) = C := by
  letI :
      SMul L.ConcreteFullAdelicSpecialOrthogonalGroup
        L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    instSMulOfMul
  letI :
      SMul L.ConcreteFullAdelicSpecialOrthogonalGroup
        (Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
    ⟨fun a s => (fun x => a * x) '' s⟩
  rw [fullAdelicRealFiniteLatticeStabilizerCoset]
  change
    g ∈ Quotient.out C •
      (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) ↔ _
  rw [← QuotientGroup.eq_class_eq_leftCoset
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup (Quotient.out C)]
  change
    ((g : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
      ((Quotient.out C :
        L.ConcreteFullAdelicSpecialOrthogonalGroup) :
          L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)) ↔ _
  have hout :
      ((Quotient.out C :
        L.ConcreteFullAdelicSpecialOrthogonalGroup) :
          L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) = C :=
    Quotient.out_eq C
  rw [hout]

/-- The chosen left cosets cover the full adelic special orthogonal group. -/
theorem iUnion_fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n) :
    (⋃ C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex,
      L.fullAdelicRealFiniteLatticeStabilizerCoset C) = Set.univ := by
  ext g
  simp

/-- Distinct quotient indices give disjoint chosen left cosets. -/
theorem pairwiseDisjoint_fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n) :
    Pairwise fun
      C D : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
        Disjoint
          (L.fullAdelicRealFiniteLatticeStabilizerCoset C)
          (L.fullAdelicRealFiniteLatticeStabilizerCoset D) := by
  intro C D hCD
  rw [Set.disjoint_left]
  intro g hgC hgD
  rw [L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff] at hgC hgD
  exact hCD (hgC.symm.trans hgD)

/-- Every chosen coset in the partition is open. -/
theorem isOpen_fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    IsOpen (L.fullAdelicRealFiniteLatticeStabilizerCoset C) :=
  L.isOpen_fullAdelicRealFiniteLatticeStabilizer_leftCoset (Quotient.out C)

/-- Every chosen coset in the partition is measurable. -/
theorem measurableSet_fullAdelicRealFiniteLatticeStabilizerCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    MeasurableSet (L.fullAdelicRealFiniteLatticeStabilizerCoset C) :=
  (L.isOpen_fullAdelicRealFiniteLatticeStabilizerCoset C).measurableSet

end PositiveDefiniteIntegralLattice
