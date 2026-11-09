import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMassSum
import SMSFormula.SpecialOrthogonalFullAdelicProperDomainCarrier

/-!
# Full-adelic carrier pieces of the proper transversal

Each translated finite-adelic proper selector is lifted through the concrete
real/finite splitting with unrestricted real component.  The resulting
full-adelic pieces are measurable, pairwise disjoint, and have union equal to
the full proper domain.

A representative with real/finite components `(1, Quot.out C)` is
also defined.  Every point of the corresponding piece factors through this
representative and an element of the real/unrestricted, finite/integral
stabilizer.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The full-adelic proper piece attached to one proper rational
double coset. -/
def concreteFullAdelicProperTransversalPiece
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Set L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv ⁻¹'
    (Set.univ ×ˢ
      rightTranslateSliceSet
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
        (Quot.out C)
        (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
          (Quot.out C)))

/-- Membership in a lifted proper piece depends exactly on membership of the
finite component in the corresponding translated selector. -/
@[simp]
theorem mem_concreteFullAdelicProperTransversalPiece_iff
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.concreteFullAdelicProperTransversalPiece C ↔
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 ∈
        rightTranslateSliceSet
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
          (Quot.out C)
          (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
            (Quot.out C)) := by
  simp [concreteFullAdelicProperTransversalPiece]

/-- Every lifted proper piece is measurable. -/
theorem concreteFullAdelicProperTransversalPiece_measurableSet
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    MeasurableSet (L.concreteFullAdelicProperTransversalPiece C) := by
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
  have hfinite :
      MeasurableSet
        (rightTranslateSliceSet
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
          (Quot.out C)
          (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
            (Quot.out C))) :=
    rightTranslateSliceSet_measurable_of_subgroup_comap_measurableMul
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (Quot.out C)
      hsub_comap
      L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet
        (Quot.out C))
  exact
    (MeasurableSet.univ.prod hfinite).preimage
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous.measurable

/-- Lifted pieces attached to distinct proper double cosets are disjoint. -/
theorem pairwiseDisjoint_concreteFullAdelicProperTransversalPiece
    (L : PositiveDefiniteIntegralLattice n) :
    Pairwise fun C D : L.ConcreteProperRationalDoubleCosetSet =>
      Disjoint
        (L.concreteFullAdelicProperTransversalPiece C)
        (L.concreteFullAdelicProperTransversalPiece D) := by
  have hfinite :=
    rightTranslateSliceSet_pairwiseDisjoint_of_leftRightDoubleCosetRepresentatives
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C)
      (fun C =>
        L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C))
  intro C D hCD
  rw [Set.disjoint_left]
  intro g hgC hgD
  exact Set.disjoint_left.mp (hfinite hCD)
    ((L.mem_concreteFullAdelicProperTransversalPiece_iff C g).mp hgC)
    ((L.mem_concreteFullAdelicProperTransversalPiece_iff D g).mp hgD)

/-- The union of the lifted translated selector pieces is exactly the
full-adelic proper domain. -/
theorem iUnion_concreteFullAdelicProperTransversalPiece
    (L : PositiveDefiniteIntegralLattice n) :
    (⋃ C : L.ConcreteProperRationalDoubleCosetSet,
      L.concreteFullAdelicProperTransversalPiece C) =
        L.concreteFullAdelicProperTransversal := by
  ext g
  simp [concreteFullAdelicProperTransversalPiece,
    concreteFullAdelicProperTransversal,
    concreteProperFiniteTransversalFundamentalDomain,
    finiteRightTransversalFundamentalDomain]

/-- The literal full-adelic representative whose real component is one and
whose finite component is the selected proper double-coset representative. -/
def concreteFullAdelicProperTransversalRepresentative
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
    (1, Quot.out C)

/-- Splitting the literal proper representative recovers `(1, Quot.out C)`. -/
@[simp]
theorem fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_properRepresentative
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (L.concreteFullAdelicProperTransversalRepresentative C) =
      (1, Quot.out C) :=
  L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.apply_symm_apply
    (1, Quot.out C)

/-- A point belongs to a proper piece exactly when it factors through the
literal representative and a stabilizer element assembled from its real
component and a selected finite local-stabilizer element. -/
theorem mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.concreteFullAdelicProperTransversalPiece C ↔
      ∃ h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup,
        h ∈ L.concreteProperLocalRightStabilizerEmbeddingRealSlice
          (Quot.out C) ∧
        g =
          L.concreteFullAdelicProperTransversalRepresentative C *
            (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
              ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).1,
                h)).1 := by
  constructor
  · intro hg
    rcases
        (L.mem_concreteFullAdelicProperTransversalPiece_iff C g).mp hg with
      ⟨h, hh, hfinite⟩
    refine ⟨h, hh, ?_⟩
    apply
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.injective
    apply Prod.ext
    · simp
    · simpa using hfinite
  · rintro ⟨h, hh, hfactor⟩
    rw [L.mem_concreteFullAdelicProperTransversalPiece_iff]
    refine ⟨h, hh, ?_⟩
    simpa using congrArg
      (fun x =>
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2)
      hfactor

/-- Every lifted proper piece lies in the left coset of the natural
real/unrestricted, finite/integral stabilizer determined by its literal
representative. -/
theorem concreteFullAdelicProperTransversalPiece_subset_stabilizer_leftCoset
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPiece C ⊆
      rightTranslateSliceSet
        L.fullAdelicRealFiniteLatticeStabilizerSubgroup
        (L.concreteFullAdelicProperTransversalRepresentative C)
        Set.univ := by
  intro g hg
  rcases
      (L.mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor C g).mp
        hg with
    ⟨h, _hh, hfactor⟩
  exact
    ⟨L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
        ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).1, h),
      Set.mem_univ _, hfactor⟩

end PositiveDefiniteIntegralLattice
