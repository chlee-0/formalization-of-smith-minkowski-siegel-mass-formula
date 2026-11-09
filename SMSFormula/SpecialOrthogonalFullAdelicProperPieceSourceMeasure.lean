import SMSFormula.SpecialOrthogonalFullAdelicProperPieceCarrier

/-!
# Source-product measure of one full-adelic proper piece

For one proper rational double coset, the corresponding finite
selector is paired with the unrestricted real special orthogonal group.  Its
real/finite differential product mass is computed before any
transport to the ambient full-adelic differential measure.

The continuous source map is left multiplication of the assembled
real/finite stabilizer element by the proper representative.  Its
image and preimage identify the source subset exactly with the
full-adelic proper piece.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The unrestricted-real times selected-finite source subset for one proper
full-adelic piece. -/
def concreteFullAdelicProperTransversalPieceSource
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Set
      (L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :=
  Set.univ ×ˢ
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C)

/-- The source subset of every proper piece is measurable. -/
theorem concreteFullAdelicProperTransversalPieceSource_measurableSet
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    MeasurableSet (L.concreteFullAdelicProperTransversalPieceSource C) :=
  MeasurableSet.univ.prod
    (L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet
      (Quot.out C))

/-- The literal product measure of a proper-piece source is the real total
mass times the finite differential selector mass. -/
theorem realFiniteDifferentialStabilizerProductMeasure_properPieceSource
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.realFiniteDifferentialStabilizerProductMeasure P
        (L.concreteFullAdelicProperTransversalPieceSource C) =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
          (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
            (Quot.out C)) := by
  letI : IsFiniteMeasure
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_isFinite
  letI : IsFiniteMeasure
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure_isFinite hP
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite
      L.concreteRealSpecialOrthogonalDifferentialMeasure := by
    infer_instance
  letI : SFinite
      (L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P) := by
    infer_instance
  rw [
    realFiniteDifferentialStabilizerProductMeasure,
    concreteFullAdelicProperTransversalPieceSource,
    Measure.prod_prod
  ]

/-- The exact named-volume and stabilizer-cardinality form of the literal
proper-piece source mass. -/
theorem
    realFiniteDifferentialStabilizerProductMeasure_properPieceSource_eq_volume
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.realFiniteDifferentialStabilizerProductMeasure P
        (L.concreteFullAdelicProperTransversalPieceSource C) =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal
            (1 / (Nat.card
              (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
                (Quot.out C)) :
              ℝ))) := by
  rw [
    L.realFiniteDifferentialStabilizerProductMeasure_properPieceSource hP C,
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice_differential_measure
      (Quot.out C) P
  ]

/-- The continuous source map for a proper piece: assemble a real/finite
stabilizer element, then translate it by the literal proper representative. -/
def concreteFullAdelicProperTransversalPieceSourceMap
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    (L.ConcreteRealSpecialOrthogonalGroup ×
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) →
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  fun x =>
    L.concreteFullAdelicProperTransversalRepresentative C *
      (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv x).1

/-- The proper-piece source map is continuous. -/
theorem continuous_concreteFullAdelicProperTransversalPieceSourceMap
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Continuous (L.concreteFullAdelicProperTransversalPieceSourceMap C) :=
  continuous_const.mul
    (continuous_subtype_val.comp
      L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.continuous)

/-- The real/finite splitting of the source map has the literal translated
component formula. -/
@[simp]
theorem
    fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_properPieceSourceMap
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet)
    (x : L.ConcreteRealSpecialOrthogonalGroup ×
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (L.concreteFullAdelicProperTransversalPieceSourceMap C x) =
      (x.1, (Quot.out C) * x.2.1) := by
  apply Prod.ext
  · simp [concreteFullAdelicProperTransversalPieceSourceMap]
  · simp [concreteFullAdelicProperTransversalPieceSourceMap]

/-- The proper-piece source map is injective. -/
theorem concreteFullAdelicProperTransversalPieceSourceMap_injective
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Function.Injective
      (L.concreteFullAdelicProperTransversalPieceSourceMap C) := by
  intro x y hxy
  have hsplit := congrArg
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv hxy
  apply Prod.ext
  · simpa using congrArg Prod.fst hsplit
  · apply Subtype.ext
    simpa using congrArg Prod.snd hsplit

/-- The image of the literal source subset is exactly the corresponding
full-adelic proper piece. -/
theorem image_concreteFullAdelicProperTransversalPieceSource
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceSourceMap C ''
        L.concreteFullAdelicProperTransversalPieceSource C =
      L.concreteFullAdelicProperTransversalPiece C := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [L.mem_concreteFullAdelicProperTransversalPiece_iff]
    refine ⟨x.2, hx.2, ?_⟩
    exact congrArg Prod.snd
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_properPieceSourceMap
        C x)
  · intro hg
    rcases
        (L.mem_concreteFullAdelicProperTransversalPiece_iff_exists_factor C g).mp
          hg with
      ⟨h, hh, hfactor⟩
    refine
      ⟨((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).1, h),
        ⟨Set.mem_univ _, hh⟩, ?_⟩
    exact hfactor.symm

/-- The exact preimage of a proper piece under its source map is its literal
source subset. -/
theorem preimage_concreteFullAdelicProperTransversalPieceSource
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceSourceMap C ⁻¹'
        L.concreteFullAdelicProperTransversalPiece C =
      L.concreteFullAdelicProperTransversalPieceSource C := by
  ext x
  constructor
  · intro hx
    have himage :
        L.concreteFullAdelicProperTransversalPieceSourceMap C x ∈
          L.concreteFullAdelicProperTransversalPieceSourceMap C ''
            L.concreteFullAdelicProperTransversalPieceSource C := by
      rw [L.image_concreteFullAdelicProperTransversalPieceSource C]
      exact hx
    rcases himage with ⟨y, hy, hxy⟩
    have hyx :=
      L.concreteFullAdelicProperTransversalPieceSourceMap_injective C hxy
    subst y
    exact hy
  · intro hx
    rw [← L.image_concreteFullAdelicProperTransversalPieceSource C]
    exact ⟨x, hx, rfl⟩

end PositiveDefiniteIntegralLattice
