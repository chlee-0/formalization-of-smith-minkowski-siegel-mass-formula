import SMSFormula.SpecialOrthogonalFullAdelicProperPieceDifferentialMeasure
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialCosetCovariance

/-!
# Identification of transported proper-piece and ambient differential measures

The chosen representative of each proper piece determines a quotient index
for the open real/unrestricted, finite/integral stabilizer.  The discrepancy
between that representative and `Quotient.out` is recorded as a
stabilizer element.  Subgroup differential left invariance absorbs this
adjustment.

Consequently, restriction of the independently constructed one-coset ambient
differential measure to the proper piece is exactly the measure transported
from the restricted real/finite source product.  The same equality is then
stated for the restriction of the full ambient differential measure.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The open-stabilizer quotient index represented by the literal proper
double-coset representative. -/
def concreteFullAdelicProperTransversalRepresentativeCosetIndex
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
  (L.concreteFullAdelicProperTransversalRepresentative C :
    L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)

/-- The chosen coset at the proper representative's quotient index is exactly
its literal left stabilizer coset. -/
theorem fullAdelicRealFiniteLatticeStabilizerCoset_properRepresentative
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.fullAdelicRealFiniteLatticeStabilizerCoset
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C) =
      rightTranslateSliceSet
        L.fullAdelicRealFiniteLatticeStabilizerSubgroup
        (L.concreteFullAdelicProperTransversalRepresentative C)
        Set.univ := by
  ext g
  rw [
    L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff,
    concreteFullAdelicProperTransversalRepresentativeCosetIndex
  ]
  constructor
  · intro hg
    have hmem :
        (L.concreteFullAdelicProperTransversalRepresentative C)⁻¹ * g ∈
          L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
      (QuotientGroup.eq
        (s := L.fullAdelicRealFiniteLatticeStabilizerSubgroup)).mp hg.symm
    refine
      ⟨⟨(L.concreteFullAdelicProperTransversalRepresentative C)⁻¹ * g, hmem⟩,
        Set.mem_univ _, ?_⟩
    simp
  · rintro ⟨h, _hh, rfl⟩
    apply
      (QuotientGroup.eq
        (s := L.fullAdelicRealFiniteLatticeStabilizerSubgroup)).mpr
    convert (h⁻¹).property using 1
    all_goals simp

/-- The adjustment between `Quotient.out` and the chosen proper
representative, bundled as an element of the open stabilizer. -/
def concreteFullAdelicProperTransversalRepresentativeAdjustment
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
  ⟨(Quotient.out
      (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C))⁻¹ *
      L.concreteFullAdelicProperTransversalRepresentative C, by
    apply
      (QuotientGroup.eq
        (s := L.fullAdelicRealFiniteLatticeStabilizerSubgroup)).mp
    calc
      ((Quotient.out
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C) :
          L.ConcreteFullAdelicSpecialOrthogonalGroup) :
            L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
          L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C :=
        Quotient.out_eq _
      _ =
          (L.concreteFullAdelicProperTransversalRepresentative C :
            L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :=
        rfl⟩

/-- Multiplying the chosen quotient representative by the
adjustment recovers the proper representative. -/
@[simp]
theorem concreteFullAdelicProperTransversalRepresentativeAdjustment_identity
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Quotient.out
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C) *
        (L.concreteFullAdelicProperTransversalRepresentativeAdjustment C :
          L.ConcreteFullAdelicSpecialOrthogonalGroup) =
      L.concreteFullAdelicProperTransversalRepresentative C := by
  simp [concreteFullAdelicProperTransversalRepresentativeAdjustment]

/-- The ambient one-coset contribution at the proper representative's index
is the direct left translate by that literal representative of the subgroup
differential measure. -/
theorem
    fullAdelicRealFiniteAmbientCosetDifferentialMeasure_properRepresentative_eq_map
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C) =
      Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          L.concreteFullAdelicProperTransversalRepresentative C * h)
        (L.fullAdelicRealFiniteDifferentialStabilizerMeasure P) := by
  let μ :=
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure P
  let a :=
    L.concreteFullAdelicProperTransversalRepresentativeAdjustment C
  let q :=
    L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C
  letI : Measure.IsMulLeftInvariant μ :=
    L.fullAdelicRealFiniteDifferentialStabilizerMeasure_isMulLeftInvariant hP
  have hout :
      Measurable
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out q * h) :=
    (continuous_const.mul continuous_subtype_val).measurable
  have ha :
      Measurable
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup => a * h) :=
    (continuous_const.mul continuous_id).measurable
  rw [
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_eq_map_mul_left P q
  ]
  change
    Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out q * h) μ =
      Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          L.concreteFullAdelicProperTransversalRepresentative C * h) μ
  calc
    Measure.map
        (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
          Quotient.out q * h) μ =
        Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            Quotient.out q * h)
          (Measure.map
            (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup => a * h)
            μ) := by
          rw [map_mul_left_eq_self μ a]
    _ =
        Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            Quotient.out q * (a * h)) μ := by
          simpa only [Function.comp_apply] using
            (Measure.map_map hout ha)
    _ =
        Measure.map
          (fun h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup =>
            L.concreteFullAdelicProperTransversalRepresentative C * h) μ := by
          congr 1
          funext h
          rw [← mul_assoc]
          exact congrArg
            (fun g : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * h)
            (L.concreteFullAdelicProperTransversalRepresentativeAdjustment_identity
              C)

/-- The transported proper-piece differential measure is exactly the
restriction of its independently constructed ambient one-coset contribution.
-/
theorem
    concreteFullAdelicProperTransversalPieceDifferentialMeasure_eq_restrict_coset
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C =
      (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C)).restrict
          (L.concreteFullAdelicProperTransversalPiece C) := by
  let e :=
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
  let μ :=
    L.realFiniteDifferentialStabilizerProductMeasure P
  let r :=
    L.concreteFullAdelicProperTransversalRepresentative C
  let f :
      L.fullAdelicRealFiniteLatticeStabilizerSubgroup →
        L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    fun h => r * h
  have hf : Measurable f :=
    (continuous_const.mul continuous_subtype_val).measurable
  have he : Measurable (fun x => e x) := by
    letI : SecondCountableTopology
        L.ConcreteRealSpecialOrthogonalGroup :=
      L.concreteRealSpecialOrthogonalGroup_secondCountable
    letI : OpensMeasurableSpace
        L.ConcreteRealSpecialOrthogonalGroup := by
      infer_instance
    letI : OpensMeasurableSpace
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
      infer_instance
    letI : SecondCountableTopologyEither
        L.ConcreteRealSpecialOrthogonalGroup
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
      ⟨Or.inl L.concreteRealSpecialOrthogonalGroup_secondCountable⟩
    letI : OpensMeasurableSpace
        (L.ConcreteRealSpecialOrthogonalGroup ×
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) := by
      infer_instance
    exact e.continuous.measurable
  rw [
    L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_properRepresentative_eq_map
      hP C
  ]
  unfold fullAdelicRealFiniteDifferentialStabilizerMeasure
  rw [Measure.map_map hf he]
  have hmap :
      f ∘
        (fun x :
          L.ConcreteRealSpecialOrthogonalGroup ×
            L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
          e x) =
      L.concreteFullAdelicProperTransversalPieceSourceMap C := by
    funext x
    rfl
  rw [hmap]
  rw [
    Measure.restrict_map
      (L.concreteFullAdelicProperTransversalPieceSourceMap_measurableEmbedding
        C).measurable
      (L.concreteFullAdelicProperTransversalPiece_measurableSet C),
    L.preimage_concreteFullAdelicProperTransversalPieceSource C
  ]
  rfl

/-- Equivalently, each transported proper-piece measure is the restriction
of the full ambient differential measure to that piece. -/
theorem
    concreteFullAdelicProperTransversalPieceDifferentialMeasure_eq_restrict_ambient
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C =
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
        (L.concreteFullAdelicProperTransversalPiece C) := by
  rw [
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_eq_restrict_coset
      hP C
  ]
  symm
  calc
    (L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
        (L.concreteFullAdelicProperTransversalPiece C) =
      ((L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
        (L.fullAdelicRealFiniteLatticeStabilizerCoset
          (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C))).restrict
            (L.concreteFullAdelicProperTransversalPiece C) := by
      rw [Measure.restrict_restrict_of_subset]
      rw [L.fullAdelicRealFiniteLatticeStabilizerCoset_properRepresentative C]
      exact
        L.concreteFullAdelicProperTransversalPiece_subset_stabilizer_leftCoset C
    _ =
      (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P
        (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C)).restrict
          (L.concreteFullAdelicProperTransversalPiece C) := by
      rw [
        L.restrict_fullAdelicSpecialOrthogonalDifferentialMeasure_coset P
          (L.concreteFullAdelicProperTransversalRepresentativeCosetIndex C)
      ]

end PositiveDefiniteIntegralLattice
