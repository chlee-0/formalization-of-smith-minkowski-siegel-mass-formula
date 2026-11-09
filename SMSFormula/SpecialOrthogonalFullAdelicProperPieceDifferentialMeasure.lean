import SMSFormula.SpecialOrthogonalFullAdelicProperPieceSourceMeasure

/-!
# Differential measure transported to one full-adelic proper piece

The real/finite differential product is restricted to one
unrestricted-real times selected-finite source subset and pushed through the
proper representative-translation map.  The resulting ambient measure has
the exact source mass and is supported on precisely the
corresponding proper piece.

This module does not identify the transported measure with a restriction of
the ambient full-adelic differential coset measure.  No sum over proper
pieces, proper-domain volume, reference-Haar comparison, or Tamagawa theorem
occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The restricted real/finite source-product measure transported to one
full-adelic proper piece. -/
noncomputable def concreteFullAdelicProperTransversalPieceDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Measure L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  Measure.map
    (L.concreteFullAdelicProperTransversalPieceSourceMap C)
    ((L.realFiniteDifferentialStabilizerProductMeasure P).restrict
      (L.concreteFullAdelicProperTransversalPieceSource C))

/-- The proper-piece source map is a measurable embedding. -/
theorem
    concreteFullAdelicProperTransversalPieceSourceMap_measurableEmbedding
    (L : PositiveDefiniteIntegralLattice n)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    MeasurableEmbedding
      (L.concreteFullAdelicProperTransversalPieceSourceMap C) := by
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
  have hstabilizer :
      MeasurableEmbedding
        (fun x :
            L.ConcreteRealSpecialOrthogonalGroup ×
              L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
          (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv x).1) :=
    (MeasurableEmbedding.subtype_coe
      L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup.measurableSet).comp
        (L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv.toHomeomorph
          |>.toMeasurableEquiv.measurableEmbedding)
  have htranslate :
      MeasurableEmbedding
        (Homeomorph.mulLeft
          (L.concreteFullAdelicProperTransversalRepresentative C)) :=
    (Homeomorph.mulLeft
      (L.concreteFullAdelicProperTransversalRepresentative C))
        |>.toMeasurableEquiv.measurableEmbedding
  simpa [concreteFullAdelicProperTransversalPieceSourceMap,
    Function.comp_def] using htranslate.comp hstabilizer

/-- Transport to a proper piece preserves the mass of its literal source
subset. -/
@[simp]
theorem concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
        Set.univ =
      L.realFiniteDifferentialStabilizerProductMeasure P
        (L.concreteFullAdelicProperTransversalPieceSource C) := by
  unfold concreteFullAdelicProperTransversalPieceDifferentialMeasure
  rw [
    Measure.map_apply
      (L.concreteFullAdelicProperTransversalPieceSourceMap_measurableEmbedding
        C).measurable
      MeasurableSet.univ,
    Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter
  ]

/-- The transported proper-piece measure has the literal real total mass
times the finite differential selector mass. -/
theorem
    concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ_eq_real_mul_selector
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
        Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
          (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
            (Quot.out C)) := by
  rw [
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ P C,
    L.realFiniteDifferentialStabilizerProductMeasure_properPieceSource hP C
  ]

/-- The exact named-volume and stabilizer-cardinality form of the transported
proper-piece total mass. -/
theorem
    concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ_eq_volume
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
        Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal
            (1 / (Nat.card
              (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
                (Quot.out C)) :
              ℝ))) := by
  rw [
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ P C,
    L.realFiniteDifferentialStabilizerProductMeasure_properPieceSource_eq_volume
      hP C
  ]

/-- The transported proper-piece measure vanishes on every measurable set
disjoint from its selected proper piece. -/
theorem
    concreteFullAdelicProperTransversalPieceDifferentialMeasure_apply_eq_zero_of_disjoint
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet)
    {A : Set L.ConcreteFullAdelicSpecialOrthogonalGroup}
    (hA : MeasurableSet A)
    (hdisj : Disjoint A (L.concreteFullAdelicProperTransversalPiece C)) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C A = 0 := by
  unfold concreteFullAdelicProperTransversalPieceDifferentialMeasure
  have hmap :
      Measurable
        (L.concreteFullAdelicProperTransversalPieceSourceMap C) :=
    (L.concreteFullAdelicProperTransversalPieceSourceMap_measurableEmbedding
      C).measurable
  rw [Measure.map_apply hmap hA,
    Measure.restrict_apply (hmap hA)]
  have hinter :
      L.concreteFullAdelicProperTransversalPieceSourceMap C ⁻¹' A ∩
          L.concreteFullAdelicProperTransversalPieceSource C =
        ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hxA, hxsource⟩
    exact Set.disjoint_left.mp hdisj hxA <| by
      rw [← L.image_concreteFullAdelicProperTransversalPieceSource C]
      exact ⟨x, hxsource, rfl⟩
  rw [hinter, measure_empty]

/-- In particular, the transported measure gives zero mass to the complement
of its proper piece. -/
theorem concreteFullAdelicProperTransversalPieceDifferentialMeasure_compl
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
        (L.concreteFullAdelicProperTransversalPiece C)ᶜ = 0 := by
  apply
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_apply_eq_zero_of_disjoint
      P C
      (L.concreteFullAdelicProperTransversalPiece_measurableSet C).compl
  rw [Set.disjoint_left]
  intro g hgc hg
  exact hgc hg

/-- Restriction to the corresponding proper piece leaves its transported
measure unchanged. -/
theorem
    restrict_concreteFullAdelicProperTransversalPieceDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    (L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C).restrict
        (L.concreteFullAdelicProperTransversalPiece C) =
      L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_compl P C)

/-- Pulling the transported proper-piece measure back through its measurable
embedding recovers exactly the restricted literal source-product measure. -/
theorem
    comap_concreteFullAdelicProperTransversalPieceDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Measure.comap
        (L.concreteFullAdelicProperTransversalPieceSourceMap C)
        (L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C) =
      (L.realFiniteDifferentialStabilizerProductMeasure P).restrict
        (L.concreteFullAdelicProperTransversalPieceSource C) := by
  unfold concreteFullAdelicProperTransversalPieceDifferentialMeasure
  exact
    (L.concreteFullAdelicProperTransversalPieceSourceMap_measurableEmbedding C)
      |>.comap_map _

end PositiveDefiniteIntegralLattice
