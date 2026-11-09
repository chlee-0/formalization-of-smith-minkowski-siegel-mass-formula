import SMSFormula.SpecialOrthogonalRealChartOverlapCompatibility

/-!
# Gluing compatible real differential chart measures

This module extracts a countable centered-chart atlas of the real special
orthogonal group and measurably disjointizes it. It then transports each
chart's invariant differential measure back to its exact source and sums its
restriction to the corresponding disjoint atlas piece.

The construction remains separate from every finite-place
normalization. Cover independence and left invariance require the local
overlap restriction theorem recorded below; no Haar rescaling is used.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator ContDiff ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem realGluing_isSymm_map_algebraMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    (F.map (algebraMap ℚ ℝ)).IsSymm :=
  hF.map _

private theorem realGluing_det_map_algebraMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℝ)).det ≠ 0 := by
  rw [show (F.map (algebraMap ℚ ℝ)).det =
    algebraMap ℚ ℝ F.det by
      simpa [RingHom.mapMatrix_apply] using
        ((algebraMap ℚ ℝ).map_det F).symm]
  intro hz
  apply hdet
  apply (algebraMap ℚ ℝ).injective
  simpa using hz

private theorem realGluing_ringChar_ne_two : ringChar ℝ ≠ 2 := by
  norm_num [ringChar.eq ℝ]

local instance realGluingGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realGluingGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realGluingModelMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realGluingModelBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Countable additivity in the exact form used by chart gluing: a measure is
the sum of its restrictions to any measurable disjoint countable cover. -/
theorem measure_eq_sum_restrict_of_disjoint_iUnion_eq_univ
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) (hs : ∀ k, MeasurableSet (s k))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ k, s k) = Set.univ) :
    μ = Measure.sum (fun k => μ.restrict (s k)) := by
  calc
    μ = μ.restrict Set.univ := Measure.restrict_univ.symm
    _ = μ.restrict (⋃ k, s k) := by rw [hcover]
    _ = Measure.sum (fun k => μ.restrict (s k)) :=
      Measure.restrict_iUnion hdisj hs

/-- The real special-orthogonal matrix group inherits a second-countable
topology from its finite-dimensional matrix ambient space. -/
theorem specialFormPreservingRealGroup_secondCountable
    (F : Matrix (Fin n) (Fin n) ℚ) :
    SecondCountableTopology
      (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  by
    letI : SecondCountableTopology (Fin n → ℝ) :=
      TopologicalSpace.instSecondCountableTopologyForallOfCountable
    letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
      TopologicalSpace.instSecondCountableTopologyForallOfCountable
    letI : SecondCountableTopology
        (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    letI : SecondCountableTopology
        (Matrix (Fin n) (Fin n) ℝ ×
          (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ) :=
      inferInstance
    letI : SecondCountableTopology
        (Matrix (Fin n) (Fin n) ℝ)ˣ :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    letI : SecondCountableTopology
        (formPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
      TopologicalSpace.secondCountableTopology_induced _ _
        ((↑) : formPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) →
          (Matrix (Fin n) (Fin n) ℝ)ˣ)
    exact TopologicalSpace.secondCountableTopology_induced _ _
      ((↑) : specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ)) →
          formPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))

/-- The source of the differential chart centered at `g`, viewed as a subset
of the full real special-orthogonal group. -/
def specialFormPreservingSmoothRealCenteredChartSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Set (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  (specialFormPreservingSmoothRealChart F hF hdet g).source

/-- Every centered differential-chart source is open. -/
theorem isOpen_specialFormPreservingSmoothRealCenteredChartSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    IsOpen (specialFormPreservingSmoothRealCenteredChartSource
      F hF hdet g) :=
  (specialFormPreservingSmoothRealChart F hF hdet g).open_source

/-- Every group point belongs to the differential chart centered at itself. -/
theorem self_mem_specialFormPreservingSmoothRealCenteredChartSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    g ∈ specialFormPreservingSmoothRealCenteredChartSource F hF hdet g := by
  exact
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      (F.map (algebraMap ℚ ℝ)) (realGluing_isSymm_map_algebraMap F hF)
      (realGluing_det_map_algebraMap_ne_zero F hdet)
      realGluing_ringChar_ne_two g

/-- The family of all centered differential charts covers the real group. -/
theorem iUnion_specialFormPreservingSmoothRealCenteredChartSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (⋃ g, specialFormPreservingSmoothRealCenteredChartSource F hF hdet g) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  exact Set.mem_iUnion.2
    ⟨g, self_mem_specialFormPreservingSmoothRealCenteredChartSource
      F hF hdet g⟩

/-- A countable sequence of centers whose chart sources still cover the real
special-orthogonal group. -/
def specialFormPreservingSmoothRealChartCoverCenter
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    ℕ → specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
  letI := specialFormPreservingRealGroup_secondCountable F
  Classical.choose
    (eq_open_union_nat
      (specialFormPreservingSmoothRealCenteredChartSource F hF hdet)
      (isOpen_specialFormPreservingSmoothRealCenteredChartSource F hF hdet))

/-- The selected countable centered atlas covers the full real group. -/
theorem iUnion_specialFormPreservingSmoothRealChartCoverCenter_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (⋃ k, specialFormPreservingSmoothRealCenteredChartSource F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)) =
      Set.univ := by
  letI := specialFormPreservingRealGroup_secondCountable F
  have hcover := Classical.choose_spec
    (eq_open_union_nat
      (specialFormPreservingSmoothRealCenteredChartSource F hF hdet)
      (isOpen_specialFormPreservingSmoothRealCenteredChartSource F hF hdet))
  change (⋃ k, specialFormPreservingSmoothRealCenteredChartSource F hF hdet
    (Classical.choose
      (eq_open_union_nat
        (specialFormPreservingSmoothRealCenteredChartSource F hF hdet)
        (isOpen_specialFormPreservingSmoothRealCenteredChartSource F hF hdet)) k)) =
      Set.univ
  exact hcover.trans
    (iUnion_specialFormPreservingSmoothRealCenteredChartSource F hF hdet)

/-- The measurable disjoint piece assigned to the `k`-th selected chart. -/
def specialFormPreservingSmoothRealChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    Set (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  disjointed
    (fun j => specialFormPreservingSmoothRealCenteredChartSource F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet j)) k

/-- Every disjoint atlas piece is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    MeasurableSet (specialFormPreservingSmoothRealChartCoverPiece
      F hF hdet k) := by
  apply MeasurableSet.disjointed
  intro j
  exact (isOpen_specialFormPreservingSmoothRealCenteredChartSource
    F hF hdet
    (specialFormPreservingSmoothRealChartCoverCenter F hF hdet j)).measurableSet

/-- Each disjoint atlas piece remains inside its assigned chart source. -/
theorem specialFormPreservingSmoothRealChartCoverPiece_subset_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    specialFormPreservingSmoothRealChartCoverPiece F hF hdet k ⊆
      specialFormPreservingSmoothRealCenteredChartSource F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k) :=
  disjointed_subset _ _

/-- The disjoint atlas pieces are pairwise disjoint. -/
theorem pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Pairwise (Function.onFun Disjoint
      (specialFormPreservingSmoothRealChartCoverPiece F hF hdet)) := by
  exact disjoint_disjointed
    (fun j => specialFormPreservingSmoothRealCenteredChartSource F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet j))

/-- The disjoint atlas pieces cover the full real group. -/
theorem iUnion_specialFormPreservingSmoothRealChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (⋃ k, specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) =
      Set.univ := by
  change (⋃ k, disjointed
    (fun j => specialFormPreservingSmoothRealCenteredChartSource F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet j)) k) =
      Set.univ
  rw [iUnion_disjointed,
    iUnion_specialFormPreservingSmoothRealChartCoverCenter_source]

/-- The invariant differential measure on an exact centered chart source,
obtained by transporting the target-density measure through the
chart homeomorphism. -/
def specialFormPreservingSmoothRealChartSourceDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure (specialFormPreservingSmoothRealChart F hF hdet g).source :=
  Measure.map
    (specialFormPreservingSmoothRealChart F hF hdet g).toHomeomorphSourceTarget.symm
    (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g)

/-- Forward chart coordinates recover the local target-density
measure exactly. -/
theorem map_specialFormPreservingSmoothRealChartSourceDensityMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChart F hF hdet g).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartSourceDensityMeasure
          F hF hdet g) =
      specialFormPreservingSmoothRealChartTargetDensityMeasure
        F hF hdet g := by
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact MeasurableEquiv.map_map_symm
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget.toMeasurableEquiv

/-- A chart-source density measure is equivalently the target-density measure
pulled back through the chart homeomorphism. -/
theorem specialFormPreservingSmoothRealChartSourceDensityMeasure_eq_target_comap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet g =
      Measure.comap
        (specialFormPreservingSmoothRealChart
          F hF hdet g).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          F hF hdet g) := by
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget.toMeasurableEquiv.map_symm

/-- Every exact centered source-density measure is sigma-finite. -/
theorem specialFormPreservingSmoothRealChartSourceDensityMeasure_sigmaFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    SigmaFinite
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet g) := by
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_sigmaFinite
      F hF hdet g
  rw [specialFormPreservingSmoothRealChartSourceDensityMeasure]
  exact
    (specialFormPreservingSmoothRealChart F hF hdet g).toHomeomorphSourceTarget.symm
      |>.toMeasurableEquiv.sigmaFinite_map

/-- The exact common group overlap mapped into the native target coordinates
of its left chart. -/
def specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
        F hF hdet g h :=
  (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
    F hF hdet g h).toHomeomorph.trans
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
        F hF hdet g h).symm

/-- The exact common group overlap mapped into the native target coordinates
of its right chart. -/
def specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h ≃ₜ
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromRight
        F hF hdet g h :=
  (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
    F hF hdet g h).toHomeomorph.trans
      (specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
        F hF hdet g h).symm

/-- In native left-chart coordinates, the common-overlap measure is
exactly the chart target-density measure pulled back to its overlap image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft_native
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
          F hF hdet g h) =
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
        F hF hdet g h := by
  let e :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
      F hF hdet g h).toHomeomorph
  let u :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromLeftHomeomorph
      F hF hdet g h
  let μ :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromLeft
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromLeft
          F hF hdet g h)
  let ν :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
      F hF hdet g h
  change Measure.map (e.trans u.symm) (Measure.map e.symm μ) = ν
  rw [Measure.map_map (e.trans u.symm).continuous.measurable
    e.symm.continuous.measurable]
  have hfun : (e.trans u.symm : _ → _) ∘ e.symm = u.symm := by
    funext y
    simp
  rw [hfun]
  have hu : Measure.map u ν = μ :=
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft_eq_coordinateImageMeasure_withDensity
      F hF hdet g h
  calc
    Measure.map u.symm μ =
        Measure.map u.symm (Measure.map u ν) :=
      congrArg (Measure.map u.symm) hu.symm
    _ = ν :=
      MeasurableEquiv.map_symm_map u.toMeasurableEquiv

/-- In native right-chart coordinates, the common-overlap measure is
exactly the chart target-density measure pulled back to its overlap image. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight_native
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromRight
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromRight
          F hF hdet g h) =
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
        F hF hdet g h := by
  let e :=
    (isEmbedding_specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromRight
      F hF hdet g h).toHomeomorph
  let u :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateFromRightHomeomorph
      F hF hdet g h
  let μ :=
    (specialFormPreservingSmoothRealChartSourceOverlapCoordinateImageMeasureFromRight
      F hF hdet g h).withDensity
        (specialFormPreservingSmoothRealChartSourceOverlapCoordinateDensityFromRight
          F hF hdet g h)
  let ν :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight
      F hF hdet g h
  change Measure.map (e.trans u.symm) (Measure.map e.symm μ) = ν
  rw [Measure.map_map (e.trans u.symm).continuous.measurable
    e.symm.continuous.measurable]
  have hfun : (e.trans u.symm : _ → _) ∘ e.symm = u.symm := by
    funext y
    simp
  rw [hfun]
  have hu : Measure.map u ν = μ :=
    map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromRight_eq_coordinateImageMeasure_withDensity
      F hF hdet g h
  calc
    Measure.map u.symm μ =
        Measure.map u.symm (Measure.map u ν) :=
      congrArg (Measure.map u.symm) hu.symm
    _ = ν :=
      MeasurableEquiv.map_symm_map u.toMeasurableEquiv

/-- The `k`-th disjoint atlas piece, represented inside its assigned exact
chart source subtype. -/
def specialFormPreservingSmoothRealChartCoverPieceWithinSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    Set (specialFormPreservingSmoothRealChart F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).source :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealChartCoverPiece F hF hdet k

/-- The `k`-th atlas piece is measurable inside its assigned source subtype. -/
theorem measurableSet_specialFormPreservingSmoothRealChartCoverPieceWithinSource
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartCoverPieceWithinSource
        F hF hdet k) :=
  (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
    F hF hdet k).preimage continuous_subtype_val.measurable

/-- The measure contribution of the `k`-th disjoint chart piece, now on the
full real special-orthogonal group. -/
def specialFormPreservingSmoothRealChartCoverPieceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    Measure (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  Measure.map Subtype.val
    ((specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).restrict
      (specialFormPreservingSmoothRealChartCoverPieceWithinSource
        F hF hdet k))

/-- On measurable sets, a disjoint chart-piece contribution is the local
source-density measure of the corresponding source-internal intersection. -/
theorem specialFormPreservingSmoothRealChartCoverPieceMeasure_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ)
    {s : Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ)))} (hs : MeasurableSet s) :
    specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k s =
      specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
          (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)
        (specialFormPreservingSmoothRealChartCoverPieceWithinSource
            F hF hdet k ∩
          Subtype.val ⁻¹' s) := by
  let i :
      (specialFormPreservingSmoothRealChart F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).source →
        specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
    Subtype.val
  have hi : MeasurableEmbedding i :=
    MeasurableEmbedding.subtype_coe
      (isOpen_specialFormPreservingSmoothRealCenteredChartSource F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).measurableSet
  change (Measure.map i
    ((specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
      (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).restrict
      (specialFormPreservingSmoothRealChartCoverPieceWithinSource
        F hF hdet k))) s = _
  rw [hi.map_apply, Measure.restrict_apply
    (hs.preimage continuous_subtype_val.measurable)]
  rw [Set.inter_comm]

/-- A chart-piece contribution is concentrated on its assigned disjoint
piece. -/
theorem specialFormPreservingSmoothRealChartCoverPieceMeasure_compl
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k)ᶜ =
      0 := by
  rw [specialFormPreservingSmoothRealChartCoverPieceMeasure_apply F hF hdet k
    (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
      F hF hdet k).compl]
  have hset :
      specialFormPreservingSmoothRealChartCoverPieceWithinSource F hF hdet k ∩
        Subtype.val ⁻¹'
          (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k)ᶜ =
        ∅ := by
    ext x
    simp [specialFormPreservingSmoothRealChartCoverPieceWithinSource]
  rw [hset, measure_empty]

/-- Restricting a chart-piece contribution to its assigned disjoint piece
does not change it. -/
theorem restrict_specialFormPreservingSmoothRealChartCoverPieceMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    (specialFormPreservingSmoothRealChartCoverPieceMeasure
      F hF hdet k).restrict
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) =
      specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (specialFormPreservingSmoothRealChartCoverPieceMeasure_compl
      F hF hdet k)

set_option backward.isDefEq.respectTransparency false in
/-- Each disjoint chart-piece contribution is sigma-finite. -/
theorem specialFormPreservingSmoothRealChartCoverPieceMeasure_sigmaFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k : ℕ) :
    SigmaFinite
      (specialFormPreservingSmoothRealChartCoverPieceMeasure
        F hF hdet k) := by
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)) :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure_sigmaFinite
      F hF hdet _
  letI : SigmaFinite
      ((specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).restrict
        (specialFormPreservingSmoothRealChartCoverPieceWithinSource
          F hF hdet k)) :=
    inferInstance
  rw [specialFormPreservingSmoothRealChartCoverPieceMeasure]
  exact
    (MeasurableEmbedding.subtype_coe
      (isOpen_specialFormPreservingSmoothRealCenteredChartSource F hF hdet
        (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)).measurableSet).sigmaFinite_map

/-- A measurable finite-measure exhaustion piece for the `k`-th disjoint
chart contribution. -/
def specialFormPreservingSmoothRealChartCoverPieceFiniteSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k j : ℕ) :
    Set (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) :=
    specialFormPreservingSmoothRealChartCoverPieceMeasure_sigmaFinite
      F hF hdet k
  specialFormPreservingSmoothRealChartCoverPiece F hF hdet k ∩
    spanningSets
      (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) j

/-- Every chart exhaustion piece is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealChartCoverPieceFiniteSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k j : ℕ) :
    MeasurableSet
      (specialFormPreservingSmoothRealChartCoverPieceFiniteSet
        F hF hdet k j) := by
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) :=
    specialFormPreservingSmoothRealChartCoverPieceMeasure_sigmaFinite
      F hF hdet k
  exact
    (measurableSet_specialFormPreservingSmoothRealChartCoverPiece
      F hF hdet k).inter
        (measurableSet_spanningSets
          (specialFormPreservingSmoothRealChartCoverPieceMeasure
            F hF hdet k) j)

/-- A chart-piece contribution gives zero mass to every other disjoint atlas
piece. -/
theorem specialFormPreservingSmoothRealChartCoverPieceMeasure_other_piece
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    {i k : ℕ} (hik : i ≠ k) :
    specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet i
        (specialFormPreservingSmoothRealChartCoverPiece F hF hdet k) =
      0 := by
  apply measure_mono_null
    (t :=
      (specialFormPreservingSmoothRealChartCoverPiece F hF hdet i)ᶜ)
  · intro x hx hxi
    exact
      (Set.disjoint_left.mp
        (pairwiseDisjoint_specialFormPreservingSmoothRealChartCoverPiece
          F hF hdet hik) hxi hx)
  · exact specialFormPreservingSmoothRealChartCoverPieceMeasure_compl
      F hF hdet i

/-- The real differential measure obtained by summing the local
chart measures over the measurable disjoint countable atlas. -/
def specialFormPreservingSmoothRealDifferentialMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measure (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  Measure.sum
    (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet)

/-- Every two-index chart exhaustion set has finite mass for the glued
differential measure. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_finiteSet_lt_top
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (k j : ℕ) :
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
        (specialFormPreservingSmoothRealChartCoverPieceFiniteSet
          F hF hdet k j) <
      (∞ : ENNReal) := by
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) :=
    specialFormPreservingSmoothRealChartCoverPieceMeasure_sigmaFinite
      F hF hdet k
  rw [specialFormPreservingSmoothRealDifferentialMeasure,
    Measure.sum_apply _
      (measurableSet_specialFormPreservingSmoothRealChartCoverPieceFiniteSet
        F hF hdet k j),
    tsum_eq_single k]
  · exact
      (measure_mono Set.inter_subset_right).trans_lt
        (measure_spanningSets_lt_top
          (specialFormPreservingSmoothRealChartCoverPieceMeasure
            F hF hdet k) j)
  · intro i hik
    apply measure_mono_null
      (t := specialFormPreservingSmoothRealChartCoverPiece F hF hdet k)
    · exact Set.inter_subset_left
    · exact specialFormPreservingSmoothRealChartCoverPieceMeasure_other_piece
        F hF hdet hik

/-- The two-index finite-measure exhaustion sets cover the full real group. -/
theorem iUnion_specialFormPreservingSmoothRealChartCoverPieceFiniteSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (⋃ k, ⋃ j,
      specialFormPreservingSmoothRealChartCoverPieceFiniteSet
        F hF hdet k j) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hxcover :
      x ∈ ⋃ k, specialFormPreservingSmoothRealChartCoverPiece F hF hdet k := by
    rw [iUnion_specialFormPreservingSmoothRealChartCoverPiece F hF hdet]
    trivial
  rcases Set.mem_iUnion.mp hxcover with ⟨k, hxk⟩
  letI : SigmaFinite
      (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) :=
    specialFormPreservingSmoothRealChartCoverPieceMeasure_sigmaFinite
      F hF hdet k
  have hxspan :
      x ∈ ⋃ j, spanningSets
        (specialFormPreservingSmoothRealChartCoverPieceMeasure F hF hdet k) j := by
    rw [iUnion_spanningSets]
    trivial
  rcases Set.mem_iUnion.mp hxspan with ⟨j, hxj⟩
  exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨j, ⟨hxk, hxj⟩⟩⟩

/-- A single sequence enumerating the finite-measure exhaustion used for the
glued differential measure. -/
def specialFormPreservingSmoothRealDifferentialSpanningSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (m : ℕ) :
    Set (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :=
  specialFormPreservingSmoothRealChartCoverPieceFiniteSet F hF hdet
    m.unpair.1 m.unpair.2

/-- The enumerated exhaustion sets are measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealDifferentialSpanningSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (m : ℕ) :
    MeasurableSet
      (specialFormPreservingSmoothRealDifferentialSpanningSet
        F hF hdet m) :=
  measurableSet_specialFormPreservingSmoothRealChartCoverPieceFiniteSet
    F hF hdet m.unpair.1 m.unpair.2

/-- The enumerated exhaustion sets cover the full real group. -/
theorem iUnion_specialFormPreservingSmoothRealDifferentialSpanningSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (⋃ m, specialFormPreservingSmoothRealDifferentialSpanningSet
      F hF hdet m) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx :
      x ∈ ⋃ k, ⋃ j,
        specialFormPreservingSmoothRealChartCoverPieceFiniteSet
          F hF hdet k j := by
    rw [iUnion_specialFormPreservingSmoothRealChartCoverPieceFiniteSet
      F hF hdet]
    trivial
  rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
  refine Set.mem_iUnion.2 ⟨Nat.pair k j, ?_⟩
  simpa only [specialFormPreservingSmoothRealDifferentialSpanningSet,
    Nat.unpair_pair] using hx

/-- The glued real differential measure is sigma-finite. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    SigmaFinite
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  refine ⟨⟨⟨
    specialFormPreservingSmoothRealDifferentialSpanningSet F hF hdet,
    fun _ => Set.mem_univ _,
    ?_, iUnion_specialFormPreservingSmoothRealDifferentialSpanningSet
      F hF hdet⟩⟩⟩
  intro m
  exact specialFormPreservingSmoothRealDifferentialMeasure_finiteSet_lt_top
    F hF hdet m.unpair.1 m.unpair.2

/-- The glued measure is explicitly the countable sum of the local
source-density masses of the disjoint chart-piece intersections. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    {s : Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ)))} (hs : MeasurableSet s) :
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet s =
      ∑' k,
        specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet
            (specialFormPreservingSmoothRealChartCoverCenter F hF hdet k)
          (specialFormPreservingSmoothRealChartCoverPieceWithinSource
              F hF hdet k ∩
            Subtype.val ⁻¹' s) := by
  rw [specialFormPreservingSmoothRealDifferentialMeasure,
    Measure.sum_apply _ hs]
  congr 1
  funext k
  exact specialFormPreservingSmoothRealChartCoverPieceMeasure_apply
    F hF hdet k hs

/-- On a same-point overlap, the native left target coordinate is exactly the
left chart coordinate of the same group point. -/
theorem coe_specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)))
    (x : specialFormPreservingSmoothRealChartSourceOverlap F hF hdet g h) :
    ((specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
      F hF hdet g h x).1 :
        (specialFormPreservingSmoothRealChart F hF hdet g).target) =
      (specialFormPreservingSmoothRealChart F hF hdet g).toHomeomorphSourceTarget
        (specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h x) := by
  rfl

/-- The inverse image of the native left target overlap under the left chart
is the same-point overlap inside that chart source. -/
theorem preimage_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    (specialFormPreservingSmoothRealChart F hF hdet g).toHomeomorphSourceTarget ⁻¹'
        specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h =
      specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
        F hF hdet g h := by
  ext x
  constructor
  · intro hx
    change
      specialFormPreservingSmoothRealChartSourceTargetHomeomorph
        F hF hdet g x ∈
          Set.range
            (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
              F hF hdet g h) at hx
    rcases hx with ⟨z, hz⟩
    have hzx :
        specialFormPreservingSmoothRealChartSourceOverlapToLeft
            F hF hdet g h z = x :=
      (specialFormPreservingSmoothRealChartSourceTargetHomeomorph
        F hF hdet g).injective hz
    simpa [specialFormPreservingSmoothRealChartSourceOverlapWithinLeft, ← hzx]
      using z.2.2
  · intro hx
    change
      specialFormPreservingSmoothRealChartSourceTargetHomeomorph
        F hF hdet g x ∈
          Set.range
            (specialFormPreservingSmoothRealChartSourceOverlapCoordinateFromLeft
              F hF hdet g h)
    exact ⟨⟨x.1, x.2, hx⟩, rfl⟩

/-- The left overlap-density measure maps to the restriction of the
left chart-source differential measure to the exact same-point overlap. -/
theorem map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
          F hF hdet g h) =
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet g).restrict
        (specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
          F hF hdet g h) := by
  let e :=
    (specialFormPreservingSmoothRealChart
      F hF hdet g).toHomeomorphSourceTarget
  let u :=
    specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
      F hF hdet g h
  let i :=
    specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h
  let j :
      specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h →
        (specialFormPreservingSmoothRealChart F hF hdet g).target :=
    Subtype.val
  let μ :=
    specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
      F hF hdet g h
  let ν :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet g
  let ρ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet g
  let s :=
    specialFormPreservingSmoothRealChartSourceOverlapWithinLeft
      F hF hdet g h
  let t :=
    specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
      F hF hdet g h
  apply e.toMeasurableEquiv.measurableEmbedding.map_injective
  calc
    Measure.map e (Measure.map i μ) =
        Measure.map (e ∘ i) μ := by
      rw [Measure.map_map e.continuous.measurable
        (measurable_specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)]
    _ = Measure.map (j ∘ u) μ := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact
        (coe_specialFormPreservingSmoothRealChartSourceOverlapNativeTargetHomeomorphFromLeft
          F hF hdet g h x).symm
    _ = Measure.map j (Measure.map u μ) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        u.continuous.measurable]
    _ = Measure.map j
          (specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
            F hF hdet g h) := by
      rw [
        map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft_native]
    _ = ρ.restrict t :=
      map_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageDensityMeasureFromLeft
        F hF hdet g h
    _ = Measure.map e (ν.restrict s) := by
      have hr := Measure.restrict_map e.continuous.measurable
        (measurableSet_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h)
        (μ := ν)
      rw [map_specialFormPreservingSmoothRealChartSourceDensityMeasure
        F hF hdet g] at hr
      rw [
        preimage_specialFormPreservingSmoothRealChartTargetOverlapCoordinateImageFromLeft
          F hF hdet g h] at hr
      simpa [ρ, t, ν, s] using hr

/-- Equivalently, pulling the left chart-source differential measure back
along the same-point inclusion recovers the overlap measure. -/
theorem comap_specialFormPreservingSmoothRealChartSourceDensityMeasure_left
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g h : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ))) :
    Measure.comap
        (specialFormPreservingSmoothRealChartSourceOverlapToLeft
          F hF hdet g h)
        (specialFormPreservingSmoothRealChartSourceDensityMeasure
          F hF hdet g) =
      specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft
        F hF hdet g h := by
  let i :=
    specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h
  apply
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h).map_injective
  rw [
    (measurableEmbedding_specialFormPreservingSmoothRealChartSourceOverlapToLeft
      F hF hdet g h).map_comap,
    range_specialFormPreservingSmoothRealChartSourceOverlapToLeft F hF hdet g h,
    map_specialFormPreservingSmoothRealChartSourceOverlapDensityMeasureFromLeft_source]

end PositiveDefiniteIntegralLattice
