import SMSFormula.PadicCayleyTranslatedChartJacobian
import SMSFormula.PadicCayleyTranslatedChartOverlapJacobian

/-!
# Measure restrictions on translated p-adic Cayley chart overlaps

This module restricts the weighted and coordinate measures to the exact
source-coordinate and common-target overlap subtypes.  Each translated Cayley
chart transports its source restriction to the corresponding restriction on
the common target.

The pointwise transition square reduces equality of the two common-target
restrictions to a pushforward identity for the nonlinear source-coordinate
transition.  That pushforward identity is not asserted here: Mathlib
does not supply the required nonarchimedean nonlinear change-of-variables
theorem.  No full-group measure, invariance theorem, or chart gluing is
introduced.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapMeasureSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapMeasureSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyOverlapMeasureMatrixCarrierMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (Matrix.specialOrthogonalMatrixSet
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyOverlapMeasureMatrixCarrierBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (Matrix.specialOrthogonalMatrixSet
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

local instance padicCayleyOverlapMeasureSubgroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyOverlapMeasureSubgroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Include the common target overlap into the target centered at `c`. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d →
      padicCayleySpecialOrthogonalTranslatedTarget F p c :=
  fun g => ⟨g.1, g.2.1⟩

/-- Include the common target overlap into the target centered at `d`. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d →
      padicCayleySpecialOrthogonalTranslatedTarget F p d :=
  fun g => ⟨g.1, g.2.2⟩

/-- The common target overlap viewed inside the target centered at `c`. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (padicCayleySpecialOrthogonalTranslatedTarget F p c) :=
  Subtype.val ⁻¹' padicCayleySpecialOrthogonalTranslatedTarget F p d

/-- The common target overlap viewed inside the target centered at `d`. -/
def padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (padicCayleySpecialOrthogonalTranslatedTarget F p d) :=
  Subtype.val ⁻¹' padicCayleySpecialOrthogonalTranslatedTarget F p c

theorem isOpen_padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
        p n F c d) :=
  (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p d).preimage
    continuous_subtype_val

theorem isOpen_padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsOpen
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
        p n F c d) :=
  (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p c).preimage
    continuous_subtype_val

private def padicCayleySpecialOrthogonalTranslatedTargetOverlapLeftHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
        p n F c d where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, ⟨g.1.2, g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def padicCayleySpecialOrthogonalTranslatedTargetOverlapRightHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
        p n F c d where
  toFun g := ⟨⟨g.1, g.2.2⟩, g.2.1⟩
  invFun g := ⟨g.1.1, ⟨g.2, g.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem
    measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    MeasurableEmbedding
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
        p n F c d) := by
  let e :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapLeftHomeomorph
      p n F c d
  have he : MeasurableEmbedding e :=
    e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val :
        padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
            p n F c d →
          padicCayleySpecialOrthogonalTranslatedTarget F p c) :=
    MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
        p n F c d).measurableSet
  simpa [e, Function.comp_def,
    padicCayleySpecialOrthogonalTranslatedTargetOverlapLeftHomeomorph,
    padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft] using
      hi.comp he

theorem
    measurableEmbedding_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    MeasurableEmbedding
      (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
        p n F c d) := by
  let e :=
    padicCayleySpecialOrthogonalTranslatedTargetOverlapRightHomeomorph
      p n F c d
  have he : MeasurableEmbedding e :=
    e.toMeasurableEquiv.measurableEmbedding
  have hi : MeasurableEmbedding
      (Subtype.val :
        padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
            p n F c d →
          padicCayleySpecialOrthogonalTranslatedTarget F p d) :=
    MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
        p n F c d).measurableSet
  simpa [e, Function.comp_def,
    padicCayleySpecialOrthogonalTranslatedTargetOverlapRightHomeomorph,
    padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight] using
      hi.comp he

/-- The coordinate source measure restricted to the exact `c`-coordinate
overlap with the chart at `d`. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure (skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :=
  Measure.comap Subtype.val
    (Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F)

theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure_subtype
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map Subtype.val
        (skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure
          p n F hF c d) =
      (Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
        p n F).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapSet
          F p hF c d) := by
  rw [skewAdjointPadicCayleyTranslatedSourceOverlapCoordinateMeasure]
  exact map_comap_subtype_coe
    (isOpen_skewAdjointPadicCayleyTranslatedSourceOverlapSet
      F p hF c d).measurableSet _

theorem
    range_padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set.range
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapToLeft
          p n F c d) =
      padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinLeft
        p n F c d := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2.2
  · intro hg
    exact ⟨⟨g.1, ⟨g.2, hg⟩⟩, rfl⟩

theorem
    range_padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
    (F : Matrix (Fin n) (Fin n) ℚ)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set.range
        (padicCayleySpecialOrthogonalTranslatedTargetOverlapToRight
          p n F c d) =
      padicCayleySpecialOrthogonalTranslatedTargetOverlapWithinRight
        p n F c d := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2.1
  · intro hg
    exact ⟨⟨g.1, ⟨hg, g.2⟩⟩, rfl⟩

/-- The right source-overlap chart with its target reordered to the common
`(c,d)` target subtype. -/
def skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c ≃ₜ
      padicCayleySpecialOrthogonalTranslatedTargetOverlap F p c d :=
  (skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
      F p hF d c).trans
    (padicCayleySpecialOrthogonalTranslatedTargetOverlapSwapHomeomorph
      F p c d).symm

/-- Pointwise, the right chart after the source-coordinate transition is the
left chart on the common target subtype. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph_transition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X) =
      skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
        F p hF c d X := by
  apply Subtype.ext
  exact
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_target
      F p hF c d X

end PositiveDefiniteIntegralLattice
