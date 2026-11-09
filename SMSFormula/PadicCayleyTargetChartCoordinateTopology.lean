import SMSFormula.PadicCayleyTargetChartJacobianFormula

/-!
# Topology of the unweighted p-adic Cayley coordinate measures

The normalized additive coordinate measure on the exact Cayley source
subtype is locally finite, finite on compact sets, regular, full-support, and
nonzero. The Cayley homeomorphism transports these properties,
together with positivity on nonempty open sets, to the unweighted coordinate
measure on the exact special-orthogonal inverse-domain subtype.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTargetCoordinateTopologySourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTargetCoordinateTopologySourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTargetCoordinateTopologyGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetCoordinateTopologyGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The unweighted coordinate measure on the exact Cayley source subtype is
locally finite. -/
theorem
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyFiniteMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) := by
  let μ := skewAdjointPadicCoordinateMeasure F p
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  letI : ProperSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    FiniteDimensional.proper ℚ_[p] _
  rw [skewAdjointPadicCayleySourceCoordinateSubtypeMeasure]
  refine ⟨fun X ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top X.1 with ⟨U, hXU, hU, hμU⟩
  refine ⟨Subtype.val ⁻¹' U,
    (hU.preimage continuous_subtype_val).mem_nhds hXU, ?_⟩
  rw [comap_subtype_coe_apply
    (isOpen_skewAdjointPadicCayleySource F p).measurableSet]
  apply (measure_mono ?_).trans_lt hμU
  rintro _ ⟨Y, hYU, rfl⟩
  exact hYU

/-- The unweighted coordinate measure on the exact Cayley source subtype is
finite on compact sets. -/
theorem
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsFiniteMeasureOnCompacts
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) := by
  letI : IsLocallyFiniteMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isLocallyFinite
      p n F
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The unweighted coordinate measure on the exact Cayley source subtype is
regular. -/
theorem skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_regular
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure.Regular
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) := by
  letI : ProperSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    FiniteDimensional.proper ℚ_[p] _
  letI : LocallyCompactSpace (skewAdjointPadicCayleySource F p) :=
    (isOpen_skewAdjointPadicCayleySource F p).locallyCompactSpace
  letI : IsLocallyFiniteMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isLocallyFinite
      p n F
  infer_instance

/-- The unweighted coordinate measure on the exact Cayley source subtype has
full support. -/
theorem skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_support
    (F : Matrix (Fin n) (Fin n) ℚ) :
    (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F).support =
      Set.univ := by
  letI : Measure.IsOpenPosMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isOpenPosMeasure
      p n F
  exact Measure.support_eq_univ

/-- The unweighted coordinate measure on the exact Cayley source subtype has
strictly positive total mass. -/
theorem skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_univ_pos
    (F : Matrix (Fin n) (Fin n) ℚ) :
    0 <
      skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
        p n F Set.univ := by
  letI : Measure.IsOpenPosMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isOpenPosMeasure
      p n F
  letI : Nonempty (skewAdjointPadicCayleySource F p) :=
    ⟨⟨0, zero_mem_skewAdjointPadicCayleySource F p⟩⟩
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

/-- The unweighted coordinate measure on the exact Cayley source subtype is
nonzero. -/
theorem skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) :
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F ≠ 0 := by
  intro hzero
  have hpos :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_univ_pos p n F
  rw [hzero] at hpos
  simp at hpos

/-- The unweighted coordinate measure on the exact Cayley target subtype is
locally finite. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    IsLocallyFiniteMeasure
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) := by
  let e := skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  letI : IsLocallyFiniteMeasure μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isLocallyFinite
      p n F
  rw [padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure]
  refine ⟨fun g ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (e.symm g) with
    ⟨U, hgU, hU, hμU⟩
  refine ⟨e.symm ⁻¹' U,
    (hU.preimage e.symm.continuous).mem_nhds hgU, ?_⟩
  rw [Measure.map_apply e.measurable
    (hU.preimage e.symm.continuous).measurableSet]
  have hpreimage : e ⁻¹' (e.symm ⁻¹' U) = U := by
    ext X
    simp
  rw [hpreimage]
  exact hμU

/-- The unweighted coordinate measure on the exact Cayley target subtype is
finite on compact sets. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_isFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    IsFiniteMeasureOnCompacts
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) := by
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  letI : IsFiniteMeasureOnCompacts μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isFiniteOnCompacts
      p n F
  rw [padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure]
  exact Measure.IsFiniteMeasureOnCompacts.map μ
    (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF)

/-- The unweighted coordinate measure on the exact Cayley target subtype is
regular. -/
theorem padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_regular
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measure.Regular
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) := by
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  letI : Measure.Regular μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_regular p n F
  rw [padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure]
  exact Measure.Regular.map
    (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF)

/-- The unweighted coordinate measure on the exact Cayley target subtype is
positive on every nonempty open set. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) := by
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  letI : Measure.IsOpenPosMeasure μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isOpenPosMeasure
      p n F
  rw [padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure]
  exact
    (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
      F p hF).continuous.isOpenPosMeasure_map
        (skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF).surjective

/-- The unweighted coordinate measure on the exact Cayley target subtype has
full support. -/
theorem padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_support
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
      p n F hF).support = Set.univ := by
  letI : Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) :=
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_isOpenPosMeasure
      p n F hF
  exact Measure.support_eq_univ

/-- The unweighted coordinate measure on the exact Cayley target subtype has
strictly positive total mass. -/
theorem
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_univ_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    0 <
      padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF Set.univ := by
  letI : Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
        p n F hF) :=
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_isOpenPosMeasure
      p n F hF
  letI : Nonempty (padicCayleySpecialOrthogonalInverseDomain F p) :=
    ⟨⟨specialOrthogonalMatrixIdentity
      (F.map (algebraMap ℚ ℚ_[p])),
      specialOrthogonalMatrixIdentity_mem_padicCayleyInverseDomain F p⟩⟩
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

/-- The unweighted coordinate measure on the exact Cayley target subtype is
nonzero. -/
theorem padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure
      p n F hF ≠ 0 := by
  intro hzero
  have hpos :=
    padicCayleySpecialOrthogonalInverseDomainCoordinateMeasure_univ_pos
      p n F hF
  rw [hzero] at hpos
  simp at hpos

end Matrix
