import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleHemisphereRankIteration

/-!
# The base rank of the elementary-normalized identity differential mass

This file evaluates the rank-zero base of the elementary-normalized real
identity differential mass.  The rank-one rational skew-adjoint tangent is
zero-dimensional, its coordinate parallelepiped is the whole tangent space,
and the real special orthogonal group `SO(1)` is the identity singleton.

The differential mass calculation uses the rational coordinate determinant
measure and the glued identity chart.  No Haar uniqueness or rescaling is
used.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

local instance identityBaseRankTangentMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin 1) (Fin 1) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance identityBaseRankTangentBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin 1) (Fin 1) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance identityBaseRankMappedGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  borel _

local instance identityBaseRankMappedGroupBorelSpace (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map
          (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance identityBaseRankGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityBaseRankGroupBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

private theorem identityBaseRankRationalTangent_finrank :
    Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra
        (1 : Matrix (Fin 1) (Fin 1) ℚ)) = 0 := by
  rw [finrank_skewAdjointMatricesLieSubalgebra_eq_choose_two
    1 (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp)]
  norm_num

private theorem identityBaseRankRealTangent_finrank :
    Module.finrank ℝ
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin 1) (Fin 1) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule = 0 := by
  rw [Matrix.finrank_skewAdjointScalarExtension_real]
  exact identityBaseRankRationalTangent_finrank

local instance identityBaseRankRationalTangentIndexIsEmpty :
    IsEmpty
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (1 : Matrix (Fin 1) (Fin 1) ℚ)))) := by
  constructor
  intro i
  have hi := i.isLt
  have hrank := identityBaseRankRationalTangent_finrank
  omega

local instance identityBaseRankRealTangentSubsingleton :
    Subsingleton
      (skewAdjointMatricesLieSubalgebra
        ((1 : Matrix (Fin 1) (Fin 1) ℚ).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  Module.finrank_zero_iff.mp identityBaseRankRealTangent_finrank

/-- The fixed-to-elementary determinant in matrix rank one is the determinant
of the unique endomorphism of a zero-dimensional rational tangent space. -/
theorem identitySpecialOrthogonalFixedElementaryDetScalar_one :
    identitySpecialOrthogonalFixedElementaryDetScalar 1 = 1 := by
  rw [identitySpecialOrthogonalFixedElementaryDetScalar]
  rw [Module.Basis.det_apply]
  exact Matrix.det_isEmpty

/-- The literal real special orthogonal group `SO(1)` has only its identity
element. -/
theorem identitySpecialOrthogonalGroup_zero_eq_one
    (g : identitySpecialOrthogonalGroup 0) :
    g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  have hdet :
      g.1.1.1.det = 1 :=
    (mem_specialFormPreservingMatrixSubgroup_iff
      (1 : Matrix (Fin 1) (Fin 1) ℝ) g.1).mp g.2
  simpa [Matrix.det_fin_one] using hdet

/-- The rationally normalized coordinate determinant measure has total mass
one in the zero-dimensional rank-one skew-adjoint tangent. -/
theorem identitySpecialOrthogonalRankOneCoordinateDetMeasure_univ :
    Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 Set.univ = 1 := by
  have hparallelepiped :
      parallelepiped
          (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ)
            (1 : Matrix (Fin 1) (Fin 1) ℚ)) =
        Set.univ := by
    rw [parallelepiped_basis_eq]
    ext x
    simp
  rw [← hparallelepiped]
  exact Matrix.skewAdjointRealCoordinateDetMeasure_parallelepiped
    (1 : Matrix (Fin 1) (Fin 1) ℚ) 0

/-- Every rank-one centered chart has constant coordinate density one. -/
private theorem identityBaseRankChartCoordinateDensity_eq_one
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ)))
    (y : (specialFormPreservingSmoothRealChart
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g).target) :
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g y = 1 := by
  rw [
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal,
    specialFormPreservingSmoothRealChartCoordinateDensity_eq_diagonalPartialJacobian,
    specialFormPreservingSmoothRealDiagonalPartialJacobian]
  simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_subsingleton]

/-- A rank-one chart target has differential volume one. -/
private theorem identityBaseRankChartTargetDensityMeasure_univ
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartTargetDensityMeasure
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g Set.univ = 1 := by
  have hdensity :
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g = 1 := by
    funext y
    exact identityBaseRankChartCoordinateDensity_eq_one g y
  have htarget :
      ((specialFormPreservingSmoothRealChart
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g).target :
          Set (skewAdjointMatricesLieSubalgebra
            ((1 : Matrix (Fin 1) (Fin 1) ℚ).map
              (algebraMap ℚ ℝ))).toSubmodule) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim y 0]
    have hsource :=
      self_mem_specialFormPreservingSmoothRealChart_source
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g
    simpa using
      (specialFormPreservingSmoothRealChart
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g).map_source
          hsource
  have himage :
      Subtype.val ''
          (Set.univ : Set
            (specialFormPreservingSmoothRealChart
              (1 : Matrix (Fin 1) (Fin 1) ℚ)
                (by simp) (by simp) g).target) =
        (specialFormPreservingSmoothRealChart
          (1 : Matrix (Fin 1) (Fin 1) ℚ)
            (by simp) (by simp) g).target := by
    ext y
    simp
  rw [specialFormPreservingSmoothRealChartTargetDensityMeasure, hdensity,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Pi.one_apply, Measure.restrict_univ, lintegral_one]
  rw [
    comap_subtype_coe_apply
      (specialFormPreservingSmoothRealChart
        (1 : Matrix (Fin 1) (Fin 1) ℚ)
          (by simp) (by simp) g).open_target.measurableSet,
    himage, htarget]
  exact identitySpecialOrthogonalRankOneCoordinateDetMeasure_univ

/-- A rank-one chart source has differential volume one. -/
private theorem identityBaseRankChartSourceDensityMeasure_univ
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartSourceDensityMeasure
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g Set.univ = 1 := by
  have hmap :=
    map_specialFormPreservingSmoothRealChartSourceDensityMeasure
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g
  have hmass := congrArg (fun μ => μ Set.univ) hmap
  change
    (Measure.map
      (specialFormPreservingSmoothRealChart
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g
          ).toHomeomorphSourceTarget
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g)) Set.univ =
      specialFormPreservingSmoothRealChartTargetDensityMeasure
        (1 : Matrix (Fin 1) (Fin 1) ℚ)
          (by simp) (by simp) g Set.univ at hmass
  rw [Measure.map_apply
    (specialFormPreservingSmoothRealChart
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g
        ).toHomeomorphSourceTarget.continuous.measurable
    MeasurableSet.univ] at hmass
  simpa using hmass.trans
    (identityBaseRankChartTargetDensityMeasure_univ g)

/-- Returning the rank-one chart source to the mapped group preserves its
unit differential volume. -/
private theorem identityBaseRankChartAmbientDensityMeasure_univ
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))) :
    specialFormPreservingSmoothRealChartAmbientDensityMeasure
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) g Set.univ = 1 := by
  rw [specialFormPreservingSmoothRealChartAmbientDensityMeasure,
    Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simpa only [preimage_univ] using
    identityBaseRankChartSourceDensityMeasure_univ g

private theorem identityBaseRankMappedGroup_eq_one
    (g : specialFormPreservingMatrixSubgroup
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))) :
    g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  have hdet :
      g.1.1.1.det = 1 :=
    (mem_specialFormPreservingMatrixSubgroup_iff
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ)) g.1).mp g.2
  simpa [Matrix.det_fin_one] using hdet

private theorem identityBaseRankIdentityChart_source_eq_univ :
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp)).source =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  rw [identityBaseRankMappedGroup_eq_one g]
  exact self_mem_specialFormPreservingSmoothRealChart_source
    (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) 1

/-- The rational differential construction gives unit total mass to the
scalar-extended rank-one identity group. -/
theorem identitySpecialOrthogonalMappedDifferentialMeasure_zero_univ :
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) Set.univ = 1 := by
  have hrestrict :=
    restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (by simp) (by simp) 1
  rw [identityBaseRankIdentityChart_source_eq_univ,
    Measure.restrict_univ] at hrestrict
  have hmass := congrArg (fun μ => μ Set.univ) hrestrict
  exact hmass.trans (identityBaseRankChartAmbientDensityMeasure_univ 1)

/-- Canonical literal differential Haar on `SO(1)` has total mass one. -/
theorem identitySpecialOrthogonalDifferentialMeasure_zero_univ :
    identitySpecialOrthogonalDifferentialMeasure 0 Set.univ = 1 := by
  have hf : Measurable
      (identitySpecialOrthogonalMappedGroupContinuousEquiv 0 :
        specialFormPreservingMatrixSubgroup
            ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ)) →
          identitySpecialOrthogonalGroup 0) :=
    (identitySpecialOrthogonalMappedGroupContinuousEquiv 0).continuous.measurable
  rw [identitySpecialOrthogonalDifferentialMeasure,
    Measure.map_apply hf MeasurableSet.univ]
  simpa only [preimage_univ] using
    identitySpecialOrthogonalMappedDifferentialMeasure_zero_univ

/-- The elementary-normalized identity differential mass starts at one. -/
theorem identitySpecialOrthogonalElementaryNormalizedDifferentialMass_zero :
    identitySpecialOrthogonalElementaryNormalizedDifferentialMass 0 = 1 := by
  rw [identitySpecialOrthogonalElementaryNormalizedDifferentialMass]
  simp only [zero_add]
  rw [identitySpecialOrthogonalFixedElementaryDetScalar_one]
  simp only [Rat.cast_one, abs_one, Real.toNNReal_one, ENNReal.coe_one, inv_one,
    one_mul]
  exact identitySpecialOrthogonalDifferentialMeasure_zero_univ

end PositiveDefiniteIntegralLattice
