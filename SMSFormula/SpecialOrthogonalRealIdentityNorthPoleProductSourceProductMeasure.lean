import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductHigherTargetDifferential
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeRadialSector
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapChartRestriction

/-!
# Source product measure for the identity north-pole transition

This module exposes the source-coordinate Haar as the product of the
rationally normalized lower mapped tangent Haar and standard Euclidean
volume, then combines the lower-chart and north-pole densities on the
exact product-transition source.

The lower chart factor is not returned to the group differential measure
here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductSourceProductMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductSourceProductBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductSourceProductLiteralTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalTangent n) :=
  borel _

local instance identityNorthPoleProductSourceProductLiteralTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalTangent n) :=
  ⟨rfl⟩

/-- Transporting the fixed literal lower tangent Haar back through the
identity-on-ambient mapped tangent equivalence recovers the rational
skew-adjoint coordinate determinant measure. -/
theorem
    map_identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv_symm_coordinateMeasure
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
          n).symm
        (identitySpecialOrthogonalTangentCoordinateMeasure n) =
      Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ) 0 := by
  rw [identitySpecialOrthogonalTangentCoordinateMeasure,
    identitySpecialOrthogonalFixedTangentBasis]
  have hmap := @Module.Basis.map_addHaar _
    (identitySpecialOrthogonalTangent n)
    (identitySpecialOrthogonalMappedTangent n) _ _ _ _ _
    (identitySpecialOrthogonalTangentMeasurableSpace n)
    (Matrix.skewAdjointRealMeasurableSpace
      (1 : Matrix (Fin n) (Fin n) ℚ))
    (identitySpecialOrthogonalTangentBorelSpace n)
    (Matrix.skewAdjointRealBorelSpace
      (1 : Matrix (Fin n) (Fin n) ℚ)) _ _
    ((skewAdjointScalarExtensionFinBasis (K := ℝ)
      (1 : Matrix (Fin n) (Fin n) ℚ)).map
      (identitySpecialOrthogonalMappedIdentityTangentEquiv n))
    (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n).symm
  erw [hmap,
    Matrix.skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    Matrix.skewAdjointRealBasisHaarMeasure]
  apply congrArg (@Module.Basis.addHaar _
    (identitySpecialOrthogonalMappedTangent n) _ _ _
    (Matrix.skewAdjointRealMeasurableSpace
      (1 : Matrix (Fin n) (Fin n) ℚ))
    (Matrix.skewAdjointRealBorelSpace
      (1 : Matrix (Fin n) (Fin n) ℚ)))
  apply DFunLike.ext
  intro i
  change
    (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
      ).symm
        (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
          ((skewAdjointScalarExtensionFinBasis (K := ℝ)
            (1 : Matrix (Fin n) (Fin n) ℚ)) i)) =
      (skewAdjointScalarExtensionFinBasis (K := ℝ)
        (1 : Matrix (Fin n) (Fin n) ℚ)) i
  exact
    (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
      ).symm_apply_apply _

/-- The standard coordinate-basis Haar on `Fin n → ℝ` becomes Euclidean
volume under the canonical `PiLp` equivalence. -/
theorem map_PiLp_symm_basisFun_addHaar_eq_volume
    (n : ℕ) :
    Measure.map
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
        (Pi.basisFun ℝ (Fin n)).addHaar =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hPi :
      (Pi.basisFun ℝ (Fin n)).addHaar =
        (volume : Measure (Fin n → ℝ)) := by
    rw [← addHaarMeasure_eq_volume_pi,
      ← Module.Basis.parallelepiped_basisFun,
      ← Module.Basis.addHaar_def]
  rw [hPi]
  exact (PiLp.volume_preserving_toLp (ι := Fin n)).map_eq

/-- The source-coordinate Haar used by the product transition is exactly the
product of the rational lower mapped tangent measure and Euclidean volume. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure_eq_prod
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
        n =
      (Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ) 0).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  letI :
      SFinite (identitySpecialOrthogonalTangentCoordinateMeasure n) := by
    rw [identitySpecialOrthogonalTangentCoordinateMeasure]
    infer_instance
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure,
    identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis]
  have hmap := @Module.Basis.map_addHaar _
    (identitySpecialOrthogonalTangent n × (Fin n → ℝ))
    (identitySpecialOrthogonalMappedTangent n × EuclideanSpace ℝ (Fin n))
    _ _ _ _ _ _ _
    (identitySpecialOrthogonalTangentProductBorelSpace n)
    (identityNorthPoleTransitionProductBorelSpace n) _ _
    (identitySpecialOrthogonalTangentProductBasis n)
    (identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv n).symm
  erw [← hmap]
  change
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv
          n).symm
        (identitySpecialOrthogonalTangentProductCoordinateMeasure n) = _
  rw [identitySpecialOrthogonalTangentProductCoordinateMeasure_eq_prod]
  change
    Measure.map
        (Prod.map
          (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv
            n).symm
          (PiLp.continuousLinearEquiv 2 ℝ
            (fun _ : Fin n => ℝ)).symm)
        ((identitySpecialOrthogonalTangentCoordinateMeasure n).prod
          (Pi.basisFun ℝ (Fin n)).addHaar) = _
  rw [← Measure.map_prod_map _ _
      (identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv n
        ).symm.continuous.measurable
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin n => ℝ)).symm.continuous.measurable,
    map_identitySpecialOrthogonalMappedIdentityTangentContinuousLinearEquiv_symm_coordinateMeasure,
    map_PiLp_symm_basisFun_addHaar_eq_volume]

/-- Returning the north-pole coordinate sphere measure to the ambient
Euclidean carrier gives ball-restricted volume weighted by the proved
inverse-square-root density. -/
theorem map_identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_subtype
    (n : ℕ) :
    Measure.map Subtype.val
        (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
          (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)) := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_eq_densityMeasure,
    identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure,
    map_comap_subtype_coe Metric.isOpen_ball.measurableSet,
    restrict_withDensity Metric.isOpen_ball.measurableSet]

/-- On the exact product-transition source, the ambient source density is the
product of the lower identity-chart ambient density and the north-pole
coordinate density. -/
theorem
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity_eq_product
    (n : ℕ)
    (x : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n x =
      specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero x.1 *
        identitySpecialOrthogonalNorthPoleCoordinateDensity x.2 := by
  have hdomain :
      x ∈ identitySpecialOrthogonalNorthPoleProductDomainSet n :=
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset n hx
  rw [
    identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity_eq n x hx,
    identitySpecialOrthogonalNorthPoleProductSourceDensity,
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity_eq
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero x.1 hdomain.1]
  rfl

/-- The lower identity-chart target-density measure times the positive
hemisphere sphere measure in north-pole coordinates. -/
def identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure
    (n : ℕ) :
    Measure
      ((specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero).target ×
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (specialFormPreservingSmoothRealChartTargetDensityMeasure
    (1 : Matrix (Fin n) (Fin n) ℚ)
    identityRationalForm_isSymm
    identityRationalForm_det_ne_zero 1).prod
      (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n)

/-- Forgetting both subtype proofs returns the lower-chart/sphere product to
the ambient product coordinate carrier. -/
def identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
    (n : ℕ) :
    ((specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).target ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
        identitySpecialOrthogonalMappedTangent n ×
          EuclideanSpace ℝ (Fin n) :=
  fun p => (p.1.1, p.2.1)

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient n) :=
  continuous_subtype_val.measurable.prodMap
    continuous_subtype_val.measurable

/-- The ambient image of the lower-chart/sphere subtype product is the
product of the two independently weighted ambient restrictions. -/
theorem
    map_identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient n)
        (identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure
          n) =
      (((Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ) 0).restrict
          (identitySpecialOrthogonalLowerChartTargetSet n)).withDensity
            (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
              (1 : Matrix (Fin n) (Fin n) ℚ)
              identityRationalForm_isSymm
              identityRationalForm_det_ne_zero)).prod
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
            (identitySpecialOrthogonalNorthPoleCoordinateDensity
              (n := n))) := by
  letI :
      SigmaFinite
        (specialFormPreservingSmoothRealChartTargetDensityMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero 1) :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure_sigmaFinite
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero 1
  letI :
      IsFiniteMeasure
        (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n) :=
    ⟨identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top n⟩
  rw [
    identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure]
  change
    Measure.map (Prod.map Subtype.val Subtype.val)
      ((specialFormPreservingSmoothRealChartTargetDensityMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero 1).prod
          (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n)) = _
  rw [← Measure.map_prod_map _ _
      continuous_subtype_val.measurable
      continuous_subtype_val.measurable,
    map_specialFormPreservingSmoothRealCongruenceSourceIdentityDensityMeasure_ambient,
    map_identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_subtype]
  rfl

/-- On the exact higher-chart source, the source-density-weighted coordinate
measure is the restriction of the product of the lower chart-density measure
and the north-pole coordinate sphere-density measure. -/
theorem
    identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_restrict_prod
    (n : ℕ) :
    (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
        ).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      ((((Matrix.skewAdjointRealCoordinateDetMeasure
        (1 : Matrix (Fin n) (Fin n) ℚ) 0).restrict
          (identitySpecialOrthogonalLowerChartTargetSet n)).withDensity
            (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
              (1 : Matrix (Fin n) (Fin n) ℚ)
              identityRationalForm_isSymm
              identityRationalForm_det_ne_zero)).prod
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
            (identitySpecialOrthogonalNorthPoleCoordinateDensity
              (n := n)))).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  let μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure
      (1 : Matrix (Fin n) (Fin n) ℚ) 0
  let ν := (volume : Measure (EuclideanSpace ℝ (Fin n)))
  let A := identitySpecialOrthogonalLowerChartTargetSet n
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
  let S := identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n
  let f :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero
  let g :=
    identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)
  let fg := fun x :
      identitySpecialOrthogonalMappedTangent n ×
        EuclideanSpace ℝ (Fin n) =>
    f x.1 * g x.2
  letI : SigmaFinite μ :=
    Matrix.skewAdjointRealCoordinateDetMeasure_sigmaFinite
      (1 : Matrix (Fin n) (Fin n) ℚ) 0
  have hS : MeasurableSet S :=
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_isOpen n
      ).measurableSet
  have hsub : S ⊆ A ×ˢ B := by
    exact identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset n
  have hdensity :
      identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n =ᵐ[
        (μ.prod ν).restrict S] fg := by
    filter_upwards [MeasureTheory.ae_restrict_mem hS] with x hx
    exact
      identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity_eq_product
        n x hx
  have hprod :
      ((μ.restrict A).withDensity f).prod
          ((ν.restrict B).withDensity g) =
        ((μ.prod ν).restrict (A ×ˢ B)).withDensity fg := by
    rw [← Measure.prod_restrict]
    exact MeasureTheory.prod_withDensity
      (μ := μ.restrict A)
      (ν := ν.restrict B)
      (f := f)
      (g := g)
      (measurable_specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
        (1 : Matrix (Fin n) (Fin n) ℚ)
        identityRationalForm_isSymm
        identityRationalForm_det_ne_zero)
      (measurable_identitySpecialOrthogonalNorthPoleCoordinateDensity n)
  change
    (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict S).withDensity
        (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      (((μ.restrict A).withDensity f).prod
        ((ν.restrict B).withDensity g)).restrict S
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure_eq_prod,
    withDensity_congr_ae hdensity,
    hprod,
    restrict_withDensity hS,
    Measure.restrict_restrict_of_subset hsub]

/-- Equivalently, the weighted source restriction is the restricted ambient
image of the intrinsic lower-chart/sphere subtype product measure. -/
theorem
    identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_restrict_map_subtype
    (n : ℕ) :
    (((identitySpecialOrthogonalNorthPoleProductTransitionSourceCoordinateMeasure
      n).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n)
        ).withDensity
          (identitySpecialOrthogonalNorthPoleProductAmbientSourceDensity n)) =
      (Measure.map
        (identitySpecialOrthogonalNorthPoleProductSourceSubtypeToAmbient n)
        (identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure
          n)).restrict
        (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) := by
  rw [
    map_identitySpecialOrthogonalNorthPoleProductSourceSubtypeProductMeasure,
    ←
      identitySpecialOrthogonalNorthPoleProductSourceWithDensity_eq_restrict_prod]

end PositiveDefiniteIntegralLattice
