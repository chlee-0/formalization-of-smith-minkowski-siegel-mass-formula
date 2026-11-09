import SMSFormula.SpecialOrthogonalRealCongruenceChartJacobian
import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductTransitionChangeOfVariables

/-!
# Pointwise normalization of the identity north-pole product Jacobian

This file records the lower-chart/sphere and higher-chart differential
densities on the exact source and target of the north-pole product transition.
It also normalizes the square-carrier derivative at the origin and separates
that intrinsic normalization from the fixed rational-basis determinant.

No nonlinear density cocycle, measure disintegration, or rank recurrence is
asserted here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open Matrix Metric Set MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleJacobianMappedTangentMeasurableSpace (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleJacobianMappedTangentBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

private theorem basis_det_comp_continuousLinearEquiv
    {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (b : Module.Basis ι ℝ E) (b' : Module.Basis ι ℝ E')
    (L : E ≃L[ℝ] E') (D : E →L[ℝ] E') :
    b'.det (fun i => D (b i)) =
      b'.det (b.map L.toLinearEquiv) *
        LinearMap.det
          (L.symm.toLinearMap.comp D.toLinearMap) := by
  let c := b.map L.toLinearEquiv
  have hchange :
      b'.det = b'.det c • c.det :=
    AlternatingMap.eq_smul_basis_det c b'.det
  calc
    b'.det (fun i => D (b i)) =
        (b'.det c • c.det) (fun i => D (b i)) := by
      rw [← hchange]
    _ = b'.det c * c.det (fun i => D (b i)) := by
      simp
    _ = b'.det c *
        b.det (fun i => L.symm (D (b i))) := by
      rw [Module.Basis.det_map]
      congr 1
    _ = b'.det c *
        LinearMap.det (L.symm.toLinearMap.comp D.toLinearMap) := by
      rw [show (fun i => L.symm (D (b i))) =
          (L.symm.toLinearMap.comp D.toLinearMap) ∘ b by rfl,
        Module.Basis.det_comp, Module.Basis.det_self, mul_one]

/-- The lower identity-chart coordinate represented by a point of the exact
higher-chart source. -/
def identitySpecialOrthogonalNorthPoleProductLowerCoordinate
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).target :=
  ⟨p.1.1,
    (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
      n p.2).1⟩

/-- Every point of the product-transition target lies in the higher
identity-chart target. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_subset_identityChartTarget
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n ⊆
      (specialFormPreservingSmoothRealIdentityChart
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
        identityRationalForm_isSymm identityRationalForm_det_ne_zero).target := by
  rintro y ⟨g, hg, rfl⟩
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm
      identityRationalForm_det_ne_zero).map_source hg.2

/-- The higher identity-chart coordinate represented by a point of the exact
product-transition target. -/
def identitySpecialOrthogonalNorthPoleProductHigherCoordinate
    (n : ℕ)
    (y : identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) :
    (specialFormPreservingSmoothRealIdentityChart
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero).target :=
  ⟨y.1,
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_subset_identityChartTarget
      n y.2⟩

/-- Product of the lower identity-chart differential density and the
north-pole sphere-coordinate density on the exact transition source. -/
def identitySpecialOrthogonalNorthPoleProductSourceDensity
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    ℝ≥0∞ :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
      (identitySpecialOrthogonalNorthPoleProductLowerCoordinate n p) *
    identitySpecialOrthogonalNorthPoleCoordinateDensity p.1.2

/-- The higher identity-chart differential density on the exact
transition target. -/
def identitySpecialOrthogonalNorthPoleProductTargetDensity
    (n : ℕ)
    (y : identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) :
    ℝ≥0∞ :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero 1
    (identitySpecialOrthogonalNorthPoleProductHigherCoordinate n y)

/-- The product transition restricted to its exact source and target. -/
def identitySpecialOrthogonalNorthPoleProductTransitionOnSource
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n :=
  ⟨identitySpecialOrthogonalNorthPoleProductTransition n p.1, by
    rw [← image_identitySpecialOrthogonalNorthPoleProductTransition_source]
    exact ⟨p.1, p.2, rfl⟩⟩

theorem
    continuous_identitySpecialOrthogonalNorthPoleProductTransitionOnSource
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n) := by
  apply Continuous.subtype_mk
  exact continuousOn_iff_continuous_restrict.mp
    (contDiffOn_identitySpecialOrthogonalNorthPoleProductTransition_higherChartSource
      n).continuousOn

/-- The higher chart density pulled back along the exact product transition. -/
def identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    ℝ≥0∞ :=
  identitySpecialOrthogonalNorthPoleProductTargetDensity n
    (identitySpecialOrthogonalNorthPoleProductTransitionOnSource n p)

theorem measurable_identitySpecialOrthogonalNorthPoleProductSourceDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductSourceDensity n) := by
  have hlower :
      Measurable
        (identitySpecialOrthogonalNorthPoleProductLowerCoordinate n) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).measurable
  have hsphere :
      Measurable
        (fun p :
            identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n =>
          identitySpecialOrthogonalNorthPoleCoordinateDensity p.1.2) :=
    (measurable_identitySpecialOrthogonalNorthPoleCoordinateDensity n).comp
      (continuous_snd.comp continuous_subtype_val).measurable
  exact
    ((measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero 1).comp
        hlower).mul hsphere

theorem measurable_identitySpecialOrthogonalNorthPoleProductTargetDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductTargetDensity n) := by
  exact
    (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero 1).comp
      (continuous_subtype_val.subtype_mk _).measurable

theorem
    measurable_identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
        n) :=
  (measurable_identitySpecialOrthogonalNorthPoleProductTargetDensity n).comp
    (continuous_identitySpecialOrthogonalNorthPoleProductTransitionOnSource
      n).measurable

theorem identitySpecialOrthogonalNorthPoleProductSourceDensity_pos
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    0 < identitySpecialOrthogonalNorthPoleProductSourceDensity n p := by
  apply bot_lt_iff_ne_bot.mpr
  exact mul_ne_zero
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal_pos
      (1 : Matrix (Fin n) (Fin n) ℚ)
      identityRationalForm_isSymm identityRationalForm_det_ne_zero 1 _).ne'
    (identitySpecialOrthogonalNorthPoleCoordinateDensity_pos
      ((identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
        n p.2).2)).ne'

theorem identitySpecialOrthogonalNorthPoleProductTargetDensity_pos
    (n : ℕ)
    (y : identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n) :
    0 < identitySpecialOrthogonalNorthPoleProductTargetDensity n y :=
  specialFormPreservingSmoothRealChartCoordinateDensityENNReal_pos
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero 1 _

/-- The origin in the exact product-transition source. -/
def identitySpecialOrthogonalNorthPoleProductSourceZero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n :=
  ⟨0,
    identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_zero_mem n⟩

theorem
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_zero_mem
    (n : ℕ) :
    (0 : identitySpecialOrthogonalMappedTangent (n + 1)) ∈
      identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n := by
  rw [← image_identitySpecialOrthogonalNorthPoleProductTransition_source]
  exact
    ⟨0,
      identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_zero_mem n,
      identitySpecialOrthogonalNorthPoleProductTransition_zero n⟩

/-- The origin in the exact product-transition target. -/
def identitySpecialOrthogonalNorthPoleProductTargetZero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet n :=
  ⟨0,
    identitySpecialOrthogonalNorthPoleProductTransitionTargetSet_zero_mem n⟩

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductTransitionOnSource_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionOnSource n
        (identitySpecialOrthogonalNorthPoleProductSourceZero n) =
      identitySpecialOrthogonalNorthPoleProductTargetZero n := by
  apply Subtype.ext
  exact identitySpecialOrthogonalNorthPoleProductTransition_zero n

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductSourceDensity_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductSourceDensity n
        (identitySpecialOrthogonalNorthPoleProductSourceZero n) =
      1 := by
  simp [identitySpecialOrthogonalNorthPoleProductSourceDensity,
    identitySpecialOrthogonalNorthPoleProductLowerCoordinate,
    identitySpecialOrthogonalNorthPoleProductSourceZero,
    specialFormPreservingSmoothRealIdentityChartCoordinateDensityENNReal_zero]

@[simp]
theorem identitySpecialOrthogonalNorthPoleProductTargetDensity_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTargetDensity n
        (identitySpecialOrthogonalNorthPoleProductTargetZero n) =
      1 := by
  simp [identitySpecialOrthogonalNorthPoleProductTargetDensity,
    identitySpecialOrthogonalNorthPoleProductHigherCoordinate,
    identitySpecialOrthogonalNorthPoleProductTargetZero,
    specialFormPreservingSmoothRealIdentityChartCoordinateDensityENNReal_zero]

/-- The ENNReal square-carrier Jacobian used by the nonlinear
change-of-variables theorem. -/
def identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    ℝ≥0∞ :=
  ENNReal.ofReal
    |LinearMap.det
      (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
        n p).toLinearMap|

/-- Determinant of the actual pointwise transition derivative relative to the
fixed source and target bases. -/
def identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).det
    (fun i =>
      fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransition n) p
        (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n i))

/-- The pointwise fixed-basis determinant is the fixed linear comparison
scalar times the intrinsic square-carrier determinant. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar_eq
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar n p =
      identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
            n p).toLinearMap := by
  simpa only [
    identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar,
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar,
    identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative] using
    basis_det_comp_continuousLinearEquiv
      (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n)
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n)
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv n)
      (fderiv ℝ
        (identitySpecialOrthogonalNorthPoleProductTransition n) p)

/-- Absolute values give the corresponding nonnegative pointwise
factorization used in measure comparisons. -/
theorem
    abs_identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
    (n : ℕ)
    (p : identitySpecialOrthogonalMappedTangent n ×
      EuclideanSpace ℝ (Fin n)) :
    |identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
        n p| =
      |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductTransitionSquareDerivative
            n p).toLinearMap| := by
  rw [
    identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar_eq,
    abs_mul]

/-- The exact remaining intrinsic pointwise density comparison.  The fixed
basis determinant does not occur here because the square map has already
removed it. -/
def identitySpecialOrthogonalNorthPoleProductDensityCocycleAt
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    Prop :=
  identitySpecialOrthogonalNorthPoleProductSourceDensity n p =
    identitySpecialOrthogonalNorthPoleProductTransitionSquareJacobian n p.1 *
      identitySpecialOrthogonalNorthPoleProductTargetDensityAlongTransition
        n p

end PositiveDefiniteIntegralLattice
