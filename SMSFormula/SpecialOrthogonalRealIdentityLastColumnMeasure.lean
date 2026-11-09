import SMSFormula.SpecialOrthogonalRealIdentityLastColumnHomogeneousSpaceTopology
import SMSFormula.SpecialOrthogonalRealIdentityMappedGroupEquiv
import SMSFormula.SpecialOrthogonalRealIdentityTangentDetFactorization

/-!
# Identity last-column pushforward measures
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory
open TopologicalSpace

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

def identitySpecialOrthogonalLastColumnSphereActionHomeomorph
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnSphere n ≃ₜ
      identitySpecialOrthogonalLastColumnSphere n := by
  letI : MulAction (identitySpecialOrthogonalGroup n)
      (identitySpecialOrthogonalLastColumnHomogeneousSpace n) :=
    MulAction.quotient (identitySpecialOrthogonalGroup n)
      (identitySpecialOrthogonalLastColumnStabilizerSubgroup n)
  letI : ContinuousSMul (identitySpecialOrthogonalGroup n)
      (identitySpecialOrthogonalLastColumnHomogeneousSpace n) :=
    QuotientGroup.instContinuousSMul
  exact
    (identitySpecialOrthogonalLastColumnQuotientHomeomorph n hn).symm.trans
      ((Homeomorph.smul g).trans
        (identitySpecialOrthogonalLastColumnQuotientHomeomorph n hn))

@[simp] theorem identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply
    (n : ℕ) (hn : 0 < n) (g h : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
        (identitySpecialOrthogonalLastColumn n h) =
      identitySpecialOrthogonalLastColumn n (g * h) := by
  letI : MulAction (identitySpecialOrthogonalGroup n)
      (identitySpecialOrthogonalLastColumnHomogeneousSpace n) :=
    MulAction.quotient (identitySpecialOrthogonalGroup n)
      (identitySpecialOrthogonalLastColumnStabilizerSubgroup n)
  let H := identitySpecialOrthogonalLastColumnQuotientHomeomorph n hn
  have hx :
      H.symm (identitySpecialOrthogonalLastColumn n h) =
        QuotientGroup.mk h := by
    apply H.injective
    simp [H]
  rw [identitySpecialOrthogonalLastColumnSphereActionHomeomorph]
  change H (g • H.symm (identitySpecialOrthogonalLastColumn n h)) =
    identitySpecialOrthogonalLastColumn n (g * h)
  rw [hx]
  change H (QuotientGroup.mk (g * h)) =
    identitySpecialOrthogonalLastColumn n (g * h)
  exact identitySpecialOrthogonalLastColumnQuotientHomeomorph_mk
    n hn (g * h)

theorem coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply
    (n : ℕ) (hn : 0 < n) (g h : identitySpecialOrthogonalGroup n) :
    (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
        (identitySpecialOrthogonalLastColumn n h) :
      EuclideanSpace ℝ (Fin (n + 1))) =
      identitySpecialOrthogonalMatrixActionVector n g
        (identitySpecialOrthogonalLastColumnVector n h) := by
  rw [identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply,
    coe_identitySpecialOrthogonalLastColumn,
    identitySpecialOrthogonalLastColumnVector_mul]

theorem coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n)
    (x : identitySpecialOrthogonalLastColumnSphere n) :
    (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x :
      EuclideanSpace ℝ (Fin (n + 1))) =
      identitySpecialOrthogonalMatrixActionVector n g x := by
  obtain ⟨h, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn n hn x
  exact
    coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply
      n hn g h

/-- The scalar-extended rational identity-form group is continuously
multiplicatively equivalent to the literal real identity-form group. -/
def identitySpecialOrthogonalMappedGroupContinuousEquiv (n : ℕ) :
    specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ)) ≃ₜ*
      identitySpecialOrthogonalGroup n :=
  identitySpecialOrthogonalMappedLiteralContinuousMulEquiv (n + 1)

local instance identitySpecialOrthogonalGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identitySpecialOrthogonalMappedGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  borel _

local instance identitySpecialOrthogonalMappedGroupBorelSpace (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
          (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Differential Haar on the literal identity-form group, retaining the
single rational tangent differential normalization. -/
def identitySpecialOrthogonalDifferentialMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalGroup n) :=
  Measure.map (identitySpecialOrthogonalMappedGroupContinuousEquiv n)
    (specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      (by simp) (by simp))

theorem identitySpecialOrthogonalDifferentialMeasure_isHaarMeasure
    (n : ℕ) :
    Measure.IsHaarMeasure
      (identitySpecialOrthogonalDifferentialMeasure n) := by
  let μ :
      Measure
        (specialFormPreservingMatrixSubgroup
          ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ).map
            (algebraMap ℚ ℝ))) :=
    specialFormPreservingSmoothRealDifferentialMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      (by simp) (by simp)
  letI : Measure.IsHaarMeasure μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
      (by simp) (by simp)
  change Measure.IsHaarMeasure
    (Measure.map (identitySpecialOrthogonalMappedGroupContinuousEquiv n) μ)
  exact
    (identitySpecialOrthogonalMappedGroupContinuousEquiv n).isHaarMeasure_map μ

instance identitySpecialOrthogonalDifferentialMeasure_instHaarMeasure
    (n : ℕ) :
    Measure.IsHaarMeasure
      (identitySpecialOrthogonalDifferentialMeasure n) :=
  identitySpecialOrthogonalDifferentialMeasure_isHaarMeasure n

instance identitySpecialOrthogonalDifferentialMeasure_instFiniteMeasure
    (n : ℕ) :
    IsFiniteMeasure (identitySpecialOrthogonalDifferentialMeasure n) :=
  ⟨isCompact_univ.measure_lt_top⟩

theorem identitySpecialOrthogonalDifferentialMeasure_univ_pos (n : ℕ) :
    0 < identitySpecialOrthogonalDifferentialMeasure n Set.univ :=
  isOpen_univ.measure_pos _ Set.univ_nonempty

/-- The whole compact identity group as a Haar normalization set. -/
def identitySpecialOrthogonalUnivPositiveCompacts (n : ℕ) :
    PositiveCompacts (identitySpecialOrthogonalGroup n) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

/-- Probability Haar on the literal identity-form group. -/
def identitySpecialOrthogonalProbabilityHaarMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalGroup n) :=
  Measure.haarMeasure (identitySpecialOrthogonalUnivPositiveCompacts n)

instance identitySpecialOrthogonalProbabilityHaarMeasure_instHaarMeasure
    (n : ℕ) :
    Measure.IsHaarMeasure
      (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
  unfold identitySpecialOrthogonalProbabilityHaarMeasure
  infer_instance

theorem identitySpecialOrthogonalProbabilityHaarMeasure_univ (n : ℕ) :
    identitySpecialOrthogonalProbabilityHaarMeasure n Set.univ = 1 :=
  by
    simpa [identitySpecialOrthogonalProbabilityHaarMeasure,
      identitySpecialOrthogonalUnivPositiveCompacts] using
        (Measure.haarMeasure_self
          (K₀ := identitySpecialOrthogonalUnivPositiveCompacts n))

instance identitySpecialOrthogonalProbabilityHaarMeasure_instFiniteMeasure
    (n : ℕ) :
    IsFiniteMeasure (identitySpecialOrthogonalProbabilityHaarMeasure n) :=
  ⟨by
    rw [identitySpecialOrthogonalProbabilityHaarMeasure_univ]
    exact ENNReal.one_lt_top⟩

/-- The last-column pushforward of identity differential Haar. -/
def identitySpecialOrthogonalLastColumnDifferentialMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalLastColumnSphere n) :=
  Measure.map (identitySpecialOrthogonalLastColumn n)
    (identitySpecialOrthogonalDifferentialMeasure n)

/-- The last-column pushforward of probability Haar. -/
def identitySpecialOrthogonalLastColumnProbabilityMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalLastColumnSphere n) :=
  Measure.map (identitySpecialOrthogonalLastColumn n)
    (identitySpecialOrthogonalProbabilityHaarMeasure n)

theorem identitySpecialOrthogonalLastColumnDifferentialMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnDifferentialMeasure n Set.univ =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ := by
  rw [identitySpecialOrthogonalLastColumnDifferentialMeasure,
    Measure.map_apply
      (continuous_identitySpecialOrthogonalLastColumn n).measurable
      MeasurableSet.univ]
  simp

theorem identitySpecialOrthogonalLastColumnProbabilityMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnProbabilityMeasure n Set.univ = 1 := by
  rw [identitySpecialOrthogonalLastColumnProbabilityMeasure,
    Measure.map_apply
      (continuous_identitySpecialOrthogonalLastColumn n).measurable
      MeasurableSet.univ]
  simpa using identitySpecialOrthogonalProbabilityHaarMeasure_univ n

instance identitySpecialOrthogonalLastColumnDifferentialMeasure_instFiniteMeasure
    (n : ℕ) :
    IsFiniteMeasure
      (identitySpecialOrthogonalLastColumnDifferentialMeasure n) :=
  ⟨by
    rw [identitySpecialOrthogonalLastColumnDifferentialMeasure_univ]
    exact measure_lt_top _ _⟩

instance identitySpecialOrthogonalLastColumnProbabilityMeasure_instFiniteMeasure
    (n : ℕ) :
    IsFiniteMeasure
      (identitySpecialOrthogonalLastColumnProbabilityMeasure n) :=
  ⟨by
    rw [identitySpecialOrthogonalLastColumnProbabilityMeasure_univ]
    exact ENNReal.one_lt_top⟩

theorem identitySpecialOrthogonalLastColumnDifferentialMeasure_univ_pos
    (n : ℕ) :
    0 <
      identitySpecialOrthogonalLastColumnDifferentialMeasure n Set.univ := by
  rw [identitySpecialOrthogonalLastColumnDifferentialMeasure_univ]
  exact identitySpecialOrthogonalDifferentialMeasure_univ_pos n

theorem identitySpecialOrthogonalLastColumnProbabilityMeasure_univ_pos
    (n : ℕ) :
    0 <
      identitySpecialOrthogonalLastColumnProbabilityMeasure n Set.univ := by
  rw [identitySpecialOrthogonalLastColumnProbabilityMeasure_univ]
  exact zero_lt_one

theorem identitySpecialOrthogonalLastColumnDifferentialMeasure_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnDifferentialMeasure n ≠ 0 := by
  intro h
  have hpos :=
    identitySpecialOrthogonalLastColumnDifferentialMeasure_univ_pos n
  rw [h] at hpos
  simp at hpos

theorem identitySpecialOrthogonalLastColumnProbabilityMeasure_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnProbabilityMeasure n ≠ 0 := by
  intro h
  have hpos :=
    identitySpecialOrthogonalLastColumnProbabilityMeasure_univ_pos n
  rw [h] at hpos
  simp at hpos

instance identitySpecialOrthogonalLastColumnProbabilityMeasure_instProbability
    (n : ℕ) :
    IsProbabilityMeasure
      (identitySpecialOrthogonalLastColumnProbabilityMeasure n) :=
  ⟨identitySpecialOrthogonalLastColumnProbabilityMeasure_univ n⟩

private theorem map_identitySpecialOrthogonalLastColumnMeasure_sphereAction
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n)
    (μ : Measure (identitySpecialOrthogonalGroup n))
    [Measure.IsMulLeftInvariant μ] :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        (Measure.map (identitySpecialOrthogonalLastColumn n) μ) =
      Measure.map (identitySpecialOrthogonalLastColumn n) μ := by
  rw [Measure.map_map
    (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g).measurable
    (continuous_identitySpecialOrthogonalLastColumn n).measurable]
  have hcomp :
      (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g :
          identitySpecialOrthogonalLastColumnSphere n →
            identitySpecialOrthogonalLastColumnSphere n) ∘
          identitySpecialOrthogonalLastColumn n =
        identitySpecialOrthogonalLastColumn n ∘ fun h => g * h := by
    funext h
    exact
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply
        n hn g h
  rw [hcomp, ← Measure.map_map
    (continuous_identitySpecialOrthogonalLastColumn n).measurable
    (measurable_const_mul g),
    map_mul_left_eq_self]

theorem map_identitySpecialOrthogonalLastColumnDifferentialMeasure_sphereAction
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        (identitySpecialOrthogonalLastColumnDifferentialMeasure n) =
      identitySpecialOrthogonalLastColumnDifferentialMeasure n := by
  exact
    map_identitySpecialOrthogonalLastColumnMeasure_sphereAction n hn g
      (identitySpecialOrthogonalDifferentialMeasure n)

theorem map_identitySpecialOrthogonalLastColumnProbabilityMeasure_sphereAction
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        (identitySpecialOrthogonalLastColumnProbabilityMeasure n) =
      identitySpecialOrthogonalLastColumnProbabilityMeasure n := by
  exact
    map_identitySpecialOrthogonalLastColumnMeasure_sphereAction n hn g
      (identitySpecialOrthogonalProbabilityHaarMeasure n)

end PositiveDefiniteIntegralLattice
