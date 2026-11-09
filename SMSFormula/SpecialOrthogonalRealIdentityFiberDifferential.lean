import SMSFormula.SpecialOrthogonalRealIdentityProbabilityDisintegration

open scoped Matrix Matrix.Norms.Operator ENNReal ProbabilityTheory

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

local instance identitySpecialOrthogonalGroupMeasurableSpace_fiberDifferential
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace_fiberDifferential
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Scale every value of a kernel by one fixed `ENNReal` scalar. -/
def fixedENNRealSmulKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ℝ≥0∞) (κ : ProbabilityTheory.Kernel α β) :
    ProbabilityTheory.Kernel α β :=
  ⟨fun a => c • κ a, by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.smul_apply, smul_eq_mul]
    exact measurable_const.mul (κ.measurable_coe hA)⟩

@[simp]
theorem fixedENNRealSmulKernel_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ℝ≥0∞) (κ : ProbabilityTheory.Kernel α β) (a : α) :
    fixedENNRealSmulKernel c κ a = c • κ a :=
  rfl

theorem fixedENNRealSmulKernel_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ℝ≥0∞) (κ : ProbabilityTheory.Kernel α β) (μ : Measure α) :
    fixedENNRealSmulKernel c κ ∘ₘ μ = c • (κ ∘ₘ μ) := by
  ext A hA
  rw [Measure.bind_apply hA
      (fixedENNRealSmulKernel c κ).measurable.aemeasurable,
    Measure.smul_apply, Measure.bind_apply hA κ.measurable.aemeasurable]
  simp_rw [fixedENNRealSmulKernel_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul c (κ.measurable_coe hA)]

/-- A fixed finite scalar multiple of a Markov kernel is a finite kernel. -/
theorem fixedENNRealSmulKernel_isFinite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : ℝ≥0∞) (hc : c < ∞) (κ : ProbabilityTheory.Kernel α β)
    [ProbabilityTheory.IsMarkovKernel κ] :
    ProbabilityTheory.IsFiniteKernel (fixedENNRealSmulKernel c κ) := by
  refine ⟨c, hc, fun a => ?_⟩
  letI : IsProbabilityMeasure (κ a) :=
    ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure a
  rw [fixedENNRealSmulKernel_apply, Measure.smul_apply, measure_univ]
  simp

/-- Lower-rank canonical differential Haar translated onto the last-column
fiber represented by `g`. -/
def identitySpecialOrthogonalLastColumnFiberDifferentialMeasure
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  Measure.map (identitySpecialOrthogonalLastColumnFiberParametrization n g)
    (identitySpecialOrthogonalDifferentialMeasure n)

theorem identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g := by
  calc
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g =
        Measure.map (identitySpecialOrthogonalLastColumnFiberParametrization n g)
          (identitySpecialOrthogonalDifferentialMeasure n) := rfl
    _ = Measure.map
        (identitySpecialOrthogonalLastColumnFiberParametrization n g)
        (identitySpecialOrthogonalDifferentialMeasure n Set.univ •
          identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      exact congrArg
        (Measure.map
          (identitySpecialOrthogonalLastColumnFiberParametrization n g))
        (identitySpecialOrthogonalDifferentialMeasure_eq_univ_smul_probabilityHaar n)
    _ = identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        Measure.map (identitySpecialOrthogonalLastColumnFiberParametrization n g)
          (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      rw [Measure.map_smul]
    _ = identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g := rfl

theorem identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_univ
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g Set.univ =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ := by
  rw [
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability,
    Measure.smul_apply,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_univ]
  simp

theorem identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_compl_fiber_eq_zero
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g
        (identitySpecialOrthogonalLastColumnFiberAt (n + 1)
          (identitySpecialOrthogonalLastColumn (n + 1) g))ᶜ = 0 := by
  rw [
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability,
    Measure.smul_apply,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_compl_fiber_eq_zero]
  simp

theorem identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_of_lastColumn_eq
    (n : ℕ) (g k : identitySpecialOrthogonalGroup (n + 1))
    (hcol : identitySpecialOrthogonalLastColumn (n + 1) g =
      identitySpecialOrthogonalLastColumn (n + 1) k) :
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g =
      identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n k := by
  rw [
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability,
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_eq_of_lastColumn_eq
      n g k hcol]

/-- The representative-independent differential fiber candidate on the
right-coset quotient. -/
def identitySpecialOrthogonalLastColumnQuotientFiberDifferentialMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1) →
      Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  fun q =>
    identitySpecialOrthogonalDifferentialMeasure n Set.univ •
      identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n q

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientFiberDifferentialMeasure_mk
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnQuotientFiberDifferentialMeasure n
        (QuotientGroup.mk g) =
      identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g := by
  rw [identitySpecialOrthogonalLastColumnQuotientFiberDifferentialMeasure,
    identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure_mk,
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability]

/-- The differential fiber candidate indexed by the unit sphere. -/
def identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphere (n + 1) →
      Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  fun x =>
    identitySpecialOrthogonalDifferentialMeasure n Set.univ •
      identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n x

@[simp]
theorem identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_lastColumn
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n
        (identitySpecialOrthogonalLastColumn (n + 1) g) =
      identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g := by
  rw [identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure,
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_lastColumn,
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability]

/-- The measurable differential-fiber candidate indexed by group
representatives. -/
def identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalGroup (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  fixedENNRealSmulKernel
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n)

@[simp]
theorem identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel n g =
      identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g := by
  rw [identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel,
    fixedENNRealSmulKernel_apply,
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_apply,
    identitySpecialOrthogonalLastColumnFiberDifferentialMeasure_eq_univ_smul_probability]

instance identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel_instFinite
    (n : ℕ) :
    ProbabilityTheory.IsFiniteKernel
      (identitySpecialOrthogonalLastColumnGroupFiberDifferentialKernel n) :=
  fixedENNRealSmulKernel_isFinite
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (measure_lt_top _ _) _

/-- The measurable differential-fiber candidate indexed by the right-coset
quotient. -/
def identitySpecialOrthogonalLastColumnQuotientFiberDifferentialKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  fixedENNRealSmulKernel
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel n)

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientFiberDifferentialKernel_apply
    (n : ℕ)
    (q : identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1)) :
    identitySpecialOrthogonalLastColumnQuotientFiberDifferentialKernel n q =
      identitySpecialOrthogonalLastColumnQuotientFiberDifferentialMeasure n q :=
  rfl

instance
    identitySpecialOrthogonalLastColumnQuotientFiberDifferentialKernel_instFinite
    (n : ℕ) :
    ProbabilityTheory.IsFiniteKernel
      (identitySpecialOrthogonalLastColumnQuotientFiberDifferentialKernel n) :=
  fixedENNRealSmulKernel_isFinite
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (measure_lt_top _ _) _

/-- The measurable differential-fiber candidate indexed by the unit sphere. -/
def identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalLastColumnSphere (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  fixedENNRealSmulKernel
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n)

@[simp]
theorem identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
      identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n x :=
  rfl

instance identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_instFinite
    (n : ℕ) :
    ProbabilityTheory.IsFiniteKernel
      (identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n) :=
  fixedENNRealSmulKernel_isFinite
    (identitySpecialOrthogonalDifferentialMeasure n Set.univ)
    (measure_lt_top _ _) _

/-- Integrating the differential-fiber candidate over normalized sphere
measure gives lower-rank differential mass times ambient probability Haar. -/
theorem identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_comp_normalizedSphereMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n ∘ₘ
        identitySpecialOrthogonalNormalizedSphereMeasure (n + 1) =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
  rw [identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel,
    fixedENNRealSmulKernel_comp,
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_comp_normalizedSphereMeasure]

end PositiveDefiniteIntegralLattice
