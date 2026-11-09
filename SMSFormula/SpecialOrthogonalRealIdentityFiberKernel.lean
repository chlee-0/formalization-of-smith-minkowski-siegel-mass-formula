import SMSFormula.SpecialOrthogonalRealIdentityFiberProbability
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable probability kernels on identity last-column fibers
-/

open scoped Matrix Matrix.Norms.Operator ENNReal ProbabilityTheory

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

local instance identitySpecialOrthogonalGroupMeasurableSpace_fiberKernel
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace_fiberKernel
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

local instance identitySpecialOrthogonalGroupSecondCountableTopology_fiberKernel
    (n : ℕ) :
    SecondCountableTopology (identitySpecialOrthogonalGroup n) := by
  letI : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin (n + 1) → Fin (n + 1) → ℝ))
  let e :=
    specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  exact e.symm.isEmbedding.secondCountableTopology

local instance identitySpecialOrthogonalGroupPolishSpace_fiberKernel
    (n : ℕ) :
    PolishSpace (identitySpecialOrthogonalGroup n) := by
  letI : PolishSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    inferInstanceAs (PolishSpace (Fin (n + 1) → Fin (n + 1) → ℝ))
  letI : PolishSpace
      (Matrix.specialOrthogonalMatrixSet
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) :=
    (isClosed_identitySpecialOrthogonalMatrixSet n).polishSpace
  let e :=
    specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  exact e.symm.isClosedEmbedding.polishSpace

local instance
    identitySpecialOrthogonalLastColumnHomogeneousSpaceT2Space_fiberKernel
    (n : ℕ) :
    T2Space
      (identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1)) :=
  (identitySpecialOrthogonalLastColumnQuotientHomeomorph
    (n + 1) (Nat.succ_pos n)).isEmbedding.t2Space

/-- The translated block embedding jointly in its ambient representative and
lower-rank fiber coordinate. -/
def identitySpecialOrthogonalLastColumnFiberJointParametrization
    (n : ℕ) :
    identitySpecialOrthogonalGroup (n + 1) ×
        identitySpecialOrthogonalGroup n →
      identitySpecialOrthogonalGroup (n + 1) :=
  fun p =>
    p.1 * identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n p.2

theorem continuous_identitySpecialOrthogonalLastColumnFiberJointParametrization
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalLastColumnFiberJointParametrization n) :=
  continuous_fst.mul
    ((continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n).comp
      continuous_snd)

theorem measurable_identitySpecialOrthogonalLastColumnFiberJointParametrization
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalLastColumnFiberJointParametrization n) :=
  (continuous_identitySpecialOrthogonalLastColumnFiberJointParametrization n).measurable

theorem identitySpecialOrthogonalLastColumnFiberJointParametrization_prodMk
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    (fun h => identitySpecialOrthogonalLastColumnFiberJointParametrization n
      (g, h)) =
      identitySpecialOrthogonalLastColumnFiberParametrization n g :=
  rfl

/-- The measurable probability kernel indexed by ambient group
representatives. -/
def identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalGroup (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        (identitySpecialOrthogonalGroup (n + 1))
        (identitySpecialOrthogonalProbabilityHaarMeasure n))
    (identitySpecialOrthogonalLastColumnFiberJointParametrization n)

@[simp]
theorem identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n g =
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g := by
  ext A hA
  rw [identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel,
    ProbabilityTheory.Kernel.map_apply'
      _ (continuous_identitySpecialOrthogonalLastColumnFiberJointParametrization n).measurable
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ g
      ((continuous_identitySpecialOrthogonalLastColumnFiberJointParametrization n).measurable
        hA),
    ProbabilityTheory.Kernel.const_apply,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure,
    Measure.map_apply
      (continuous_identitySpecialOrthogonalLastColumnFiberParametrization n g).measurable
      hA]
  rfl

/-- The group-representative-indexed probability fiber measures form a
measurable measure-valued map. -/
theorem measurable_identitySpecialOrthogonalLastColumnFiberProbabilityMeasure
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n) := by
  have hkernel :
      Measurable fun g =>
        identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n g :=
    (identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n).measurable
  simpa only [
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_apply] using
      hkernel

instance identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_instMarkov
    (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel
      (identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n) where
  isProbabilityMeasure g := by
    rw [identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_apply]
    infer_instance

/-- The representative-independent quotient-indexed fiber family is
measurable. -/
theorem measurable_identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n) := by
  rw [QuotientGroup.measurable_from_quotient]
  simpa only [Function.comp_apply,
    identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure_mk] using
      measurable_identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n

/-- The measurable probability kernel indexed by the right-coset quotient. -/
def identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  ⟨identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n,
    measurable_identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n⟩

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel_apply
    (n : ℕ)
    (q : identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1)) :
    identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel n q =
      identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n q :=
  rfl

instance identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel_instMarkov
    (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel
      (identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel n) where
  isProbabilityMeasure q := by
    induction q using Quotient.inductionOn' with
    | _ g =>
        rw [
          identitySpecialOrthogonalLastColumnQuotientFiberProbabilityKernel_apply,
          identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure_mk]
        infer_instance

/-- The sphere-indexed probability fiber family is measurable. -/
theorem measurable_identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n) :=
  (measurable_identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n).comp
    (identitySpecialOrthogonalLastColumnQuotientHomeomorph
      (n + 1) (Nat.succ_pos n)).symm.measurable

/-- The measurable probability kernel indexed by the unit sphere. -/
def identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (identitySpecialOrthogonalLastColumnSphere (n + 1))
      (identitySpecialOrthogonalGroup (n + 1)) :=
  ⟨identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n,
    measurable_identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n⟩

@[simp]
theorem identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_apply
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n x =
      identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n x :=
  rfl

instance identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_instMarkov
    (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel
      (identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n) where
  isProbabilityMeasure x := by
    rw [identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_apply]
    infer_instance

end PositiveDefiniteIntegralLattice
