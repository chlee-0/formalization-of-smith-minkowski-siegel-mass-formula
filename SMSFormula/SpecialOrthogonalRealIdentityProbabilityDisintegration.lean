import SMSFormula.SpecialOrthogonalRealIdentityFiberKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Probability disintegration along the identity last-column map
-/

open scoped Matrix Matrix.Norms.Operator ENNReal ProbabilityTheory

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

local instance identitySpecialOrthogonalGroupMeasurableSpace_probabilityDisintegration
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace_probabilityDisintegration
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Averaging the translated lower-rank block over both probability Haar
measures recovers ambient probability Haar. -/
theorem map_identitySpecialOrthogonalFiberJointParametrization_prod_probabilityHaar
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalLastColumnFiberJointParametrization n)
        ((identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)).prod
          (identitySpecialOrthogonalProbabilityHaarMeasure n)) =
      identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
  ext A hA
  rw [Measure.map_apply
    (measurable_identitySpecialOrthogonalLastColumnFiberJointParametrization n)
    hA]
  rw [Measure.prod_apply_symm
    ((measurable_identitySpecialOrthogonalLastColumnFiberJointParametrization n)
      hA)]
  have hsection :
      ∀ h : identitySpecialOrthogonalGroup n,
        identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)
          ((fun g => (g, h)) ⁻¹'
            (identitySpecialOrthogonalLastColumnFiberJointParametrization n ⁻¹'
              A)) =
          identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) A := by
    intro h
    let k : identitySpecialOrthogonalGroup (n + 1) :=
      identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n h
    have hr := congrArg
      (fun μ : Measure (identitySpecialOrthogonalGroup (n + 1)) => μ A)
      (map_identitySpecialOrthogonalProbabilityHaarMeasure_mul_right
        (n + 1) k)
    change
      (Measure.map (fun g : identitySpecialOrthogonalGroup (n + 1) => g * k)
        (identitySpecialOrthogonalProbabilityHaarMeasure (n + 1))) A =
        identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) A at hr
    rw [Measure.map_apply (continuous_mul_right k).measurable hA] at hr
    simpa only [
      identitySpecialOrthogonalLastColumnFiberJointParametrization,
      Set.preimage_preimage, Function.comp_apply, k] using hr
  simp_rw [hsection]
  rw [lintegral_const,
    identitySpecialOrthogonalProbabilityHaarMeasure_univ, mul_one]

/-- Integrating the group-representative-indexed fiber kernel against
ambient probability Haar recovers ambient probability Haar. -/
theorem identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_comp_probabilityHaar
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n ∘ₘ
        identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) =
      identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
  let κ₀ :
      ProbabilityTheory.Kernel
        (identitySpecialOrthogonalGroup (n + 1))
        (identitySpecialOrthogonalGroup (n + 1) ×
          identitySpecialOrthogonalGroup n) :=
    ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        (identitySpecialOrthogonalGroup (n + 1))
        (identitySpecialOrthogonalProbabilityHaarMeasure n)
  calc
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n ∘ₘ
          identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) =
        Measure.map
          (identitySpecialOrthogonalLastColumnFiberJointParametrization n)
          (κ₀ ∘ₘ
            identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)) := by
      rw [identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel,
        Measure.map_comp _ _
          (measurable_identitySpecialOrthogonalLastColumnFiberJointParametrization n)]
    _ = Measure.map
          (identitySpecialOrthogonalLastColumnFiberJointParametrization n)
          ((identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)).prod
            (identitySpecialOrthogonalProbabilityHaarMeasure n)) := by
      rw [show κ₀ =
          ProbabilityTheory.Kernel.id ×ₖ
            ProbabilityTheory.Kernel.const
              (identitySpecialOrthogonalGroup (n + 1))
              (identitySpecialOrthogonalProbabilityHaarMeasure n) by rfl,
        ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
    _ = identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) :=
      map_identitySpecialOrthogonalFiberJointParametrization_prod_probabilityHaar n

/-- Pulling the sphere-indexed fiber kernel back along the last-column map
recovers the group-representative-indexed kernel. -/
theorem comap_identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel
    (n : ℕ) :
    ProbabilityTheory.Kernel.comap
        (identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n)
        (identitySpecialOrthogonalLastColumn (n + 1))
        (continuous_identitySpecialOrthogonalLastColumn (n + 1)).measurable =
      identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n := by
  ext g
  rw [ProbabilityTheory.Kernel.comap_apply,
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_apply,
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_lastColumn,
    identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_apply]

/-- The sphere-indexed fiber kernel disintegrates ambient probability Haar
over normalized Euclidean sphere measure. -/
theorem identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel_comp_normalizedSphereMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n ∘ₘ
        identitySpecialOrthogonalNormalizedSphereMeasure (n + 1) =
      identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
  rw [← identitySpecialOrthogonalLastColumnProbabilityMeasure_eq_normalizedSphereMeasure
    (n + 1) (Nat.succ_pos n)]
  rw [identitySpecialOrthogonalLastColumnProbabilityMeasure]
  calc
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n ∘ₘ
          Measure.map (identitySpecialOrthogonalLastColumn (n + 1))
            (identitySpecialOrthogonalProbabilityHaarMeasure (n + 1)) =
        (ProbabilityTheory.Kernel.comap
          (identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel n)
          (identitySpecialOrthogonalLastColumn (n + 1))
          (continuous_identitySpecialOrthogonalLastColumn (n + 1)).measurable) ∘ₘ
            identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
      rw [← Measure.deterministic_comp_eq_map
          (continuous_identitySpecialOrthogonalLastColumn (n + 1)).measurable,
        Measure.comp_assoc,
        ProbabilityTheory.Kernel.comp_deterministic_eq_comap]
    _ = identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel n ∘ₘ
          identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) := by
      rw [comap_identitySpecialOrthogonalLastColumnSphereFiberProbabilityKernel]
    _ = identitySpecialOrthogonalProbabilityHaarMeasure (n + 1) :=
      identitySpecialOrthogonalLastColumnGroupFiberProbabilityKernel_comp_probabilityHaar n

end PositiveDefiniteIntegralLattice
