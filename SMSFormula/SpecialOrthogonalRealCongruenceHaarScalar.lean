import SMSFormula.SpecialOrthogonalRealCongruenceGlobalRecovery

/-!
# The real congruence Haar scalar

This module restricts the value-level overlap recovery to measurable subsets.
Later modules choose one finite positive common-open subset and cancel its
mass to identify the global Haar comparison scalar.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceHaarScalarGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceHaarScalarGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Subset-valued consequence of native chart recovery, without retaining the
specialized ambient measure equality. -/
theorem measure_preimage_eq_measure_of_map_eq_native_restrict
    {O S G : Type*}
    [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace G]
    (j : O → S) (i : S → G) (k : O → G)
    (μ : Measure O) (σ : Measure S) (ν : Measure G)
    (P : Set S) (A Q B : Set G)
    (hj : Measurable j) (hi : Measurable i) (hk : Measurable k)
    (hQ : MeasurableSet Q) (hB : MeasurableSet B)
    (hcomp : ∀ x, i (j x) = k x)
    (hmap : Measure.map j μ = σ.restrict P)
    (hchart : ν.restrict A = Measure.map i σ)
    (hpre : i ⁻¹' Q = P) (hsub : Q ⊆ A) (hBQ : B ⊆ Q) :
    μ (k ⁻¹' B) = ν B := by
  have h := congrArg (fun m : Measure G => m B)
    (map_eq_restrict_of_map_eq_native_restrict
      j i k μ σ ν P A Q hj hi hQ hcomp hmap hchart hpre hsub)
  change Measure.map k μ B = (ν.restrict Q) B at h
  rw [Measure.map_apply hk hB, Measure.restrict_apply hB,
    Set.inter_eq_left.mpr hBQ] at h
  exact h

end PositiveDefiniteIntegralLattice
