import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measures agreeing on one set

Two left Haar measures on a second-countable locally compact group agree as soon as they agree on
one set of finite positive mass (Haar uniqueness).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem MeasureTheory.Measure.eq_of_isHaarMeasure_of_apply_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    {E : Set G} (h0 : ν E ≠ 0) (htop : ν E ≠ ⊤) (h : μ E = ν E) : μ = ν := by
  have hs := Measure.isMulLeftInvariant_eq_smul μ ν
  have hE := congrArg (fun m : Measure G ↦ m E) hs
  simp only [Measure.smul_apply, h] at hE
  have hc : (Measure.haarScalarFactor μ ν : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right h0 htop).1 hE.symm
    exact this
  rw [hs, show Measure.haarScalarFactor μ ν = 1 from by exact_mod_cast hc, one_smul]
