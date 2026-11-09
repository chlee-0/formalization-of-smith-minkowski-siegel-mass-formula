import SMSFormula.TranslatedHomChartTwoSheet
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalHaar
import SMSFormula.RationalCliffordGeneralSpinFieldCentralFiber

/-! Two-sheet mass of the horizontal p-ADIC GSpin Haar. The horizontal
differential Haar on intrinsic `GSpin(V)(ℚ_p)` is glued from
`Haar(ℚ_p^×) × padicInvariantDifferentialGroupMeasure` through the central
fiber map `φ = (similitude, toSO)`, whose kernel is `{1, -1}`. Hence for every
measurable `B ⊆ ℚ_p^× × SO`,

`μ_GSpin(φ⁻¹ B) = 2 · (Haar × μ_SO)(B ∩ range φ)`.

This is step (a) of the GSpin central factor. No section, sheet or normalization is chosen. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.TranslatedHomChart

variable {G H : Type*} [Group G] [Group H]

/-- A kernel `{1, z}` gives two-point fibers `{x, x z}`. -/
theorem fiber_iff_of_ker_eq_pair (f : G →* H) {z : G} (hker : (f.ker : Set G) = {1, z})
    (x y : G) : f x = f y ↔ y = x ∨ y = x * z := by
  have hmem : ∀ w, f w = 1 ↔ w = 1 ∨ w = z := fun w ↦ by
    have : w ∈ (f.ker : Set G) ↔ w ∈ ({1, z} : Set G) := by rw [hker]
    simpa using this
  constructor
  · intro h
    have h1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rcases (hmem _).mp h1 with h2 | h2
    · left; rw [← mul_inv_cancel_left x y, h2, mul_one]
    · right; rw [← mul_inv_cancel_left x y, h2]
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, (hmem z).mpr (Or.inr rfl), mul_one]

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1200000

noncomputable local instance twoSheetPadicUnitMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance twoSheetPadicUnitBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance twoSheetPadicSOMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance twoSheetPadicSOBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- Two-sheet mass: `μ_GSpin(φ⁻¹ B) = 2 · (Haar × μ_SO)(B ∩ range φ)`. -/
theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage
    (p : ℕ) [Fact (Nat.Prime p)] {B : Set (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p])}
    (hB : MeasurableSet B) :
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] ⁻¹' B) =
      2 * V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p
        (B ∩ Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])) := by
  have hfe := V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p
  have hone := V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p
  have hcont : Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) := by
    refine continuous_of_continuousAt_one
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) ?_
    have h := (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).continuousAt hone
    rwa [← hfe] at h
  exact MeasureTheory.TranslatedHomChart.gluedMeasure_preimage_eq_two_mul _ _ hfe hone _
    (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℚ_[p])
    (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint_ne_one V ℚ_[p])
    (MeasureTheory.TranslatedHomChart.fiber_iff_of_ker_eq_pair _
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_ker_eq_pair V ℚ_[p]))
    hcont hB

end RationalQuadraticSpaceMatrix
