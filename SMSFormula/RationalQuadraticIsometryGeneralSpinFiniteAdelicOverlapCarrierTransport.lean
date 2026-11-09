import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierImage
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarFactorization

/-!
# Finite-Haar restriction to presentation overlap cylinders

The global finite-Haar scalar comparison restricts to the exact
block and ambient overlap-cylinder carriers.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierTransportFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance overlapCarrierTransportFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The global finite-Haar comparison restricts with the same scalar
to the exact presentation overlap cylinders. -/
theorem map_blockFiniteHaar_restrict_presentationOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        (((P.blockSpace hx)
          |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure).restrict
            (P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S)) =
      P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx •
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S) := by
  let F := P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
  let μ := (P.blockSpace hx).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let ν := V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let A := P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S
  have hA : MeasurableSet A :=
    P.measurableSet_ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S
  calc
    Measure.map F
        (μ.restrict (P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S)) =
        (Measure.map F μ).restrict A := by
      have hr := Measure.restrict_map (μ := μ) (f := fun g ↦ F g) F.measurable hA
      rw [P.preimage_ambientFiniteAdelicPresentationOverlapCylinderCarrier hx hS] at hr
      exact hr.symm
    _ = (P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx • ν).restrict A := by
      rw [P.map_blockToAmbientFiniteAdelicGeneralSpinHorizontalMeasure_eq_smul hx]
    _ = P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx •
        ν.restrict A := by rw [Measure.restrict_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
