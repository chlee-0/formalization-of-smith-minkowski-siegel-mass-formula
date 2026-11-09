import SMSFormula.RationalQuadraticIsometryGeneralSpinHorizontalThetaTransport
import SMSFormula.RationalCliffordGeneralSpinQuotientLogCutoff

/-!
# Logarithmic shell-theta cutoff transport

The quotient logarithmic idele-class module commutes with every supplied
anisotropic-complement presentation because the intrinsic general-Spin map
preserves the similitude coordinate literally.  Combining this with the
already fixed horizontal theta-cutoff pushforward gives the exact integral
transport for every nonnegative measurable logarithmic cutoff.

The horizontal Haar scalar remains visible.  No quotient representative,
fundamental domain, complement lattice, new measure, or chart is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The quotient logarithmic module is unchanged by the presentation
homeomorphism.  This is the quotient form of the literal preservation of the
intrinsic general-Spin similitude coordinate. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_blockToAmbient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (C : (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx C) =
      (P.blockSpace hx).fullAdelicCliffordGeneralSpinLeftQuotientLogModule C := by
  refine Quot.inductionOn C ?_
  intro g
  rfl

/-- Every nonnegative measurable logarithmic cutoff on the block shell-theta
measure transports to the intrinsic ambient rational-shell density with
exactly the fixed horizontal Haar scalar. -/
theorem lintegral_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure_logCutoff_eq_ambient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    [NeZero m]
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (_hf : Measurable f) :
    (∫⁻ C,
        f ((P.blockSpace hx
          ).fullAdelicCliffordGeneralSpinLeftQuotientLogModule C)
      ∂P.lowerSpace.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
          hx RationalAdele y).1)) =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        ∫⁻ Z,
          f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
        ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
          |>.quotientMeasure).withDensity
            (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
              x Phi) := by
  let eX := P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx
  let muB :=
    P.lowerSpace.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
      (V.nativeRationalQuadraticForm x) hx
      (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
        hx RationalAdele y).1)
  let muA :=
    (V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
        (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
          x Phi)
  let logB :=
    (P.blockSpace hx).fullAdelicCliffordGeneralSpinLeftQuotientLogModule
  let logA := V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
  have hlog : logB = logA ∘ eX := by
    funext C
    exact (P.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_blockToAmbient
      hx C).symm
  have hmap : Measure.map eX muB =
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx • muA := by
    exact P.map_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure_eq_ambient
      hx Phi hPhi
  change (∫⁻ C, f (logB C) ∂muB) = _
  rw [hlog]
  calc
    (∫⁻ C, f (logA (eX C)) ∂muB) =
        ∫⁻ Z, f (logA Z) ∂Measure.map eX muB := by
      exact (lintegral_map_equiv (fun Z ↦ f (logA Z))
        eX.toMeasurableEquiv).symm
    _ = ∫⁻ Z, f (logA Z) ∂
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx • muA) := by
      rw [hmap]
    _ = (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        ∫⁻ Z, f (logA Z) ∂muA := by
      rw [lintegral_smul_measure]
      rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
