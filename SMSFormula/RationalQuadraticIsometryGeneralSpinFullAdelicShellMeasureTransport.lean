import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicOrbitFiberKernelTransport
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarComparison

/-!
# Full-adelic shell measure transport across a supplied presentation

The native Riesz shell measure is pushed through the existing shell
homeomorphism.  Binding that transported measure against the transported
orbit-fiber kernel gives the pushforward of native horizontal Haar, hence the
ambient Haar scalar `c_G` times the fixed ambient horizontal Haar.

The ambient shell measure normalized for the fixed ambient Haar is therefore
defined by multiplying the transported Riesz measure by `c_G⁻¹`.  The exact
transport law has scalar `c_G/c_H = c_G`, since the transported stabilizer
normalization has `c_H = 1`, and its bind with the ambient kernel is literally
the fixed ambient Haar.  No coefficient-one presentation invariance, chosen
representative, new chart, cutoff, or Tamagawa theorem is asserted.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance ambientShellMeasureTransportInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance ambientShellMeasureTransportFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance ambientShellMeasureTransportT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

noncomputable local instance ambientShellMeasureTransportBlockGroupMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup :=
  P.lowerSpace.fullAdelicShellMeasurableWeilSourceMeasurableSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientShellMeasureTransportBlockGroupBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup :=
  P.lowerSpace.fullAdelicShellMeasurableWeilSourceBorelSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientShellMeasureTransportBlockShellMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :=
  P.lowerSpace.fullAdelicShellMeasurableWeilTargetMeasurableSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientShellMeasureTransportBlockShellBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :=
  P.lowerSpace.fullAdelicShellMeasurableWeilTargetBorelSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientShellMeasureTransportAmbientGroupMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance ambientShellMeasureTransportAmbientGroupBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance ambientShellMeasureTransportAmbientShellMeasurableSpace :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance ambientShellMeasureTransportAmbientShellBorelSpace :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

/-- Naturality of the shell/kernel bind under the certified shell and group
presentation homeomorphisms. -/
theorem map_fullAdelicNonisotropicLastShellMeasure_bind_ambientKernel_eq_map_bind
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Measure.map
        (P.blockToAmbientShellHomeomorph hx RationalAdele)
        (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (V.nativeRationalQuadraticForm x) hx)).bind
        (P.anisotropicRationalAmbientShellOrbitFiberKernel hx) =
      Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (V.nativeRationalQuadraticForm x) hx).bind
          (P.lowerSpace.fullAdelicNonisotropicLastShellOrbitFiberKernel
            (V.nativeRationalQuadraticForm x) hx)) := by
  let μ := P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
    (V.nativeRationalQuadraticForm x) hx
  let κ := P.lowerSpace.fullAdelicNonisotropicLastShellOrbitFiberKernel
    (V.nativeRationalQuadraticForm x) hx
  let κA := P.anisotropicRationalAmbientShellOrbitFiberKernel hx
  let eX := P.blockToAmbientShellHomeomorph hx RationalAdele
  let eG := P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx
  have heX : Measurable eX := eX.continuous.measurable
  have heG : Measurable eG :=
    P.measurable_blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx
  apply Measure.ext_of_lintegral
  intro f hf
  have houter : Measurable fun y ↦ ∫⁻ z, f z ∂κA y :=
    hf.lintegral_kernel
  calc
    ∫⁻ z, f z ∂(Measure.map eX μ).bind κA =
        ∫⁻ y, ∫⁻ z, f z ∂κA y ∂Measure.map eX μ := by
      rw [Measure.lintegral_bind κA.aemeasurable hf.aemeasurable]
    _ = ∫⁻ y, ∫⁻ z, f z ∂κA (eX y) ∂μ := by
      rw [MeasureTheory.lintegral_map houter heX]
    _ = ∫⁻ y, ∫⁻ g, f (eG g) ∂κ y ∂μ := by
      congr 1
      funext y
      rw [show κA (eX y) = Measure.map eG (κ y) by
        exact P.anisotropicRationalAmbientShellOrbitFiberKernel_apply_homeomorph
          hx y]
      rw [MeasureTheory.lintegral_map hf heG]
    _ = ∫⁻ g, f (eG g) ∂μ.bind κ := by
      symm
      exact Measure.lintegral_bind κ.aemeasurable
        (hf.comp heG).aemeasurable
    _ = ∫⁻ z, f z ∂Measure.map eG (μ.bind κ) := by
      rw [MeasureTheory.lintegral_map hf heG]

/-- The unnormalized transported shell measure and transported kernel bind to
exactly `c_G` times the fixed ambient horizontal Haar. -/
theorem map_fullAdelicNonisotropicLastShellMeasure_bind_ambientKernel_eq_smul_horizontal
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Measure.map
        (P.blockToAmbientShellHomeomorph hx RationalAdele)
        (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (V.nativeRationalQuadraticForm x) hx)).bind
        (P.anisotropicRationalAmbientShellOrbitFiberKernel hx) =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [P.map_fullAdelicNonisotropicLastShellMeasure_bind_ambientKernel_eq_map_bind
    hx]
  rw [P.lowerSpace
    |>.fullAdelicNonisotropicLastShellMeasure_bind_orbitFiberKernel_eq_horizontal]
  exact P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_smul hx

/-- The ambient Riesz shell measure normalized for the fixed ambient
horizontal Haar.  The inverse scalar is forced by `c_H = 1`. -/
noncomputable def anisotropicRationalAmbientShellMeasure
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ((P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞)⁻¹) •
    Measure.map
      (P.blockToAmbientShellHomeomorph hx RationalAdele)
      (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
        (V.nativeRationalQuadraticForm x) hx)

/-- Exact quotient-shell transport law.  The scalar is
`c_G/c_H = c_G`, not one. -/
theorem map_fullAdelicNonisotropicLastShellMeasure_eq_smul_ambient
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.blockToAmbientShellHomeomorph hx RationalAdele)
        (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
          (V.nativeRationalQuadraticForm x) hx) =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) •
        P.anisotropicRationalAmbientShellMeasure hx := by
  rw [anisotropicRationalAmbientShellMeasure, smul_smul]
  rw [ENNReal.mul_inv_cancel
    (ENNReal.coe_ne_zero.mpr
      (ne_of_gt (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx)))
    ENNReal.coe_ne_top,
    one_smul]

/-- Integral form of the exact shell-measure transport law.  The supplied
ambient test function is pulled back through the existing shell
homeomorphism, and the fixed horizontal presentation scalar remains
visible. -/
theorem lintegral_fullAdelicNonisotropicLastShellMeasure_eq_mul_ambient
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (f : V.anisotropicRationalAmbientShell x RationalAdele → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ y, f (P.blockToAmbientShellHomeomorph hx RationalAdele y)
      ∂P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
        (V.nativeRationalQuadraticForm x) hx) =
      (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        ∫⁻ z, f z ∂P.anisotropicRationalAmbientShellMeasure hx := by
  calc
    (∫⁻ y, f (P.blockToAmbientShellHomeomorph hx RationalAdele y)
      ∂P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
        (V.nativeRationalQuadraticForm x) hx) =
        ∫⁻ z, f z ∂Measure.map
          (P.blockToAmbientShellHomeomorph hx RationalAdele)
          (P.lowerSpace.fullAdelicNonisotropicLastShellMeasure
            (V.nativeRationalQuadraticForm x) hx) := by
      rw [MeasureTheory.lintegral_map hf
        (P.blockToAmbientShellHomeomorph hx RationalAdele).continuous.measurable]
    _ = ∫⁻ z, f z ∂
        ((P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) •
          P.anisotropicRationalAmbientShellMeasure hx) := by
      rw [P.map_fullAdelicNonisotropicLastShellMeasure_eq_smul_ambient hx]
    _ = (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
        ∫⁻ z, f z ∂P.anisotropicRationalAmbientShellMeasure hx := by
      rw [lintegral_smul_measure]
      rfl

/-- The normalized ambient shell measure bound against the transported
ambient kernel recovers the fixed ambient horizontal Haar literally. -/
theorem anisotropicRationalAmbientShellMeasure_bind_orbitFiberKernel_eq_horizontal
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.anisotropicRationalAmbientShellMeasure hx).bind
        (P.anisotropicRationalAmbientShellOrbitFiberKernel hx) =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [anisotropicRationalAmbientShellMeasure, Measure.bind_smul]
  rw [P.map_fullAdelicNonisotropicLastShellMeasure_bind_ambientKernel_eq_smul_horizontal
    hx]
  rw [smul_smul]
  rw [ENNReal.inv_mul_cancel
    (ENNReal.coe_ne_zero.mpr
      (ne_of_gt (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx)))
    ENNReal.coe_ne_top,
    one_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
