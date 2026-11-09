import SMSFormula.RationalCliffordGeneralSpinHorizontalFiberHaarMeasure

/-!
# Logarithmic cutoffs on horizontal general-Spin fibers

The descended general-Spin similitude on a central idele-class translate is
the square of the translating class times the original similitude.  Hence its
logarithmic coordinate is translated by twice the idele-class logarithm.

Pushing the fixed Haar measure through the actual orbit map evaluates a
nonnegative measurable cutoff on an explicit horizontal fiber as the literal
idele-class Haar integral of this translated doubled logarithm.  This is the
horizontal fiber formula needed before the crossed Weil comparison; it does
not postulate a measure on the whole general-Spin quotient.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The descended similitude on a central translate is the square of the
idele class times the original descended similitude. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_scalarAction
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) =
      c ^ 2 * V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass z := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    induction z using Quot.inductionOn with
    | _ x =>
      change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x)) =
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) ^ 2 *
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)
      rw [map_mul]
      change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
          (a ^ 2 * V.fullAdelicCliffordGeneralSpinSimilitudeHom x) = _
      rw [map_mul, map_pow]

/-- The logarithmic coordinate on a central translate is shifted by twice
the idele-class logarithm. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_scalarAction
    (c : RationalIdeleClassGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
          c z) =
      2 * rationalIdeleClassLogModule c +
        V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z := by
  rw [fullAdelicCliffordGeneralSpinLeftQuotientLogModule,
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_scalarAction,
    rationalIdeleClassLogModule_mul,
    rationalIdeleClassLogModule_sq]
  rfl

/-- The logarithmic cutoff integral on the actual horizontal torsor through
`z`. -/
noncomputable def horizontalFiberLogCutoffLIntegral
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ w, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule w)
    ∂V.horizontalFiberHaarMeasure z

/-- Horizontal fiber integration is the literal idele-class Haar integral
of the shifted doubled logarithmic coordinate. -/
theorem horizontalFiberLogCutoffLIntegral_eq
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    V.horizontalFiberLogCutoffLIntegral z f =
      ∫⁻ c : RationalIdeleClassGroup,
        f (2 * rationalIdeleClassLogModule c +
          V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
          ∂rationalIdeleClassHaarMeasure := by
  rw [horizontalFiberLogCutoffLIntegral, horizontalFiberHaarMeasure]
  change (∫⁻ w,
      (f ∘ V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule) w
        ∂Measure.map
          (fun c : RationalIdeleClassGroup =>
            V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
              c z)
          rationalIdeleClassHaarMeasure) = _
  rw [lintegral_map'
    (hf.comp
      V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable).aemeasurable
    (V.measurable_rationalIdeleClassOrbitMap z).aemeasurable]
  apply lintegral_congr
  intro c
  change f
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
      (V.rationalIdeleClassActionOnFullAdelicCliffordGeneralSpinLeftQuotient
        c z)) = _
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_scalarAction]

/-- The fiber cutoff is independent of the chosen origin in a fixed
horizontal `SO` fiber. -/
theorem horizontalFiberLogCutoffLIntegral_eq_of_sameSO
    {z w : V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (f : ℝ → ℝ≥0∞)
    (hzw :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal w =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z) :
    V.horizontalFiberLogCutoffLIntegral w f =
      V.horizontalFiberLogCutoffLIntegral z f := by
  unfold horizontalFiberLogCutoffLIntegral
  rw [V.horizontalFiberHaarMeasure_eq_of_sameSO hzw]

/-- At the identity horizontal fiber, the cutoff sees exactly the doubled
idele-class logarithm. -/
theorem horizontalFiberLogCutoffLIntegral_one
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    V.horizontalFiberLogCutoffLIntegral
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f =
      ∫⁻ c : RationalIdeleClassGroup,
        f (2 * rationalIdeleClassLogModule c)
          ∂rationalIdeleClassHaarMeasure := by
  rw [V.horizontalFiberLogCutoffLIntegral_eq _ f hf]
  have hzero :
      V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) = 0 := by
    rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_mk]
    rw [map_one]
    simp [rationalIdeleLogModule, rationalIdeleModuleNNReal_one]
  rw [hzero]
  simp only [add_zero]

/-- Haar translation by the logarithmic half-section removes an arbitrary
additive offset from a doubled logarithmic cutoff. -/
theorem rationalIdeleClassHaar_lintegral_two_log_add
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (t : ℝ) :
    (∫⁻ c : RationalIdeleClassGroup,
      f (2 * rationalIdeleClassLogModule c + t)
        ∂rationalIdeleClassHaarMeasure) =
      ∫⁻ c : RationalIdeleClassGroup,
        f (2 * rationalIdeleClassLogModule c)
          ∂rationalIdeleClassHaarMeasure := by
  let d : RationalIdeleClassGroup := rationalIdeleClassLogSection (t / 2)
  let leftMul := fun c : RationalIdeleClassGroup => d * c
  let g := fun c : RationalIdeleClassGroup =>
    f (2 * rationalIdeleClassLogModule c)
  have hleft : Measurable leftMul := by
    simpa [leftMul] using
      ((continuous_const : Continuous
          (fun _ : RationalIdeleClassGroup => d)).mul
        (continuous_id : Continuous
          (fun c : RationalIdeleClassGroup => c))).measurable
  have hlog : Measurable rationalIdeleClassLogModule :=
    continuous_rationalIdeleClassLogModule.measurable
  have hg : Measurable g := by
    have htwo : Measurable (fun c : RationalIdeleClassGroup =>
        (2 : ℝ) * rationalIdeleClassLogModule c) :=
      measurable_const.mul hlog
    exact hf.comp htwo
  have hpoint :
      (fun c : RationalIdeleClassGroup =>
        f (2 * rationalIdeleClassLogModule c + t)) = g ∘ leftMul := by
    funext c
    simp only [g, leftMul, Function.comp_apply,
      rationalIdeleClassLogModule_mul]
    rw [show rationalIdeleClassLogModule d = t / 2 by
      exact rationalIdeleClassLogModule_logSection (t / 2)]
    congr 1
    ring
  rw [hpoint]
  change (∫⁻ c : RationalIdeleClassGroup, g (leftMul c)
      ∂rationalIdeleClassHaarMeasure) =
    ∫⁻ c : RationalIdeleClassGroup, g c
      ∂rationalIdeleClassHaarMeasure
  rw [← lintegral_map' hg.aemeasurable hleft.aemeasurable]
  rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self d]

/-- Every horizontal torsor has the same logarithmic cutoff integral as the
identity torsor.  The proof uses only the genuine fiber Haar measure and its
logarithmic half-section translation. -/
theorem horizontalFiberLogCutoffLIntegral_eq_one_forall
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    V.horizontalFiberLogCutoffLIntegral z f =
      V.horizontalFiberLogCutoffLIntegral
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f := by
  rw [V.horizontalFiberLogCutoffLIntegral_eq z f hf,
    V.horizontalFiberLogCutoffLIntegral_one f hf]
  exact rationalIdeleClassHaar_lintegral_two_log_add f hf
    (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)

end RationalQuadraticSpaceMatrix
