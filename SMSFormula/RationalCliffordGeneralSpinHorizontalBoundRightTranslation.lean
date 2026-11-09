import SMSFormula.RationalCliffordGeneralSpinHorizontalFiberRightTranslation
import SMSFormula.RationalCliffordGeneralSpinLatticeSpecialOrthogonalRightTranslation

/-!
# Right invariance of the concrete horizontal quotient bind

For the literal lattice raw `SO` datum, the rational-carrier quotient measure
is invariant under adelic right translation.  Combining this with the exact
equivariance of the descended idele-class fiber kernel proves that the
concrete horizontal bound measure on `GSpin(Q)\\GSpin(A)` is invariant under
every genuine adelic `GSpin` right translation.

This closes a necessary homogeneous-space compatibility condition for the
remaining normalization comparison.  It does not invoke uniqueness of
invariant measures on a nonnormal quotient and does not compute the still
independent idele-class Haar scalar.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The literal raw-`SO` horizontal fiber-Haar bind is invariant under every
genuine adelic `GSpin` right translation. -/
theorem map_horizontalRawSOFiberHaarBoundMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          x)
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv)) =
      L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv) := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L hn inst hP hconv
  let R := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
  let B := V.fullAdelicSpecialOrthogonalLeftQuotientRightMul
    (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs]
  rw [horizontalRawSOFiberHaarBoundMeasure,
    horizontalSOFiberHaarBoundMeasure_apply _ _ _
      ((V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs),
    horizontalSOFiberHaarBoundMeasure_apply _ _ _ hs]
  have hfiber (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
      L.horizontalFiberHaarKernelAtSO inst q (R ⁻¹' s) =
        L.horizontalFiberHaarKernelAtSO inst (B q) s := by
    have heq := L.map_horizontalFiberHaarKernelAtSO_rightMul inst x q
    have happ := congrArg (fun μ : Measure
        V.FullAdelicCliffordGeneralSpinLeftQuotient => μ s) heq
    change (Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (L.horizontalFiberHaarKernelAtSO inst q)) s =
      (L.horizontalFiberHaarKernelAtSO inst
        (V.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) q)) s at happ
    rw [Measure.map_apply
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs]
      at happ
    simpa only [R, B] using happ
  change (∫⁻ q, L.horizontalFiberHaarKernelAtSO inst q (R ⁻¹' s)
      ∂D.specialOrthogonalData.quotientMeasure) =
    ∫⁻ q, L.horizontalFiberHaarKernelAtSO inst q s
      ∂D.specialOrthogonalData.quotientMeasure
  simp_rw [hfiber]
  have hmeas : Measurable
      (fun q : V.FullAdelicSpecialOrthogonalLeftQuotient =>
        L.horizontalFiberHaarKernelAtSO inst q s) :=
    (L.horizontalFiberHaarKernelAtSO inst).measurable_coe hs
  rw [← lintegral_map' hmeas.aemeasurable
    (V.measurable_fullAdelicSpecialOrthogonalLeftQuotientRightMul
      (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)).aemeasurable]
  rw [L.map_latticeRawSpecialOrthogonalQuotientMeasure_rightMul
    hn inst hP hconv]

end PositiveDefiniteIntegralLattice
