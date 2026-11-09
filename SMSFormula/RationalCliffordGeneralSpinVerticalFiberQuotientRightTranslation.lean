import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientBind

/-!
# Right translation of the vertical Spin quotient bind

Right multiplication on the rational adelic `GSpin` quotient sends the
translated neutral Spin measure through an ambient origin `g` to the one
through `g * x`.  After the exact idele-class descent, the base coordinate is
translated by the rational idele class of the similitude of `x`.

The independently selected rational idele-class Haar is right invariant, so
binding the equivariant fibers against it produces a right-invariant measure
on the actual rational `GSpin` quotient.  This is only the homogeneous-space
invariance needed for the later periodized-Haar comparison; no uniqueness on
the nonnormal quotient or scalar value is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- Ambient right multiplication carries the vertical kernel through `g` to
the kernel through `g * x`. -/
theorem map_verticalSpinFiberKernelAtAmbient_rightMul
    {V : RationalQuadraticSpaceMatrix n}
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (g x : V.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (D.verticalSpinFiberKernelAtAmbient (V := V) g) =
      D.verticalSpinFiberKernelAtAmbient (V := V) (g * x) := by
  rw [D.verticalSpinFiberKernelAtAmbient_apply,
    D.verticalSpinFiberKernelAtAmbient_apply,
    Measure.map_map
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul g)]
  apply congrArg
    (fun f : V.FullAdelicCliffordGeneralSpinLeftQuotient →
        V.FullAdelicCliffordGeneralSpinLeftQuotient =>
      Measure.map f (spinGeneralSpinQuotientPushforwardMeasure V D))
  funext z
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul g x z

/-- The descended idele-class-indexed kernel is equivariant for simultaneous
right translation on its base and on the rational `GSpin` quotient. -/
theorem map_verticalSpinFiberKernelAtIdeleClass_rightMul
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (c : RationalIdeleClassGroup) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          x)
        (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c) =
      D.verticalSpinFiberKernelAtIdeleClass L hn hsurj
        (c * QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
            x)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let g := V.verticalGeneralSpinRepresentative hsurj c
  have hgclass :
      QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom g) = c :=
    V.verticalGeneralSpinRepresentative_ideleClass hsurj c
  calc
    Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c) =
      Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (D.verticalSpinFiberKernelAtAmbient (V := V) g) := by
          rw [← hgclass]
          rw [D.verticalSpinFiberKernelAtIdeleClass_ambient_projection
            L hn hsurj g]
    _ = D.verticalSpinFiberKernelAtAmbient (V := V) (g * x) :=
      D.map_verticalSpinFiberKernelAtAmbient_rightMul g x
    _ = D.verticalSpinFiberKernelAtIdeleClass L hn hsurj
        (c * QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)) := by
      rw [← D.verticalSpinFiberKernelAtIdeleClass_ambient_projection
        L hn hsurj (g * x)]
      congr 1
      change
        QuotientGroup.mk'
            RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom g *
              V.fullAdelicCliffordGeneralSpinSimilitudeHom x) = _
      rw [map_mul
        (QuotientGroup.mk'
          RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup), hgclass]

/-- The class-Haar bind of the translated vertical Spin fibers is invariant
under every genuine adelic `GSpin` right translation. -/
theorem map_verticalSpinFiberHaarBoundMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          x)
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
      D.verticalSpinFiberHaarBoundMeasure L hn hsurj := by
  let V := L.rationalQuadraticSpaceMatrix
  let R := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
  let d : RationalIdeleClassGroup :=
    QuotientGroup.mk' RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
      (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs]
  rw [D.verticalSpinFiberHaarBoundMeasure_apply L hn hsurj
      ((V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs),
    D.verticalSpinFiberHaarBoundMeasure_apply L hn hsurj hs]
  have hfiber (c : RationalIdeleClassGroup) :
      D.verticalSpinFiberMeasure V hsurj c (R ⁻¹' s) =
        D.verticalSpinFiberMeasure V hsurj (c * d) s := by
    have heq := D.map_verticalSpinFiberKernelAtIdeleClass_rightMul
      L hn hsurj x c
    have happ := congrArg
      (fun μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient => μ s) heq
    change (Measure.map R
        (D.verticalSpinFiberMeasure V hsurj c)) s =
      D.verticalSpinFiberMeasure V hsurj (c * d) s at happ
    rw [Measure.map_apply
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hs]
      at happ
    exact happ
  change (∫⁻ c : RationalIdeleClassGroup,
      D.verticalSpinFiberMeasure V hsurj c (R ⁻¹' s)
        ∂rationalIdeleClassHaarMeasure) =
    ∫⁻ c : RationalIdeleClassGroup,
      D.verticalSpinFiberMeasure V hsurj c s
        ∂rationalIdeleClassHaarMeasure
  simp_rw [hfiber]
  have hmeas : Measurable
      (fun c : RationalIdeleClassGroup =>
        D.verticalSpinFiberMeasure V hsurj c s) :=
    (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj).measurable_coe hs
  rw [← lintegral_map' hmeas.aemeasurable
    (measurable_mul_const d).aemeasurable]
  have hright : Measure.map (fun c : RationalIdeleClassGroup => c * d)
      rationalIdeleClassHaarMeasure = rationalIdeleClassHaarMeasure := by
    calc
      Measure.map (fun c : RationalIdeleClassGroup => c * d)
          rationalIdeleClassHaarMeasure =
        Measure.map (fun c : RationalIdeleClassGroup => d * c)
          rationalIdeleClassHaarMeasure := by
            apply Measure.map_congr
            filter_upwards [] with c
            exact mul_comm c d
      _ = rationalIdeleClassHaarMeasure :=
        Measure.IsMulLeftInvariant.map_mul_left_eq_self d
  rw [hright]

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
