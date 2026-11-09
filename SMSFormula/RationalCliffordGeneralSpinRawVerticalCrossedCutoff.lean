import SMSFormula.RationalCliffordGeneralSpinAdelicRightTranslation
import SMSFormula.RationalIdeleClassHaarMeasure

/-!
# The raw vertical crossed cutoff

Choose a full-adelic intrinsic general-Spin representative over each rational
idele class.  Right translation of the neutral raw Spin quotient pushforward
then gives a measure supported on the corresponding vertical fiber of

```text
GSpin(Q)\GSpin(A) -> Q^x\A^x.
```

Every translated fiber has the raw Spin mass.  Its logarithmic
cutoff is the cutoff value at the base idele class times that mass.  Integrating
over the fixed idele-class Haar measure therefore evaluates the vertical
crossed integral as the common idele cutoff times `tau_raw(Spin)`.

No measure on the whole general-Spin quotient and no comparison with the
singular raw `SO` measure is introduced.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- A chosen general-Spin quotient point over an idele class. -/
noncomputable def verticalGeneralSpinQuotientLift
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Classical.choose (hsurj c)

@[simp]
theorem verticalGeneralSpinQuotientLift_spec
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.verticalGeneralSpinQuotientLift hsurj c) = c :=
  Classical.choose_spec (hsurj c)

/-- A chosen full-adelic representative of the quotient lift. -/
noncomputable def verticalGeneralSpinRepresentative
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  Quot.out (V.verticalGeneralSpinQuotientLift hsurj c)

theorem verticalGeneralSpinRepresentative_quotient
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.verticalGeneralSpinRepresentative hsurj c) =
      V.verticalGeneralSpinQuotientLift hsurj c :=
  Quot.out_eq _

theorem verticalGeneralSpinRepresentative_ideleClass
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (V.verticalGeneralSpinRepresentative hsurj c)) = c := by
  rw [← V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk,
    V.verticalGeneralSpinRepresentative_quotient,
    V.verticalGeneralSpinQuotientLift_spec]

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The translated raw Spin quotient measure on the vertical fiber over `c`.
-/
noncomputable def verticalSpinFiberMeasure
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.map
    (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.verticalGeneralSpinRepresentative hsurj c))
    (spinGeneralSpinQuotientPushforwardMeasure V D)

@[simp]
theorem verticalSpinFiberMeasure_univ
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    D.verticalSpinFiberMeasure V hsurj c Set.univ =
      D.spinTamagawaNumberENNReal := by
  rw [verticalSpinFiberMeasure,
    Measure.map_apply_of_aemeasurable
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.verticalGeneralSpinRepresentative hsurj c)).aemeasurable
      MeasurableSet.univ]
  simp

/-- The translated Spin measure vanishes on every measurable set disjoint
from its literal idele-class fiber. -/
theorem verticalSpinFiberMeasure_apply_eq_zero_of_disjoint_fiber
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup)
    {s : Set V.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s)
    (hdisj : Disjoint s
      {z | V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass z = c}) :
    D.verticalSpinFiberMeasure V hsurj c s = 0 := by
  rw [verticalSpinFiberMeasure,
    Measure.map_apply_of_aemeasurable
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.verticalGeneralSpinRepresentative hsurj c)).aemeasurable hs]
  rw [spinGeneralSpinQuotientPushforwardMeasure]
  apply V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward_apply_eq_zero_of_disjoint_range
    D.spinData.quotientMeasure
    (hs.preimage
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.verticalGeneralSpinRepresentative hsurj c)))
  apply Set.disjoint_left.2
  intro z hz hzrange
  rcases hzrange with ⟨u, rfl⟩
  apply Set.disjoint_left.1 hdisj hz
  change V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.verticalGeneralSpinRepresentative hsurj c)
        (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin u)) = c
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul]
  have hneutral :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
          (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin u) = 1 := by
    induction u using Quot.inductionOn with
    | _ x =>
      exact V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_neutral x
  rw [hneutral]
  exact (one_mul _).trans
    (V.verticalGeneralSpinRepresentative_ideleClass hsurj c)

/-- The logarithmic cutoff on one translated vertical Spin fiber. -/
noncomputable def verticalSpinFiberLogCutoffLIntegral
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
    ∂D.verticalSpinFiberMeasure V hsurj c

/-- A vertical fiber cutoff is its base idele-class value times the literal
raw Spin quotient mass. -/
theorem verticalSpinFiberLogCutoffLIntegral_eq
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    D.verticalSpinFiberLogCutoffLIntegral V hsurj c f =
      f (rationalIdeleClassLogModule c) *
        D.spinTamagawaNumberENNReal := by
  rw [verticalSpinFiberLogCutoffLIntegral, verticalSpinFiberMeasure]
  change (∫⁻ z,
      (f ∘ V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule) z
        ∂Measure.map
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
            (V.verticalGeneralSpinRepresentative hsurj c))
          (spinGeneralSpinQuotientPushforwardMeasure V D)) = _
  rw [lintegral_map'
    (hf.comp
      V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable).aemeasurable
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.verticalGeneralSpinRepresentative hsurj c)).aemeasurable]
  let t := rationalIdeleClassLogModule c
  let g := fun u : ℝ => f (u + t)
  have hg : Measurable g := by
    exact hf.comp (measurable_id.add measurable_const)
  have hrepLog :
      rationalIdeleLogModule
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom
            (V.verticalGeneralSpinRepresentative hsurj c)) = t := by
    change rationalIdeleClassLogModule
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinSimilitudeHom
            (V.verticalGeneralSpinRepresentative hsurj c))) = _
    rw [V.verticalGeneralSpinRepresentative_ideleClass]
  calc
    (∫⁻ z,
      (f ∘ V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule)
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (V.verticalGeneralSpinRepresentative hsurj c) z)
        ∂spinGeneralSpinQuotientPushforwardMeasure V D) =
        ∫⁻ z, g
          (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
          ∂spinGeneralSpinQuotientPushforwardMeasure V D := by
      apply lintegral_congr
      intro z
      change f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
            (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
              (V.verticalGeneralSpinRepresentative hsurj c) z)) = _
      rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_rightMul,
        hrepLog]
    _ = g 0 * D.spinTamagawaNumberENNReal :=
      D.lintegral_spinGeneralSpinQuotientPushforward_logCutoff V g hg
    _ = f (rationalIdeleClassLogModule c) *
        D.spinTamagawaNumberENNReal := by simp [g, t]

/-- The vertical crossed integral over all rational idele classes. -/
noncomputable def verticalCrossedLogCutoffLIntegral
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : RationalIdeleClassGroup,
    D.verticalSpinFiberLogCutoffLIntegral V hsurj c f
      ∂rationalIdeleClassHaarMeasure

/-- The vertical crossed integral is the common idele-class cutoff times the
actual raw Spin quotient mass. -/
theorem verticalCrossedLogCutoffLIntegral_eq
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    D.verticalCrossedLogCutoffLIntegral V hsurj f =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  rw [verticalCrossedLogCutoffLIntegral]
  simp_rw [D.verticalSpinFiberLogCutoffLIntegral_eq V hsurj _ f hf]
  change (∫⁻ c : RationalIdeleClassGroup,
      (f ∘ rationalIdeleClassLogModule) c * D.spinTamagawaNumberENNReal
        ∂rationalIdeleClassHaarMeasure) = _
  rw [lintegral_mul_const _
    (hf.comp continuous_rationalIdeleClassLogModule.measurable)]
  rfl

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
