import SMSFormula.RationalCliffordGeneralSpinHorizontalFiberLogCutoff

/-!
# The raw horizontal crossed cutoff

For a surjective horizontal map
`GSpin(Q)\GSpin(A) -> SO(Q)\SO(A)`, choose one lift of each `SO` quotient
point and integrate the genuine idele-class Haar cutoff on its horizontal
torsor against the existing raw `SO` quotient measure.

The preceding Haar-translation theorem makes the fiber integral constant,
so the choice disappears and the resulting iterated integral is literally
the identity-fiber cutoff times the raw `SO` Tamagawa number.  This packages
the horizontal side of the crossed comparison without asserting a measure or
disintegration theorem on the whole general-Spin quotient.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- A chosen general-Spin lift of an `SO` quotient point, under the exact
surjectivity hypothesis consumed by the horizontal crossed integral. -/
noncomputable def horizontalGeneralSpinLift
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Classical.choose (hsurj q)

@[simp]
theorem horizontalGeneralSpinLift_spec
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.horizontalGeneralSpinLift hsurj q) = q :=
  Classical.choose_spec (hsurj q)

/-- The actual horizontal fiber cutoff, viewed as a function of the raw `SO`
quotient point through any chosen lift. -/
noncomputable def horizontalFiberLogCutoffAtSO
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (f : ℝ → ℝ≥0∞)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) : ℝ≥0∞ :=
  V.horizontalFiberLogCutoffLIntegral
    (V.horizontalGeneralSpinLift hsurj q) f

/-- For a measurable cutoff, the horizontal fiber integral is the same
constant at every `SO` quotient point. -/
theorem horizontalFiberLogCutoffAtSO_eq_identity
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (q : V.FullAdelicSpecialOrthogonalLeftQuotient) :
    V.horizontalFiberLogCutoffAtSO hsurj f q =
      V.horizontalFiberLogCutoffLIntegral
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f :=
  V.horizontalFiberLogCutoffLIntegral_eq_one_forall
    (V.horizontalGeneralSpinLift hsurj q) f hf

theorem measurable_horizontalFiberLogCutoffAtSO
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (V.horizontalFiberLogCutoffAtSO hsurj f) := by
  rw [show V.horizontalFiberLogCutoffAtSO hsurj f =
      fun _q => V.horizontalFiberLogCutoffLIntegral
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f by
    funext q
    exact V.horizontalFiberLogCutoffAtSO_eq_identity hsurj f hf q]
  exact measurable_const

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The horizontal iterated crossed integral against the literal raw `SO`
quotient measure. -/
noncomputable def horizontalCrossedLogCutoffLIntegral
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ q, V.horizontalFiberLogCutoffAtSO hsurj f q
    ∂D.specialOrthogonalData.quotientMeasure

/-- The horizontal crossed integral is the common identity-fiber cutoff
times the actual raw `SO` quotient mass. -/
theorem horizontalCrossedLogCutoffLIntegral_eq
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    D.horizontalCrossedLogCutoffLIntegral V hsurj f =
      V.horizontalFiberLogCutoffLIntegral
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f *
        D.specialOrthogonalData.tamagawaNumberENNReal := by
  rw [horizontalCrossedLogCutoffLIntegral]
  have hfun : V.horizontalFiberLogCutoffAtSO hsurj f =
      fun _q => V.horizontalFiberLogCutoffLIntegral
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f := by
    funext q
    exact V.horizontalFiberLogCutoffAtSO_eq_identity hsurj f hf q
  rw [hfun, lintegral_const]
  rfl

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix

