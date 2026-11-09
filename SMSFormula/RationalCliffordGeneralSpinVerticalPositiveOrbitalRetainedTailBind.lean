import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedCylinderReconstruction

/-!
# Absorb the retained Spin tail into the horizontal SO-tail bind

The retained vertical cylinder displays a normalized integral Spin-tail
coordinate.  It must not be pushed directly to the integral `SO` tail: that
pushforward is the singular Spin-image measure.  Instead, first bind the
`SO`-indexed central-fiber kernel to normalized `SO` Haar.  This gives
the normalized horizontal `GSpin` tail.  Left invariance then absorbs every
embedded Spin-tail action, and probability normalization removes the outer
Spin integral with coefficient one.

This is the nonnegative-integral identity needed for the cylinder
reassociation.  It uses neither a section nor a Cartesian presentation of
the good tail.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance retainedTailBindDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedTailBindPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The normalized retained Spin tail, embedded componentwise as an element
of the existing horizontal integral `GSpin` tail. -/
def retainedIntegralSpinTailElement
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B →
      V.CliffordGeneralSpinHorizontalIntegralTail E :=
  fun u v => L.retainedIntegralSpinTailAction S u v

theorem measurable_retainedIntegralSpinTailElement
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.retainedIntegralSpinTailElement S) := by
  unfold retainedIntegralSpinTailElement
  exact measurable_pi_lambda _ fun v => L.measurable_retainedIntegralSpinTailAction S v

@[simp]
theorem retainedIntegralSpinTailElement_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :
    L.retainedIntegralSpinTailElement S u v =
      L.retainedIntegralSpinTailAction S u v := by
  rfl

/-- Binding the genuine central-fiber kernel over normalized integral `SO`
Haar and then averaging every retained Spin-tail left translation gives the
same normalized horizontal `GSpin` tail.  No direct Spin-to-`SO` pushforward
is used. -/
theorem lintegral_retainedIntegralSpinTail_centralFiberBind
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let μSpin :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
    let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
    let kappa := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
    (∫⁻ u, ∫⁻ q, ∫⁻ g,
        f (L.retainedIntegralSpinTailElement S u * g) ∂kappa q ∂μSO ∂μSpin) =
      ∫⁻ g, f g ∂μG := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let kappa := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  let μG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  letI : IsProbabilityMeasure μSpin :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability B
  have hbind : kappa ∘ₘ μSO = μG :=
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  calc
    (∫⁻ u, ∫⁻ q, ∫⁻ g,
        f (L.retainedIntegralSpinTailElement S u * g) ∂kappa q ∂μSO ∂μSpin) =
        ∫⁻ u, ∫⁻ g,
          f (L.retainedIntegralSpinTailElement S u * g) ∂(kappa ∘ₘ μSO) ∂μSpin := by
      apply lintegral_congr
      intro u
      simpa only [Function.comp_apply] using
        (Measure.lintegral_bind (m := μSO) (μ := kappa) kappa.aemeasurable
          ((hf.comp (measurable_const_mul
            (L.retainedIntegralSpinTailElement S u))).aemeasurable)).symm
    _ = ∫⁻ u, ∫⁻ g,
          f (L.retainedIntegralSpinTailElement S u * g) ∂μG ∂μSpin := by
      rw [hbind]
    _ = ∫⁻ u, ∫⁻ g, f g ∂μG ∂μSpin := by
      apply lintegral_congr
      intro u
      exact lintegral_mul_left_eq_self f (L.retainedIntegralSpinTailElement S u)
    _ = ∫⁻ g, f g ∂μG := by simp [μSpin]

end PositiveDefiniteIntegralLattice

end
