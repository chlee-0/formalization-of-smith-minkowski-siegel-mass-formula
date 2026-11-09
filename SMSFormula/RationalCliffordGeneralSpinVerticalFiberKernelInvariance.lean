import SMSFormula.RationalCliffordGeneralSpinVerticalFiberKernel
import SMSFormula.RationalCliffordGeneralSpinVerticalParametrization
import SMSFormula.RationalCliffordSpinCandidateGeneralSpinConjugationMeasure

/-!
# Representative invariance of the vertical Spin source kernel

The neutral raw Spin quotient pushforward on the rational adelic `GSpin`
quotient is invariant under right multiplication by a rational `GSpin`
diagonal.  This is obtained by transporting the exact raw Spin quotient
conjugation theorem through the literal Spin-to-`GSpin` quotient map.  Its
existing Spin right invariance is transported in the same way.

Consequently the measurable ambient-source vertical kernel is constant under
left multiplication of its ambient origin by a rational `GSpin` diagonal and
an adelic Spin point.  This is the exact representative-independence input for
descent to rational idele classes.  No quotient descent, section, measure bind,
or new scalar is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-- Spin quotient right translation commutes with inclusion into the rational
adelic `GSpin` quotient. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_rightMul
    (s : V.FullAdelicCliffordSpinCandidateGroup)
    (q : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
        (V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul s q) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s)
        (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q) := by
  induction q using Quot.inductionOn with
  | _ x =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom (x * s)) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x *
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s)
    rw [map_mul]

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The neutral raw Spin quotient pushforward is fixed by every rational
`GSpin` diagonal right translation. -/
theorem map_spinGeneralSpinQuotientPushforwardMeasure_rightMul_rationalDiagonal
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma))
        (spinGeneralSpinQuotientPushforwardMeasure V D) =
      spinGeneralSpinQuotientPushforwardMeasure V D := by
  let J := V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
  let C :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma
  let R := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
  have hJ : Measurable J :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_measurable
  have hC : Measurable C :=
    V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma
  have hR : Measurable R :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
  have hcomm : R ∘ J = J ∘ C := by
    funext q
    exact
      (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_conjugation
        gamma q).symm
  unfold spinGeneralSpinQuotientPushforwardMeasure
  unfold fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward
  change Measure.map R (Measure.map J D.spinData.quotientMeasure) =
    Measure.map J D.spinData.quotientMeasure
  rw [Measure.map_map hR hJ, hcomm]
  rw [← Measure.map_map hJ hC]
  rw [map_spin_quotientMeasure_rationalGeneralSpinConjugation
    (V := V) D gamma]

/-- The neutral raw Spin quotient pushforward is fixed by right translation
through every adelic Spin point. -/
theorem map_spinGeneralSpinQuotientPushforwardMeasure_rightMul_spin
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (s : V.FullAdelicCliffordSpinCandidateGroup) :
    Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s))
        (spinGeneralSpinQuotientPushforwardMeasure V D) =
      spinGeneralSpinQuotientPushforwardMeasure V D := by
  let J := V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
  let S := V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul s
  let R := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s)
  have hJ : Measurable J :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_measurable
  have hS : Measurable S :=
    V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRightMul s
  have hR : Measurable R :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s)
  have hcomm : R ∘ J = J ∘ S := by
    funext q
    exact
      (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_rightMul
        s q).symm
  unfold spinGeneralSpinQuotientPushforwardMeasure
  unfold fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward
  change Measure.map R (Measure.map J D.spinData.quotientMeasure) =
    Measure.map J D.spinData.quotientMeasure
  rw [Measure.map_map hR hJ, hcomm]
  rw [← Measure.map_map hJ hS]
  rw [D.map_spin_quotientMeasure_rightMul s]

/-- Left multiplication of the ambient origin by a rational `GSpin` diagonal
does not change the translated vertical Spin kernel value. -/
theorem verticalSpinFiberKernelAtAmbient_rationalDiagonal_mul
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberKernelAtAmbient (V := V)
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma * g) =
      D.verticalSpinFiberKernelAtAmbient (V := V) g := by
  rw [D.verticalSpinFiberKernelAtAmbient_apply,
    D.verticalSpinFiberKernelAtAmbient_apply]
  let Rgamma := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
  let Rg := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g
  have hRgamma : Measurable Rgamma :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul _
  have hRg : Measurable Rg :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul _
  have hcomp :
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma * g) =
        Rg ∘ Rgamma := by
    funext z
    exact
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) g z).symm
  rw [hcomp, ← Measure.map_map hRg hRgamma]
  rw [D.map_spinGeneralSpinQuotientPushforwardMeasure_rightMul_rationalDiagonal
    gamma]

/-- Left multiplication of the ambient origin by an adelic Spin point does
not change the translated vertical Spin kernel value. -/
theorem verticalSpinFiberKernelAtAmbient_spin_mul
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (s : V.FullAdelicCliffordSpinCandidateGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberKernelAtAmbient (V := V)
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * g) =
      D.verticalSpinFiberKernelAtAmbient (V := V) g := by
  rw [D.verticalSpinFiberKernelAtAmbient_apply,
    D.verticalSpinFiberKernelAtAmbient_apply]
  let Rs := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
    (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s)
  let Rg := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g
  have hRs : Measurable Rs :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul _
  have hRg : Measurable Rg :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul _
  have hcomp :
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * g) =
        Rg ∘ Rs := by
    funext z
    exact
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s) g z).symm
  rw [hcomp, ← Measure.map_map hRg hRs]
  rw [D.map_spinGeneralSpinQuotientPushforwardMeasure_rightMul_spin s]

/-- The exact representative-change identity for the ambient vertical kernel:
a rational `GSpin` diagonal and an adelic Spin factor on the left of an origin
do not change its value. -/
theorem verticalSpinFiberKernelAtAmbient_rationalDiagonal_spin_mul
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (s : V.FullAdelicCliffordSpinCandidateGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberKernelAtAmbient (V := V)
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma *
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * g) =
      D.verticalSpinFiberKernelAtAmbient (V := V) g := by
  rw [mul_assoc, D.verticalSpinFiberKernelAtAmbient_rationalDiagonal_mul,
    D.verticalSpinFiberKernelAtAmbient_spin_mul]

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
