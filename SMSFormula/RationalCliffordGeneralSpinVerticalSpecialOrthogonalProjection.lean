import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier
import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicRestrictedFamilyGroup
import SMSFormula.RationalSpecialOrthogonalAdelicSpinorNormDiagonal
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Special-orthogonal projection of vertical general-Spin fibers

Right multiplication descends to the rational adelic `SO` left quotient.
The horizontal projection of the vertical general-Spin parametrization is
exactly the corresponding right translate of the existing Spin-to-`SO`
quotient map.  This is the component formula needed to send the vertical
finite cutoff into the proper-selector presentation.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- Right multiplication by an adelic `SO` point on its rational left
quotient. -/
def fullAdelicSpecialOrthogonalLeftQuotientRightMul
    (x : V.FullAdelicSpecialOrthogonalGroup) :
    V.FullAdelicSpecialOrthogonalLeftQuotient →
      V.FullAdelicSpecialOrthogonalLeftQuotient :=
  Quot.lift
    (fun y => V.fullAdelicSpecialOrthogonalLeftQuotientMap (y * x)) (by
      intro y z hyz
      rcases hyz with ⟨gamma, rfl⟩
      change V.fullAdelicSpecialOrthogonalLeftQuotientMap (y * x) =
        V.fullAdelicSpecialOrthogonalLeftQuotientMap
          (((gamma : V.FullAdelicSpecialOrthogonalGroup) * y) * x)
      rw [mul_assoc]
      exact (leftCosetMap_gamma_mul
        V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup gamma
        (y * x)).symm)

@[simp]
theorem fullAdelicSpecialOrthogonalLeftQuotientRightMul_mk
    (x y : V.FullAdelicSpecialOrthogonalGroup) :
    V.fullAdelicSpecialOrthogonalLeftQuotientRightMul x
        (V.fullAdelicSpecialOrthogonalLeftQuotientMap y) =
      V.fullAdelicSpecialOrthogonalLeftQuotientMap (y * x) :=
  rfl

/-- Quotient right multiplication is measurable for the existing
map-generated `SO` quotient measurable structure. -/
theorem measurable_fullAdelicSpecialOrthogonalLeftQuotientRightMul
    (x : V.FullAdelicSpecialOrthogonalGroup) :
    Measurable (V.fullAdelicSpecialOrthogonalLeftQuotientRightMul x) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun y : V.FullAdelicSpecialOrthogonalGroup =>
        V.fullAdelicSpecialOrthogonalLeftQuotientMap (y * x)) :=
    V.fullAdelicSpecialOrthogonalLeftQuotientMap_measurable.comp
      (continuous_mul_right x).measurable
  simpa [fullAdelicSpecialOrthogonalLeftQuotientRightMul,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

/-- The horizontal general-Spin quotient map commutes with right
translation. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_rightMul
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) =
      V.fullAdelicSpecialOrthogonalLeftQuotientRightMul
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)
        (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal z) := by
  induction z using Quot.inductionOn with
  | _ y =>
    change V.fullAdelicSpecialOrthogonalLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom (y * x)) =
      V.fullAdelicSpecialOrthogonalLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom y *
          V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)
    rw [map_mul]

end RationalQuadraticSpaceMatrix
