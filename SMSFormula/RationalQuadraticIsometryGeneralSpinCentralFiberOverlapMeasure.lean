import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberOverlap
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarFactorization

/-!
# Fixed real Haar measures on the presentation chart overlap

The transported block identity chart and the independently chosen ambient
identity chart have an exact common open group source.  This file restricts
the two fixed real horizontal Haar measures to that source and proves
that they differ there by the presentation Haar scalar.

The scalar is not evaluated in this file.  In particular, it is not
identified with the rational tangent determinant, and the two independently
chosen chart domains are not asserted equal.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The transported block Haar measure restricted intrinsically to the exact
common group source of the transported and ambient identity charts. -/
def transportedRealCentralFiberOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientRealCentralFiberSourceOverlap hx) :=
  Measure.comap Subtype.val
    (Measure.map
      (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure))

/-- The fixed ambient Haar measure restricted intrinsically to the exact
common group source of the transported and ambient identity charts. -/
def ambientRealCentralFiberOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientRealCentralFiberSourceOverlap hx) :=
  Measure.comap Subtype.val
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure

/-- The intrinsic transported overlap measure maps back to the literal
restriction of the transported block Haar on the ambient group carrier. -/
theorem map_transportedRealCentralFiberOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.transportedRealCentralFiberOverlapHaarMeasure hx) =
      (Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)).restrict
        (P.transportedAmbientRealCentralFiberSourceOverlap hx) := by
  rw [transportedRealCentralFiberOverlapHaarMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet _

/-- The intrinsic ambient overlap measure maps back to the literal restriction
of the fixed ambient Haar on the ambient group carrier. -/
theorem map_ambientRealCentralFiberOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.ambientRealCentralFiberOverlapHaarMeasure hx) =
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
        (P.transportedAmbientRealCentralFiberSourceOverlap hx) := by
  rw [ambientRealCentralFiberOverlapHaarMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet _

/-- On the exact common identity-chart source, the two fixed real group Haar
measures differ by precisely the already named presentation scalar. -/
theorem transportedRealCentralFiberOverlapHaarMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedRealCentralFiberOverlapHaarMeasure hx =
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx •
        P.ambientRealCentralFiberOverlapHaarMeasure hx := by
  rw [transportedRealCentralFiberOverlapHaarMeasure,
    ambientRealCentralFiberOverlapHaarMeasure,
    P.map_blockToAmbientRealGeneralSpinHorizontalMeasure_eq_smul hx,
    ENNReal.smul_def, ENNReal.smul_def,
    Measure.comap_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
