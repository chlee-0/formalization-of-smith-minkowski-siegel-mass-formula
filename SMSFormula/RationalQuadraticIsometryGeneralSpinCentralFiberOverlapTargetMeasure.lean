import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberOverlapMeasure

/-!
# Fixed Haar measures in the central-fiber overlap coordinates

The common group source of the transported block and ambient central-fiber
charts maps homeomorphically to each chart's exact coordinate overlap.  This
file pushes the fixed group-overlap Haar measures through those two
homeomorphisms and transports their presentation scalar across the
certified cross-chart transition.

The resulting coordinate measures are defined from the fixed group Haar
restrictions.  This file does not identify them with restrictions of the
independently constructed product differential measures on `R^x times SO`,
and hence does not evaluate the real presentation scalar.
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

/-- The transported chart identifies the exact common group source with its
transported-coordinate overlap. -/
def transportedRealCentralFiberSourceOverlapHomeomorphTarget
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientRealCentralFiberSourceOverlap hx ≃ₜ
      P.transportedRealCentralFiberTargetOverlap hx where
  toFun g :=
    ⟨((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx)
        |>.toHomeomorphSourceTarget ⟨g.1, g.2.1⟩).1,
      ⟨(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).map_source
          g.2.1,
        by
          change
            (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm
                (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1) ∈
              V.realCliffordGeneralSpinCentralFiberIdentityChart.source
          rw [(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).left_inv
            g.2.1]
          exact g.2.2⟩⟩
  invFun y :=
    ⟨((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx)
        |>.toHomeomorphSourceTarget.symm ⟨y.1, y.2.1⟩).1,
      ⟨(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm.map_source
          y.2.1,
        y.2.2⟩⟩
  left_inv g := by
    apply Subtype.ext
    exact (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).left_inv
      g.2.1
  right_inv y := by
    apply Subtype.ext
    exact (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).right_inv
      y.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      (((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx)
          |>.toHomeomorphSourceTarget.continuous.comp
            (continuous_subtype_val.subtype_mk
              (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) =>
                g.2.1))).subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      (((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx)
          |>.toHomeomorphSourceTarget.symm.continuous.comp
            (continuous_subtype_val.subtype_mk
              (fun (y : P.transportedRealCentralFiberTargetOverlap hx) =>
                y.2.1))).subtype_val)

/-- The ambient chart identifies the same common group source with its
ambient-coordinate overlap. -/
def ambientRealCentralFiberSourceOverlapHomeomorphTarget
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientRealCentralFiberSourceOverlap hx ≃ₜ
      P.ambientRealCentralFiberTargetOverlap hx where
  toFun g :=
    ⟨(V.realCliffordGeneralSpinCentralFiberIdentityChart
        |>.toHomeomorphSourceTarget ⟨g.1, g.2.2⟩).1,
      ⟨V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source g.2.2,
        by
          change
            V.realCliffordGeneralSpinCentralFiberIdentityChart.symm
                (V.realCliffordGeneralSpinCentralFiberIdentityChart g.1) ∈
              (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
          rw [V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv g.2.2]
          exact g.2.1⟩⟩
  invFun y :=
    ⟨(V.realCliffordGeneralSpinCentralFiberIdentityChart
        |>.toHomeomorphSourceTarget.symm ⟨y.1, y.2.1⟩).1,
      ⟨y.2.2,
        V.realCliffordGeneralSpinCentralFiberIdentityChart.symm.map_source
          y.2.1⟩⟩
  left_inv g := by
    apply Subtype.ext
    exact V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv g.2.2
  right_inv y := by
    apply Subtype.ext
    exact V.realCliffordGeneralSpinCentralFiberIdentityChart.right_inv y.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      ((V.realCliffordGeneralSpinCentralFiberIdentityChart
        |>.toHomeomorphSourceTarget.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) =>
              g.2.2))).subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    simpa only [Function.comp_apply] using
      ((V.realCliffordGeneralSpinCentralFiberIdentityChart
        |>.toHomeomorphSourceTarget.symm.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun (y : P.ambientRealCentralFiberTargetOverlap hx) =>
              y.2.1))).subtype_val)

/-- The cross-chart transition square commutes on the exact common source. -/
theorem transportedAmbientRealCentralFiberOverlapHomeomorph_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) :
    P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx
        (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx g) =
      P.ambientRealCentralFiberSourceOverlapHomeomorphTarget hx g := by
  apply Subtype.ext
  rw [P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph_apply hx]
  exact P.blockToAmbientTransportedRealCentralFiberIdentityChart_eq_ambient_apply
    hx g.1

/-- The fixed transported block Haar written in the exact transported target
coordinates. -/
def transportedRealCentralFiberTargetOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedRealCentralFiberTargetOverlap hx) :=
  Measure.map
    (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx)
    (P.transportedRealCentralFiberOverlapHaarMeasure hx)

/-- The fixed ambient Haar written in the exact ambient target coordinates. -/
def ambientRealCentralFiberTargetOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.ambientRealCentralFiberTargetOverlap hx) :=
  Measure.map
    (P.ambientRealCentralFiberSourceOverlapHomeomorphTarget hx)
    (P.ambientRealCentralFiberOverlapHaarMeasure hx)

/-- The coordinate transition carries the transported overlap measure to the
ambient overlap measure with precisely the real presentation scalar. -/
theorem map_transportedRealCentralFiberTargetOverlapHaarMeasure_eq_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx)
        (P.transportedRealCentralFiberTargetOverlapHaarMeasure hx) =
      P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx •
        P.ambientRealCentralFiberTargetOverlapHaarMeasure hx := by
  rw [transportedRealCentralFiberTargetOverlapHaarMeasure,
    ambientRealCentralFiberTargetOverlapHaarMeasure,
    P.transportedRealCentralFiberOverlapHaarMeasure_eq_smul hx]
  rw [Measure.map_smul
    (P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx)
    (P.ambientRealCentralFiberOverlapHaarMeasure hx)
    (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx)]
  rw [Measure.map_smul
    (P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx)
    (Measure.map
      (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx)
      (P.ambientRealCentralFiberOverlapHaarMeasure hx))
    (P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx)]
  rw [Measure.map_map
    (P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx).measurable
    (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx).measurable]
  apply congrArg
  apply Measure.map_congr
  filter_upwards [] with g
  exact P.transportedAmbientRealCentralFiberOverlapHomeomorph_commutes hx g

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
