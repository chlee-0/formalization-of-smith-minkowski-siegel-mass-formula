import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberOverlapTargetMeasure

/-!
# Ambient product density on the central-fiber target overlap

The ambient central-fiber chart sends the fixed Haar measure on the exact
common group overlap to the restriction of the repository's fixed product
differential measure on `ℝˣ × SO`.  The chart domains remain independent: the
proof passes through the literal common source and the certified ambient
target overlap.

This is the ambient half of the target-density comparison.  It does not
identify the transported block target measure with the transported block
product density, and hence does not evaluate the real presentation scalar.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

noncomputable local instance ambientDensityRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance ambientDensityRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance ambientDensityRealSOGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance ambientDensityRealSOGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The common group overlap viewed inside the ambient identity-chart source. -/
def ambientRealCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set V.realCliffordGeneralSpinCentralFiberIdentityChart.source :=
  Subtype.val ⁻¹'
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source

/-- The canonical inclusion of the common group overlap into the ambient
identity-chart source. -/
def ambientRealCentralFiberSourceOverlapToIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientRealCentralFiberSourceOverlap hx →
      V.realCliffordGeneralSpinCentralFiberIdentityChart.source :=
  fun g => ⟨g.1, g.2.2⟩

theorem measurableSet_ambientRealCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSet
      (P.ambientRealCentralFiberSourceOverlapWithinIdentitySource hx) :=
  (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_source.measurableSet.preimage
    continuous_subtype_val.measurable

theorem preimage_ambientRealCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Subtype.val : V.realCliffordGeneralSpinCentralFiberIdentityChart.source → _) ⁻¹'
        P.transportedAmbientRealCentralFiberSourceOverlap hx =
      P.ambientRealCentralFiberSourceOverlapWithinIdentitySource hx := by
  ext g
  simp [ambientRealCentralFiberSourceOverlapWithinIdentitySource,
    transportedAmbientRealCentralFiberSourceOverlap]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed Haar measure on the common group overlap, mapped into the
ambient identity-chart source, is the intrinsic identity-source measure
restricted to the corresponding open subset. -/
theorem map_ambientRealCentralFiberOverlapHaarMeasure_to_identitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map (P.ambientRealCentralFiberSourceOverlapToIdentitySource hx)
        (P.ambientRealCentralFiberOverlapHaarMeasure hx) =
      V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure.restrict
        (P.ambientRealCentralFiberSourceOverlapWithinIdentitySource hx) := by
  apply (MeasurableEmbedding.subtype_coe
    V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source.measurableSet).map_injective
  have hj : Measurable
      (P.ambientRealCentralFiberSourceOverlapToIdentitySource hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) => g.2.2)).measurable
  rw [Measure.map_map continuous_subtype_val.measurable hj]
  change Measure.map Subtype.val
      (P.ambientRealCentralFiberOverlapHaarMeasure hx) = _
  rw [P.map_ambientRealCentralFiberOverlapHaarMeasure_subtype hx]
  rw [← P.preimage_ambientRealCentralFiberSourceOverlapWithinIdentitySource hx]
  rw [← Measure.restrict_map continuous_subtype_val.measurable
    (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet]
  calc
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
        (P.transportedAmbientRealCentralFiberSourceOverlap hx) =
        (V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure.restrict
          V.realCliffordGeneralSpinCentralFiberIdentityChart.source).restrict
            (P.transportedAmbientRealCentralFiberSourceOverlap hx) := by
      rw [Measure.restrict_restrict
        (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet]
      congr 2
      ext g
      simp [transportedAmbientRealCentralFiberSourceOverlap]
    _ = (Measure.map Subtype.val
          V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure).restrict
            (P.transportedAmbientRealCentralFiberSourceOverlap hx) :=
      congrArg
        (fun μ : Measure (V.CliffordGeneralSpinIntrinsicPoint ℝ) =>
          μ.restrict (P.transportedAmbientRealCentralFiberSourceOverlap hx))
        V.restrict_realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity

theorem preimage_ambientRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (fun g : V.realCliffordGeneralSpinCentralFiberIdentityChart.source =>
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g.1) ⁻¹'
        P.ambientRealCentralFiberTargetOverlap hx =
      P.ambientRealCentralFiberSourceOverlapWithinIdentitySource hx := by
  ext g
  change
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g.1 ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.target ∩
          (fun y => V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y) ⁻¹'
            (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source ↔
      g.1 ∈ (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
  constructor
  · intro hg
    rcases hg with ⟨_, hg⟩
    change V.realCliffordGeneralSpinCentralFiberIdentityChart.symm
        (V.realCliffordGeneralSpinCentralFiberIdentityChart g.1) ∈
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source at hg
    rw [V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv g.2] at hg
    exact hg
  · intro hg
    constructor
    · exact V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source g.2
    · change V.realCliffordGeneralSpinCentralFiberIdentityChart.symm
          (V.realCliffordGeneralSpinCentralFiberIdentityChart g.1) ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
      rw [V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv g.2]
      exact hg

/-- The fixed ambient product differential measure restricted intrinsically
to the exact target overlap. -/
def ambientRealCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.ambientRealCentralFiberTargetOverlap hx) :=
  Measure.comap Subtype.val
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

set_option backward.isDefEq.respectTransparency false in
/-- The ambient target-coordinate Haar measure pushes to the literal
restriction of the fixed ambient product differential measure. -/
theorem map_ambientRealCentralFiberTargetOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.ambientRealCentralFiberTargetOverlapHaarMeasure hx) =
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure.restrict
        (P.ambientRealCentralFiberTargetOverlap hx) := by
  rw [ambientRealCentralFiberTargetOverlapHaarMeasure]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.ambientRealCentralFiberSourceOverlapHomeomorphTarget hx).measurable]
  let cf := fun g : V.realCliffordGeneralSpinCentralFiberIdentityChart.source =>
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g.1
  have hcf : Measurable cf :=
    ((V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℝ).measurable.comp
      continuous_subtype_val.measurable).prodMk
      ((V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℝ).measurable.comp
        continuous_subtype_val.measurable)
  have hj : Measurable
      (P.ambientRealCentralFiberSourceOverlapToIdentitySource hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) => g.2.2)).measurable
  rw [show (Subtype.val ∘
      P.ambientRealCentralFiberSourceOverlapHomeomorphTarget hx) =
        cf ∘ P.ambientRealCentralFiberSourceOverlapToIdentitySource hx by
      funext g
      rfl]
  rw [← Measure.map_map hcf hj]
  rw [P.map_ambientRealCentralFiberOverlapHaarMeasure_to_identitySource hx]
  rw [← P.preimage_ambientRealCentralFiberTargetOverlap hx]
  rw [← Measure.restrict_map hcf
    (P.isOpen_ambientRealCentralFiberTargetOverlap hx).measurableSet]
  change
    (Measure.map
      (fun g : V.realCliffordGeneralSpinCentralSpinIdentityChart.target =>
        CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g)
      V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure).restrict
        (P.ambientRealCentralFiberTargetOverlap hx) = _
  rw [V.map_realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber]
  rw [Measure.restrict_restrict
    (P.isOpen_ambientRealCentralFiberTargetOverlap hx).measurableSet]
  rw [Set.inter_eq_left.mpr (fun _ hy => hy.1)]

/-- Intrinsically on the target-overlap subtype, the ambient target-coordinate
Haar measure is the fixed ambient product differential measure. -/
theorem ambientRealCentralFiberTargetOverlapHaarMeasure_eq_product
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.ambientRealCentralFiberTargetOverlapHaarMeasure hx =
      P.ambientRealCentralFiberTargetOverlapProductMeasure hx := by
  apply (MeasurableEmbedding.subtype_coe
    (P.isOpen_ambientRealCentralFiberTargetOverlap hx).measurableSet).map_injective
  rw [P.map_ambientRealCentralFiberTargetOverlapHaarMeasure_subtype hx]
  rw [ambientRealCentralFiberTargetOverlapProductMeasure]
  exact (map_comap_subtype_coe
    (P.isOpen_ambientRealCentralFiberTargetOverlap hx).measurableSet _).symm

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
