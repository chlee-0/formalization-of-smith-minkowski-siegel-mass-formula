import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberAmbientTargetDensity

/-!
# Transported block product density on the central-fiber target overlap

The fixed block central-fiber product differential measure is pushed through
the supplied presentation's crossed-target equivalence.  This file proves
that its intrinsic restriction to the exact transported target overlap is the
already fixed transported target-coordinate Haar measure.

The proof transports the block identity-source measure through the actual
presentation chart and restricts only after the full source/target measure
square is literal.  It does not compare the transported block product density
with the ambient product density, evaluate the real presentation scalar, or
equate independently chosen chart domains.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

noncomputable local instance transportedDensityRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance transportedDensityRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance transportedDensityBlockRealSOGroupMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℝ) :=
  (P.blockSpace hx).realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance transportedDensityBlockRealSOGroupBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℝ) :=
  (P.blockSpace hx).realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance transportedDensityAmbientRealSOGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance transportedDensityAmbientRealSOGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The block identity-chart source transported to the source of the
presentation chart. -/
def blockRealCentralFiberIdentitySourceHomeomorphTransported
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart.source ≃ₜ
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source where
  toFun g :=
    ⟨P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ g.1,
      (P.mem_blockToAmbientTransportedRealCentralFiberIdentityChart_source_iff
        hx _).2 (by
          change P.ambientToBlockGeneralSpinIntrinsicPoint ℝ hx
              (P.blockToAmbientGeneralSpinIntrinsicPoint ℝ hx g.1) ∈ _
          rw [P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℝ hx]
          exact g.2)⟩
  invFun g :=
    ⟨P.ambientToBlockGeneralSpinIntrinsicPoint ℝ hx g.1,
      (P.mem_blockToAmbientTransportedRealCentralFiberIdentityChart_source_iff
        hx g.1).1 g.2⟩
  left_inv g := by
    apply Subtype.ext
    exact P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℝ hx g.1
  right_inv g := by
    apply Subtype.ext
    exact P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock ℝ hx g.1
  continuous_toFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- The fixed block identity-source measure transported to the presentation
chart source. -/
def transportedRealCentralFiberIdentitySourceMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source :=
  Measure.map
    (P.blockRealCentralFiberIdentitySourceHomeomorphTransported hx)
    ((P.blockSpace hx)
      |>.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure)

/-- The exact common source viewed inside the transported chart source. -/
def transportedRealCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source :=
  Subtype.val ⁻¹'
    V.realCliffordGeneralSpinCentralFiberIdentityChart.source

/-- Inclusion of the common source into the transported chart source. -/
def transportedRealCentralFiberSourceOverlapToTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientRealCentralFiberSourceOverlap hx →
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source :=
  fun g => ⟨g.1, g.2.1⟩

theorem measurableSet_transportedRealCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSet
      (P.transportedRealCentralFiberSourceOverlapWithinTransportedSource hx) :=
  V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source.measurableSet.preimage
    continuous_subtype_val.measurable

/-- The fixed block product differential measure transported to the ambient
central-fiber target coordinates. -/
def transportedBlockRealCentralFiberProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (ℝˣ × V.specialOrthogonalMatrixGroup ℝ) :=
  Measure.map
    (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℝ)
    ((P.blockSpace hx)
      |>.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)

/-- The transported block identity-source measure written in the target of
the transported chart. -/
def transportedRealCentralFiberIdentityChartTargetMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target :=
  Measure.map
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
      |>.toHomeomorphSourceTarget)
    (P.transportedRealCentralFiberIdentitySourceMeasure hx)

set_option backward.isDefEq.respectTransparency false in
theorem map_transportedRealCentralFiberIdentityChartTargetMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.transportedRealCentralFiberIdentityChartTargetMeasure hx) =
      (P.transportedBlockRealCentralFiberProductMeasure hx).restrict
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target := by
  rw [transportedRealCentralFiberIdentityChartTargetMeasure,
    transportedRealCentralFiberIdentitySourceMeasure]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
      |>.toHomeomorphSourceTarget).measurable]
  rw [Measure.map_map
    (continuous_subtype_val.measurable.comp
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
        |>.toHomeomorphSourceTarget).measurable)
    (P.blockRealCentralFiberIdentitySourceHomeomorphTransported hx).measurable]
  let T := P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℝ
  let cf := fun g :
      (P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart.source =>
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (P.blockSpace hx) ℝ g.1
  have hcf : Measurable cf :=
    (((P.blockSpace hx).continuous_cliffordGeneralSpinSimilitudeGroupHom ℝ).measurable.comp
      continuous_subtype_val.measurable).prodMk
      (((P.blockSpace hx)
        |>.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℝ).measurable.comp
          continuous_subtype_val.measurable)
  have hT : Measurable (fun y => T y) := T.continuous.measurable
  rw [show
      (Subtype.val ∘
          (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
            |>.toHomeomorphSourceTarget)) ∘
            P.blockRealCentralFiberIdentitySourceHomeomorphTransported hx =
        (fun y => T y) ∘ cf by
      funext g
      change P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
          (P.blockToAmbientGeneralSpinIntrinsicPoint ℝ hx g.1) = _
      rw [P.blockToAmbientTransportedRealCentralFiberIdentityChart_apply hx]
      exact P.blockToAmbientGeneralSpin_centralFiber_commutes ℝ hx g.1]
  change Measure.map ((fun y => T y) ∘ cf)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure) = _
  rw [← Measure.map_map hT hcf]
  dsimp only [cf]
  change Measure.map (fun y => T y)
      (Measure.map
        (fun g : (P.blockSpace hx)
            |>.realCliffordGeneralSpinCentralSpinIdentityChart.target =>
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
            (P.blockSpace hx) ℝ g)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure)) = _
  rw [(P.blockSpace hx)
    |>.map_realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber]
  rw [transportedBlockRealCentralFiberProductMeasure]
  change Measure.map (fun y => T y)
      (((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialProductMeasure).restrict
          ((P.blockSpace hx)
            |>.realCliffordGeneralSpinHorizontalProductIdentityChart.target)) =
    (Measure.map (fun y => T y)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)).restrict
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target
  rw [Measure.restrict_map hT
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_target.measurableSet]
  congr 2
  ext y
  change y ∈ ((P.blockSpace hx)
      |>.realCliffordGeneralSpinHorizontalProductIdentityChart.target) ↔
    T y ∈ (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target
  rw [P.mem_blockToAmbientTransportedRealCentralFiberIdentityChart_target_iff hx]
  change y ∈ ((P.blockSpace hx)
      |>.realCliffordGeneralSpinHorizontalProductIdentityChart.target) ↔
    T.symm (T y) ∈ ((P.blockSpace hx)
      |>.realCliffordGeneralSpinCentralFiberIdentityChart.target)
  rw [T.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrict_transportedBlockRealHaar_identitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Measure.map
      (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)).restrict
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source =
      Measure.map Subtype.val
        (P.transportedRealCentralFiberIdentitySourceMeasure hx) := by
  let G := P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx
  have hG : Measurable (fun g => G g) := G.continuous.measurable
  rw [Measure.restrict_map hG
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_source.measurableSet]
  have hpreimage :
      (fun g => G g) ⁻¹'
          (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source =
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinCentralFiberIdentityChart.source) := by
    ext g
    change P.blockToAmbientGeneralSpinIntrinsicPoint ℝ hx g ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source ↔ _
    rw [P.mem_blockToAmbientTransportedRealCentralFiberIdentityChart_source_iff hx]
    rw [P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℝ hx]
  rw [hpreimage]
  rw [(P.blockSpace hx)
    |>.restrict_realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity]
  rw [transportedRealCentralFiberIdentitySourceMeasure]
  rw [Measure.map_map hG continuous_subtype_val.measurable]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.blockRealCentralFiberIdentitySourceHomeomorphTransported hx).measurable]
  apply Measure.map_congr
  filter_upwards [] with g
  rfl

theorem preimage_transportedRealCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Subtype.val :
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source → _) ⁻¹'
        P.transportedAmbientRealCentralFiberSourceOverlap hx =
      P.transportedRealCentralFiberSourceOverlapWithinTransportedSource hx := by
  ext g
  simp [transportedRealCentralFiberSourceOverlapWithinTransportedSource,
    transportedAmbientRealCentralFiberSourceOverlap]

theorem map_transportedRealCentralFiberOverlapHaarMeasure_to_transportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedRealCentralFiberSourceOverlapToTransportedSource hx)
        (P.transportedRealCentralFiberOverlapHaarMeasure hx) =
      (P.transportedRealCentralFiberIdentitySourceMeasure hx).restrict
        (P.transportedRealCentralFiberSourceOverlapWithinTransportedSource hx) := by
  apply (MeasurableEmbedding.subtype_coe
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
      |>.open_source.measurableSet)).map_injective
  have hj : Measurable
      (P.transportedRealCentralFiberSourceOverlapToTransportedSource hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) => g.2.1)).measurable
  rw [Measure.map_map continuous_subtype_val.measurable hj]
  change Measure.map Subtype.val
      (P.transportedRealCentralFiberOverlapHaarMeasure hx) = _
  rw [P.map_transportedRealCentralFiberOverlapHaarMeasure_subtype hx]
  rw [← P.preimage_transportedRealCentralFiberSourceOverlapWithinTransportedSource hx]
  rw [← Measure.restrict_map continuous_subtype_val.measurable
    (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet]
  calc
    (Measure.map
      (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
      ((P.blockSpace hx)
        |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)).restrict
        (P.transportedAmbientRealCentralFiberSourceOverlap hx) =
      ((Measure.map
        (P.blockToAmbientRealGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)).restrict
          (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source).restrict
            (P.transportedAmbientRealCentralFiberSourceOverlap hx) := by
      rw [Measure.restrict_restrict
        (P.isOpen_transportedAmbientRealCentralFiberSourceOverlap hx).measurableSet]
      congr 2
      ext g
      simp only [transportedAmbientRealCentralFiberSourceOverlap,
        Set.mem_inter_iff]
      aesop
    _ = (Measure.map Subtype.val
        (P.transportedRealCentralFiberIdentitySourceMeasure hx)).restrict
          (P.transportedAmbientRealCentralFiberSourceOverlap hx) :=
      congrArg
        (fun μ : Measure (V.CliffordGeneralSpinIntrinsicPoint ℝ) =>
          μ.restrict (P.transportedAmbientRealCentralFiberSourceOverlap hx))
        (P.restrict_transportedBlockRealHaar_identitySource hx)

theorem preimage_transportedRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (fun g :
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source =>
        P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1) ⁻¹'
        P.transportedRealCentralFiberTargetOverlap hx =
      P.transportedRealCentralFiberSourceOverlapWithinTransportedSource hx := by
  ext g
  change
    P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1 ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target ∩
          (fun y =>
            (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y) ⁻¹'
            V.realCliffordGeneralSpinCentralFiberIdentityChart.source ↔
      g.1 ∈ V.realCliffordGeneralSpinCentralFiberIdentityChart.source
  constructor
  · intro hg
    rcases hg with ⟨_, hg⟩
    change
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm
          (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1) ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source at hg
    rw [(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).left_inv g.2] at hg
    exact hg
  · intro hg
    constructor
    · exact
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).map_source g.2
    · change
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm
            (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1) ∈
          V.realCliffordGeneralSpinCentralFiberIdentityChart.source
      rw [(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).left_inv g.2]
      exact hg

/-- The fixed block product differential measure, transported to ambient
target coordinates and restricted intrinsically to the exact overlap. -/
def transportedRealCentralFiberTargetOverlapProductMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedRealCentralFiberTargetOverlap hx) :=
  Measure.comap Subtype.val
    (P.transportedBlockRealCentralFiberProductMeasure hx)

set_option backward.isDefEq.respectTransparency false in
theorem map_transportedRealCentralFiberTargetOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.transportedRealCentralFiberTargetOverlapHaarMeasure hx) =
      (P.transportedBlockRealCentralFiberProductMeasure hx).restrict
        (P.transportedRealCentralFiberTargetOverlap hx) := by
  rw [transportedRealCentralFiberTargetOverlapHaarMeasure]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx).measurable]
  let cf := fun g :
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source =>
    P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g.1
  have hcf : Measurable cf :=
    continuous_subtype_val.measurable.comp
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
        |>.toHomeomorphSourceTarget.measurable)
  have hj : Measurable
      (P.transportedRealCentralFiberSourceOverlapToTransportedSource hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientRealCentralFiberSourceOverlap hx) => g.2.1)).measurable
  rw [show (Subtype.val ∘
      P.transportedRealCentralFiberSourceOverlapHomeomorphTarget hx) =
        cf ∘ P.transportedRealCentralFiberSourceOverlapToTransportedSource hx by
      funext g
      rfl]
  rw [← Measure.map_map hcf hj]
  rw [P.map_transportedRealCentralFiberOverlapHaarMeasure_to_transportedSource hx]
  rw [← P.preimage_transportedRealCentralFiberTargetOverlap hx]
  rw [← Measure.restrict_map hcf
    (P.isOpen_transportedRealCentralFiberTargetOverlap hx).measurableSet]
  dsimp only [cf]
  change
    (Measure.map
      (Subtype.val ∘
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
          |>.toHomeomorphSourceTarget))
      (P.transportedRealCentralFiberIdentitySourceMeasure hx)).restrict
        (P.transportedRealCentralFiberTargetOverlap hx) = _
  rw [← Measure.map_map continuous_subtype_val.measurable
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
      |>.toHomeomorphSourceTarget.measurable)]
  change
    (Measure.map Subtype.val
      (P.transportedRealCentralFiberIdentityChartTargetMeasure hx)).restrict
        (P.transportedRealCentralFiberTargetOverlap hx) = _
  rw [P.map_transportedRealCentralFiberIdentityChartTargetMeasure_subtype hx]
  rw [Measure.restrict_restrict
    (P.isOpen_transportedRealCentralFiberTargetOverlap hx).measurableSet]
  rw [Set.inter_eq_left.mpr (fun _ hy => hy.1)]

theorem transportedRealCentralFiberTargetOverlapHaarMeasure_eq_product
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedRealCentralFiberTargetOverlapHaarMeasure hx =
      P.transportedRealCentralFiberTargetOverlapProductMeasure hx := by
  apply (MeasurableEmbedding.subtype_coe
    (P.isOpen_transportedRealCentralFiberTargetOverlap hx).measurableSet).map_injective
  rw [P.map_transportedRealCentralFiberTargetOverlapHaarMeasure_subtype hx]
  rw [transportedRealCentralFiberTargetOverlapProductMeasure]
  exact (map_comap_subtype_coe
    (P.isOpen_transportedRealCentralFiberTargetOverlap hx).measurableSet _).symm

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
