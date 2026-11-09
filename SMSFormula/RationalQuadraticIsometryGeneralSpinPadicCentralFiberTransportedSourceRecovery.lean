import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberSourceOverlapRecovery

/-!
# Recovery of the transported p-adic source-overlap measure

The fixed block horizontal Haar is transported through the supplied intrinsic
`GSpin` presentation and restricted to the literal common source of the
transported and independently selected ambient charts.  This file identifies
that intrinsic restriction with the transported-block product measure already
defined on the same overlap subtype.

No chart domains are equated and no Haar-comparison scalar is evaluated.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance transportedSourceRecoveryUnitMeasurableSpace :
    MeasurableSpace ℚ_[p]ˣ := borel _

local instance transportedSourceRecoveryUnitBorelSpace :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

local instance transportedSourceRecoveryBlockGroupMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]) :=
  borel _

local instance transportedSourceRecoveryBlockGroupBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]) :=
  ⟨rfl⟩

local instance transportedSourceRecoveryAmbientGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

local instance transportedSourceRecoveryAmbientGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-- The transported block Haar restricted intrinsically to the exact common
group source of the transported and ambient p-adic charts. -/
def transportedPadicCentralFiberSourceOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
  Measure.comap Subtype.val
    (Measure.map
      (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p])
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p))

theorem map_transportedPadicCentralFiberSourceOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      (Measure.map
        (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p])
        ((P.blockSpace hx)
          |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)).restrict
        (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) := by
  rw [transportedPadicCentralFiberSourceOverlapHaarMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet _

/-- The block identity-chart source transported to the source of the existing
presentation chart. -/
def blockPadicCentralFiberIdentitySourceHomeomorphTransported
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).source ≃ₜ
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source where
  toFun g :=
    ⟨P.blockToAmbientGeneralSpinIntrinsicPoint ℚ_[p] hx g.1,
      (P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff
        hx p _).2 (by
          rw [P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℚ_[p] hx]
          exact g.2)⟩
  invFun g :=
    ⟨P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g.1,
      (P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff
        hx p g.1).1 g.2⟩
  left_inv g := by
    apply Subtype.ext
    exact P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℚ_[p] hx g.1
  right_inv g := by
    apply Subtype.ext
    exact P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock ℚ_[p] hx g.1
  continuous_toFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- The fixed block identity-source measure transported to the presentation
chart source. -/
def transportedPadicCentralFiberIdentitySourceMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source :=
  Measure.map
    (P.blockPadicCentralFiberIdentitySourceHomeomorphTransported p hx)
    ((P.blockSpace hx)
      |>.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p)

/-- The exact common source viewed inside the transported chart source. -/
def transportedPadicCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source :=
  Subtype.val ⁻¹' (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source

/-- Inclusion of the common source into the transported chart source. -/
def transportedPadicCentralFiberSourceOverlapToTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx →
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source :=
  fun g => ⟨g.1, g.2.1⟩

theorem measurableSet_transportedPadicCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSet
      (P.transportedPadicCentralFiberSourceOverlapWithinTransportedSource p hx) :=
  (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_source.measurableSet.preimage
    continuous_subtype_val.measurable

/-- The transported block identity-source measure written in the target of
the transported chart. -/
def transportedPadicCentralFiberIdentityChartTargetMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target :=
  Measure.map
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
      |>.toHomeomorphSourceTarget)
    (P.transportedPadicCentralFiberIdentitySourceMeasure p hx)

set_option backward.isDefEq.respectTransparency false in
theorem map_transportedPadicCentralFiberIdentityChartTargetMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.transportedPadicCentralFiberIdentityChartTargetMeasure p hx) =
      (P.transportedBlockPadicCentralFiberProductMeasure p hx).restrict
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target := by
  rw [transportedPadicCentralFiberIdentityChartTargetMeasure,
    transportedPadicCentralFiberIdentitySourceMeasure]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
      |>.toHomeomorphSourceTarget).measurable]
  rw [Measure.map_map
    (continuous_subtype_val.measurable.comp
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
        |>.toHomeomorphSourceTarget).measurable)
    (P.blockPadicCentralFiberIdentitySourceHomeomorphTransported p hx).measurable]
  let T := P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℚ_[p]
  let cf := fun g :
      (P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p |>.source =>
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
      (P.blockSpace hx) ℚ_[p] g.1
  have hcf : Measurable cf :=
    (((P.blockSpace hx).continuous_cliffordGeneralSpinSimilitudeGroupHom ℚ_[p]).measurable.comp
      continuous_subtype_val.measurable).prodMk
      (((P.blockSpace hx)
        |>.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℚ_[p]).measurable.comp
          continuous_subtype_val.measurable)
  have hT : Measurable (fun y => T y) := T.continuous.measurable
  rw [show
      (Subtype.val ∘
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
            |>.toHomeomorphSourceTarget)) ∘
            P.blockPadicCentralFiberIdentitySourceHomeomorphTransported p hx =
        (fun y => T y) ∘ cf by
      funext g
      change P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
          (P.blockToAmbientGeneralSpinIntrinsicPoint ℚ_[p] hx g.1) = _
      rw [P.blockToAmbientTransportedPadicCentralFiberIdentityChart_apply hx p]
      exact P.blockToAmbientGeneralSpin_centralFiber_commutes ℚ_[p] hx g.1]
  change Measure.map ((fun y => T y) ∘ cf)
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p) = _
  rw [← Measure.map_map hT hcf]
  dsimp only [cf]
  change Measure.map (fun y => T y)
      (Measure.map
        (fun g : (P.blockSpace hx)
            |>.padicCliffordGeneralSpinCentralSpinIdentityChart p |>.target =>
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
            (P.blockSpace hx) ℚ_[p] g)
        ((P.blockSpace hx)
          |>.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p)) = _
  rw [(P.blockSpace hx)
    |>.map_padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber p]
  rw [transportedBlockPadicCentralFiberProductMeasure]
  change Measure.map (fun y => T y)
      (((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p).restrict
          ((P.blockSpace hx)
            |>.padicCliffordGeneralSpinHorizontalProductIdentityChart p |>.target)) =
    (Measure.map (fun y => T y)
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)).restrict
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target
  rw [Measure.restrict_map hT
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_target.measurableSet]
  congr 2
  ext y
  change y ∈ ((P.blockSpace hx)
      |>.padicCliffordGeneralSpinHorizontalProductIdentityChart p |>.target) ↔
    T y ∈ (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target
  rw [P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_target_iff hx p]
  change y ∈ ((P.blockSpace hx)
      |>.padicCliffordGeneralSpinHorizontalProductIdentityChart p |>.target) ↔
    T.symm (T y) ∈ ((P.blockSpace hx)
      |>.padicCliffordGeneralSpinCentralFiberIdentityChart p |>.target)
  rw [T.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrict_transportedBlockPadicHaar_identitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Measure.map
      (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p])
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)).restrict
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source =
      Measure.map Subtype.val
        (P.transportedPadicCentralFiberIdentitySourceMeasure p hx) := by
  let G := P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]
  have hG : Measurable (fun g => G g) := G.continuous.measurable
  rw [Measure.restrict_map hG
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_source.measurableSet]
  have hpreimage :
      (fun g => G g) ⁻¹'
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source =
        ((P.blockSpace hx)
          |>.padicCliffordGeneralSpinCentralFiberIdentityChart p |>.source) := by
    ext g
    change P.blockToAmbientGeneralSpinIntrinsicPoint ℚ_[p] hx g ∈
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source ↔ _
    rw [P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff hx p]
    rw [P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient ℚ_[p] hx]
  rw [hpreimage]
  rw [(P.blockSpace hx)
    |>.restrict_padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity p]
  rw [transportedPadicCentralFiberIdentitySourceMeasure]
  rw [Measure.map_map hG continuous_subtype_val.measurable]
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.blockPadicCentralFiberIdentitySourceHomeomorphTransported p hx).measurable]
  apply Measure.map_congr
  filter_upwards [] with g
  rfl

theorem preimage_transportedPadicCentralFiberSourceOverlapWithinTransportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Subtype.val :
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source → _) ⁻¹'
        P.transportedAmbientPadicCentralFiberSourceOverlap p hx =
      P.transportedPadicCentralFiberSourceOverlapWithinTransportedSource p hx := by
  ext g
  simp [transportedPadicCentralFiberSourceOverlapWithinTransportedSource,
    transportedAmbientPadicCentralFiberSourceOverlap]

theorem map_transportedPadicCentralFiberOverlapHaarMeasure_to_transportedSource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedPadicCentralFiberSourceOverlapToTransportedSource p hx)
        (P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      (P.transportedPadicCentralFiberIdentitySourceMeasure p hx).restrict
        (P.transportedPadicCentralFiberSourceOverlapWithinTransportedSource p hx) := by
  apply (MeasurableEmbedding.subtype_coe
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
      |>.open_source.measurableSet)).map_injective
  have hj : Measurable
      (P.transportedPadicCentralFiberSourceOverlapToTransportedSource p hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) => g.2.1)).measurable
  rw [Measure.map_map continuous_subtype_val.measurable hj]
  change Measure.map Subtype.val
      (P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx) = _
  rw [P.map_transportedPadicCentralFiberSourceOverlapHaarMeasure_subtype p hx]
  rw [← P.preimage_transportedPadicCentralFiberSourceOverlapWithinTransportedSource p hx]
  rw [← Measure.restrict_map continuous_subtype_val.measurable
    (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet]
  calc
    (Measure.map
      (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p])
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)).restrict
        (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =
      ((Measure.map
        (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p])
        ((P.blockSpace hx)
          |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)).restrict
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source).restrict
            (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) := by
      rw [Measure.restrict_restrict
        (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet]
      congr 2
      ext g
      simp only [transportedAmbientPadicCentralFiberSourceOverlap, Set.mem_inter_iff]
      aesop
    _ = (Measure.map Subtype.val
        (P.transportedPadicCentralFiberIdentitySourceMeasure p hx)).restrict
          (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
      congrArg
        (fun μ : Measure (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) =>
          μ.restrict (P.transportedAmbientPadicCentralFiberSourceOverlap p hx))
        (P.restrict_transportedBlockPadicHaar_identitySource p hx)

theorem preimage_transportedPadicCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (fun g :
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source =>
        P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1) ⁻¹'
        P.transportedPadicCentralFiberTargetOverlap p hx =
      P.transportedPadicCentralFiberSourceOverlapWithinTransportedSource p hx := by
  ext g
  change
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1 ∈
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target ∩
          (fun y =>
            (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y) ⁻¹'
            (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source ↔
      g.1 ∈ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source
  constructor
  · intro hg
    rcases hg with ⟨_, hg⟩
    change
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1) ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source at hg
    rw [(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).left_inv g.2] at hg
    exact hg
  · intro hg
    constructor
    · exact
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).map_source g.2
    · change
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm
            (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1) ∈
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source
      rw [(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).left_inv g.2]
      exact hg

theorem map_transportedPadicCentralFiberTargetOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (Measure.map
          (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
          (P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx)) =
      (P.transportedBlockPadicCentralFiberProductMeasure p hx).restrict
        (P.transportedPadicCentralFiberTargetOverlap p hx) := by
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx).measurable]
  let cf := fun g :
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source =>
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1
  have hcf : Measurable cf :=
    continuous_subtype_val.measurable.comp
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
        |>.toHomeomorphSourceTarget.measurable)
  have hj : Measurable
      (P.transportedPadicCentralFiberSourceOverlapToTransportedSource p hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) => g.2.1)).measurable
  rw [show (Subtype.val ∘
      P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx) =
        cf ∘ P.transportedPadicCentralFiberSourceOverlapToTransportedSource p hx by
      funext g
      rfl]
  rw [← Measure.map_map hcf hj]
  rw [P.map_transportedPadicCentralFiberOverlapHaarMeasure_to_transportedSource p hx]
  rw [← P.preimage_transportedPadicCentralFiberTargetOverlap p hx]
  rw [← Measure.restrict_map hcf
    (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet]
  dsimp only [cf]
  rw [show
      (fun g :
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source =>
        P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g.1) =
        Subtype.val ∘
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
            |>.toHomeomorphSourceTarget) by
      funext g
      rfl]
  rw [← Measure.map_map continuous_subtype_val.measurable
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
      |>.toHomeomorphSourceTarget.measurable)]
  change
    (Measure.map Subtype.val
      (P.transportedPadicCentralFiberIdentityChartTargetMeasure p hx)).restrict
        (P.transportedPadicCentralFiberTargetOverlap p hx) = _
  rw [P.map_transportedPadicCentralFiberIdentityChartTargetMeasure_subtype p hx]
  rw [Measure.restrict_restrict
    (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet]
  rw [Set.inter_eq_left.mpr (fun _ hy => hy.1)]

/-- The transported product measure is literally the transported block Haar
restricted to the common p-adic group source. -/
theorem transportedPadicCentralFiberSourceOverlapProductMeasure_eq_haar
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx =
      P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx := by
  apply (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
    |>.toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map
      (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx) =
    Measure.map
      (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.transportedPadicCentralFiberSourceOverlapHaarMeasure p hx)
  rw [P.map_transportedPadicCentralFiberSourceOverlapProductMeasure p hx]
  apply (MeasurableEmbedding.subtype_coe
    (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet).map_injective
  rw [P.map_transportedPadicCentralFiberTargetOverlapHaarMeasure_subtype p hx]
  rw [transportedPadicCentralFiberTargetOverlapProductMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet _

/-! ## Recovery on the native block carrier -/

/-- The genuine common source pulled back to the native block p-adic `GSpin`
carrier by the supplied presentation. -/
def blockPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set ((P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]) ⁻¹'
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx

theorem isOpen_blockPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.blockPadicCentralFiberSourceOverlap p hx) :=
  (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).preimage
    (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).continuous

/-- The presentation identifies its literal block pullback with the common
ambient source. -/
def blockPadicCentralFiberSourceOverlapHomeomorphAmbient
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockPadicCentralFiberSourceOverlap p hx ≃ₜ
      P.transportedAmbientPadicCentralFiberSourceOverlap p hx where
  toEquiv := Equiv.subtypeEquiv
    (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).toEquiv
    (fun _ => Iff.rfl)
  continuous_toFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- The inverse presentation identifies the common ambient source with its
literal pullback on the native block group. -/
def transportedPadicCentralFiberSourceOverlapHomeomorphBlock
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx ≃ₜ
      P.blockPadicCentralFiberSourceOverlap p hx :=
  (P.blockPadicCentralFiberSourceOverlapHomeomorphAmbient p hx).symm

/-- The globally glued block p-adic horizontal Haar restricted intrinsically
to the pulled-back common source. -/
def blockPadicCentralFiberSourceOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.blockPadicCentralFiberSourceOverlap p hx) :=
  Measure.comap Subtype.val
    ((P.blockSpace hx).padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)

theorem map_blockPadicCentralFiberSourceOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.blockPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (P.blockPadicCentralFiberSourceOverlap p hx) := by
  rw [blockPadicCentralFiberSourceOverlapHaarMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_blockPadicCentralFiberSourceOverlap p hx).measurableSet _

/-- Applying the inverse presentation to the transported source product
measure recovers the literal block-Haar restriction, with no scalar left. -/
theorem map_transportedPadicCentralFiberSourceOverlapProductMeasure_to_block
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock p hx)
        (P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx) =
      P.blockPadicCentralFiberSourceOverlapHaarMeasure p hx := by
  let G := P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]
  let s := P.blockPadicCentralFiberSourceOverlap p hx
  let t := P.transportedAmbientPadicCentralFiberSourceOverlap p hx
  let e := P.transportedPadicCentralFiberSourceOverlapHomeomorphBlock p hx
  let μ := (P.blockSpace hx).padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
  let ν := Measure.map G μ
  have hforward : Measure.map e.symm (Measure.comap Subtype.val μ) =
      Measure.comap Subtype.val ν := by
    change Measure.map e.symm.toMeasurableEquiv (Measure.comap Subtype.val μ) =
      Measure.comap Subtype.val ν
    have h := Measure.map_comap_subtype_of_map_smul_of_mem_iff
      (P.isOpen_blockPadicCentralFiberSourceOverlap p hx).measurableSet
      (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet
      G G.measurable e.symm.toMeasurableEquiv
      (by
        funext g
        rfl)
      μ ν 1 (by simp only [ν, one_smul]) (fun _ => Iff.rfl)
    simpa only [one_smul] using h
  rw [P.transportedPadicCentralFiberSourceOverlapProductMeasure_eq_haar p hx]
  change Measure.map e (Measure.comap Subtype.val ν) =
    Measure.comap Subtype.val μ
  rw [← hforward]
  exact e.toMeasurableEquiv.map_map_symm

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
