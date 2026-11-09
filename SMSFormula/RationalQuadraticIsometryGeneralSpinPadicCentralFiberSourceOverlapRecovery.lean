import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberSourceOverlapMeasure

/-!
# Recovery of the selected p-adic source-overlap measure

The ambient product measure pulled back through the selected
central-fiber chart is identified here with the restriction of the
globally glued p-adic horizontal `GSpin` Haar measure to the
common source overlap.  This local restriction is used to compare
coherent finite-adelic cylinder weights.
The two independently selected chart domains are not identified.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (p : ℕ) [Fact (Nat.Prime p)]

local instance sourceOverlapRecoveryUnitMeasurableSpace :
    MeasurableSpace ℚ_[p]ˣ := borel _

local instance sourceOverlapRecoveryUnitBorelSpace :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

local instance sourceOverlapRecoveryGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

local instance sourceOverlapRecoveryGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-- The globally glued ambient p-adic horizontal Haar restricted intrinsically
to the genuine common group source. -/
def ambientPadicCentralFiberSourceOverlapHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
  Measure.comap Subtype.val
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)

/-- The intrinsic overlap Haar maps back to the literal group-measure
restriction. -/
theorem map_ambientPadicCentralFiberSourceOverlapHaarMeasure_subtype
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map Subtype.val
        (P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) := by
  rw [ambientPadicCentralFiberSourceOverlapHaarMeasure]
  exact map_comap_subtype_coe
    (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet _

/-- The common group overlap viewed inside the ambient selected identity-chart
source. -/
def ambientPadicCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source :=
  Subtype.val ⁻¹'
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source

/-- Inclusion of the common source overlap into the ambient selected chart
source. -/
def ambientPadicCentralFiberSourceOverlapToIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx →
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source :=
  fun g => ⟨g.1, g.2.2⟩

theorem measurableSet_ambientPadicCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSet
      (P.ambientPadicCentralFiberSourceOverlapWithinIdentitySource p hx) :=
  (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_source.measurableSet.preimage
    continuous_subtype_val.measurable

theorem preimage_ambientPadicCentralFiberSourceOverlapWithinIdentitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Subtype.val :
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source → _) ⁻¹'
        P.transportedAmbientPadicCentralFiberSourceOverlap p hx =
      P.ambientPadicCentralFiberSourceOverlapWithinIdentitySource p hx := by
  ext g
  simp [ambientPadicCentralFiberSourceOverlapWithinIdentitySource,
    transportedAmbientPadicCentralFiberSourceOverlap]

set_option backward.isDefEq.respectTransparency false in
/-- Mapping the intrinsic overlap Haar into the ambient identity source gives
the established identity-source measure restricted to the corresponding open
subset. -/
theorem map_ambientPadicCentralFiberSourceOverlapHaarMeasure_to_identitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.ambientPadicCentralFiberSourceOverlapToIdentitySource p hx)
        (P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p).restrict
        (P.ambientPadicCentralFiberSourceOverlapWithinIdentitySource p hx) := by
  apply (MeasurableEmbedding.subtype_coe
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_source.measurableSet)
      |>.map_injective
  have hj : Measurable
      (P.ambientPadicCentralFiberSourceOverlapToIdentitySource p hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =>
        g.2.2)).measurable
  rw [Measure.map_map continuous_subtype_val.measurable hj]
  change Measure.map Subtype.val
      (P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx) = _
  rw [P.map_ambientPadicCentralFiberSourceOverlapHaarMeasure_subtype p hx]
  rw [← P.preimage_ambientPadicCentralFiberSourceOverlapWithinIdentitySource p hx]
  rw [← Measure.restrict_map continuous_subtype_val.measurable
    (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet]
  calc
    (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =
        ((V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source).restrict
            (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) := by
      rw [Measure.restrict_restrict
        (P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap p hx).measurableSet]
      congr 2
      ext g
      simp [transportedAmbientPadicCentralFiberSourceOverlap]
    _ = (Measure.map Subtype.val
          (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p)).restrict
            (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
      congrArg
        (fun μ : Measure (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) =>
          μ.restrict (P.transportedAmbientPadicCentralFiberSourceOverlap p hx))
        (V.restrict_padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity p)

theorem preimage_ambientPadicCentralFiberTargetOverlap_from_identitySource
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (fun g : (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =>
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g.1) ⁻¹'
        P.ambientPadicCentralFiberTargetOverlap p hx =
      P.ambientPadicCentralFiberSourceOverlapWithinIdentitySource p hx := by
  ext g
  change
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g.1 ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).target ∩
          (fun y => (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y) ⁻¹'
            (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source ↔
      g.1 ∈ (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source
  constructor
  · intro hg
    rcases hg with ⟨_, hg⟩
    change (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p g.1) ∈
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source at hg
    rw [(V.padicCliffordGeneralSpinCentralFiberIdentityChart p).left_inv g.2] at hg
    exact hg
  · intro hg
    constructor
    · exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).map_source g.2
    · change (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p g.1) ∈
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source
      rw [(V.padicCliffordGeneralSpinCentralFiberIdentityChart p).left_inv g.2]
      exact hg

set_option backward.isDefEq.respectTransparency false in
/-- The ambient selected chart carries the intrinsic group-overlap Haar to the
fixed product measure on the exact coordinate overlap. -/
theorem map_ambientPadicCentralFiberSourceOverlapHaarMeasure_to_target
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map
        (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx) =
      P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx := by
  apply (MeasurableEmbedding.subtype_coe
    (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet).map_injective
  rw [Measure.map_map continuous_subtype_val.measurable
    (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx).measurable]
  let cf := fun g :
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source =>
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g.1
  have hcf : Measurable cf :=
    ((V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℚ_[p]).measurable.comp
      continuous_subtype_val.measurable).prodMk
      ((V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℚ_[p]).measurable.comp
        continuous_subtype_val.measurable)
  have hj : Measurable
      (P.ambientPadicCentralFiberSourceOverlapToIdentitySource p hx) :=
    (continuous_subtype_val.subtype_mk
      (fun (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) =>
        g.2.2)).measurable
  rw [show (Subtype.val ∘
      P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx) =
        cf ∘ P.ambientPadicCentralFiberSourceOverlapToIdentitySource p hx by
      funext g
      rfl]
  rw [← Measure.map_map hcf hj]
  rw [P.map_ambientPadicCentralFiberSourceOverlapHaarMeasure_to_identitySource p hx]
  rw [← P.preimage_ambientPadicCentralFiberTargetOverlap_from_identitySource p hx]
  rw [← Measure.restrict_map hcf
    (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet]
  change
    (Measure.map
      (fun g :
          (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target =>
        CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g)
      (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p)).restrict
        (P.ambientPadicCentralFiberTargetOverlap p hx) = _
  rw [V.map_padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber p]
  rw [ambientPadicCentralFiberTargetOverlapProductMeasure,
    map_comap_subtype_coe
      (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet]
  rw [Measure.restrict_restrict
    (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet]
  rw [Set.inter_eq_left.mpr (fun _ hy => hy.1)]

/-- The product measure pulled back through the selected ambient
chart is the restriction/comap of the globally glued p-adic group
Haar to the common source overlap. -/
theorem ambientPadicCentralFiberSourceOverlapProductMeasure_eq_haar
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx =
      P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx := by
  apply (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
    |>.toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map
      (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
        (P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx) =
    Measure.map (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx)
      (P.ambientPadicCentralFiberSourceOverlapHaarMeasure p hx)
  rw [P.map_ambientPadicCentralFiberSourceOverlapProductMeasure p hx]
  exact (P.map_ambientPadicCentralFiberSourceOverlapHaarMeasure_to_target p hx).symm

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
