import SMSFormula.RationalCliffordGeneralSpinLocalDifferentialChartMeasure
import SMSFormula.RationalIdeleDifferentialSquareModulus
import SMSFormula.RationalPadicUnitSquarePushforward

/-!
# One-dimensional square factors in local horizontal charts

The horizontal local `GSpin` chart is the product of the scalar square chart
and the established Spin-to-`SO` chart.  This file separates those two
measure coordinates literally.  The target restriction and its inverse
transport split, through the canonical set-product homeomorphisms, as the
one-dimensional square-branch measure times the existing Spin chart measure.

Consequently the only unresolved local normalization is the comparison of
the square branch's inverse-transport measure with ambient multiplicative
Haar on its source.  Spin contributes coefficient one, and the two algebraic
sheets contribute no coefficient here.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 200000

private theorem map_setProd_comap_prod
    {alpha beta : Type*}
    [TopologicalSpace alpha] [TopologicalSpace beta]
    [MeasurableSpace alpha] [MeasurableSpace beta]
    [BorelSpace alpha] [BorelSpace beta]
    (s : Set alpha) (t : Set beta) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (mu : Measure alpha) (nu : Measure beta)
    [SigmaFinite mu] [SigmaFinite nu]
    [SigmaFinite (mu.comap (fun x : s => x.1))]
    [SigmaFinite (nu.comap (fun x : t => x.1))] :
    Measure.map (Homeomorph.Set.prod s t)
        (Measure.comap Subtype.val (mu.prod nu)) =
      (Measure.comap Subtype.val mu).prod (Measure.comap Subtype.val nu) := by
  have hprodMeasurable : Measurable (Homeomorph.Set.prod s t) := by
    have hfst : Measurable (fun x : (s ×ˢ t) => (⟨x.1.1, x.2.1⟩ : s)) :=
      Measurable.subtype_mk
        (measurable_fst.comp
          (measurable_subtype_coe : Measurable (Subtype.val : (s ×ˢ t) → alpha × beta)))
    have hsnd : Measurable (fun x : (s ×ˢ t) => (⟨x.1.2, x.2.2⟩ : t)) :=
      Measurable.subtype_mk
        (measurable_snd.comp
          (measurable_subtype_coe : Measurable (Subtype.val : (s ×ˢ t) → alpha × beta)))
    simpa only [Homeomorph.Set.prod_apply] using hfst.prodMk hsnd
  symm
  apply Measure.prod_eq
  intro a b ha hb
  rw [Measure.map_apply hprodMeasurable (ha.prod hb)]
  rw [(MeasurableEmbedding.subtype_coe (hs.prod ht)).comap_apply]
  have himage :
      Subtype.val '' ((Homeomorph.Set.prod s t) ⁻¹' (a ×ˢ b)) =
        (Subtype.val '' a) ×ˢ (Subtype.val '' b) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨(Homeomorph.Set.prod s t z).1, hz.1, rfl⟩,
        ⟨(Homeomorph.Set.prod s t z).2, hz.2, rfl⟩⟩
    · rintro ⟨⟨za, hza, hzaVal⟩, ⟨zb, hzb, hzbVal⟩⟩
      have hx : x = (za.1, zb.1) :=
        Prod.ext hzaVal.symm hzbVal.symm
      subst x
      let z : (s ×ˢ t) := ⟨(za.1, zb.1), za.2, zb.2⟩
      refine ⟨z, ?_, rfl⟩
      exact ⟨hza, hzb⟩
  rw [himage, Measure.prod_prod,
    (MeasurableEmbedding.subtype_coe hs).comap_apply,
    (MeasurableEmbedding.subtype_coe ht).comap_apply]

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance : MeasurableSpace ℝˣ := borel _
noncomputable local instance : BorelSpace ℝˣ := ⟨rfl⟩
noncomputable local instance : SecondCountableTopology ℝˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology
noncomputable local instance :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm
noncomputable local instance :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable def realUnitSquareIdentityChartTargetMeasure :
    Measure (Rat.unitSquareIdentityChart ℝ).target :=
  Measure.comap Subtype.val (Measure.haar : Measure ℝˣ)

noncomputable def realUnitSquareIdentityChartSourceMeasure :
    Measure (Rat.unitSquareIdentityChart ℝ).source :=
  Measure.map (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.symm
    realUnitSquareIdentityChartTargetMeasure

theorem map_realUnitSquareIdentityChartSourceMeasure :
    Measure.map
        (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
        realUnitSquareIdentityChartSourceMeasure =
      realUnitSquareIdentityChartTargetMeasure := by
  rw [realUnitSquareIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget.toMeasurableEquiv

set_option backward.isDefEq.respectTransparency false in
theorem map_realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure_split :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℝ).target
          V.realCliffordSpinCandidateIdentityChart.target)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure =
      realUnitSquareIdentityChartTargetMeasure.prod
        V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) := by
    exact Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℝˣ)
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite
      (Measure.comap Subtype.val (Measure.haar : Measure ℝˣ) :
        Measure (Rat.unitSquareIdentityChart ℝ).target) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart ℝ).open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      (Measure.comap Subtype.val V.realInvariantDifferentialGroupMeasure :
        Measure V.realCliffordSpinCandidateIdentityChart.target) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet]
    infer_instance
  rw [realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
    realCliffordGeneralSpinHorizontalDifferentialProductMeasure,
    realUnitSquareIdentityChartTargetMeasure,
    realCliffordSpinCandidateIdentityChartTargetMeasure]
  exact map_setProd_comap_prod _ _
    (Rat.unitSquareIdentityChart ℝ).open_target.measurableSet
    V.realCliffordSpinCandidateIdentityChart.open_target.measurableSet _ _

set_option backward.isDefEq.respectTransparency false in
theorem map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_split :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℝ).source
          V.realCliffordSpinCandidateIdentityChart.source)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      realUnitSquareIdentityChartSourceMeasure.prod
        V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let squareChart := Rat.unitSquareIdentityChart ℝ
  let spinChart := V.realCliffordSpinCandidateIdentityChart
  let productChart := V.realCliffordGeneralSpinHorizontalProductIdentityChart
  let sourceSplit := Homeomorph.Set.prod squareChart.source spinChart.source
  let targetSplit := Homeomorph.Set.prod squareChart.target spinChart.target
  let componentChart := squareChart.toHomeomorphSourceTarget.prodCongr
    spinChart.toHomeomorphSourceTarget
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) := by
    exact Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℝˣ)
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite realUnitSquareIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [realUnitSquareIdentityChartTargetMeasure,
      map_comap_subtype_coe squareChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite realUnitSquareIdentityChartSourceMeasure := by
    rw [realUnitSquareIdentityChartSourceMeasure]
    exact squareChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite
      V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe spinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  have hsourceMeasurable : Measurable sourceSplit := by
    have hfst : Measurable
        (fun x : (squareChart.source ×ˢ spinChart.source) =>
          (⟨x.1.1, x.2.1⟩ : squareChart.source)) :=
      Measurable.subtype_mk
        (measurable_fst.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.source ×ˢ spinChart.source) →
              ℝˣ × V.RealCliffordSpinCandidateGroup)))
    have hsnd : Measurable
        (fun x : (squareChart.source ×ˢ spinChart.source) =>
          (⟨x.1.2, x.2.2⟩ : spinChart.source)) :=
      Measurable.subtype_mk
        (measurable_snd.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.source ×ˢ spinChart.source) →
              ℝˣ × V.RealCliffordSpinCandidateGroup)))
    simpa only [sourceSplit, Homeomorph.Set.prod_apply] using hfst.prodMk hsnd
  have htargetMeasurable : Measurable targetSplit := by
    have hfst : Measurable
        (fun x : (squareChart.target ×ˢ spinChart.target) =>
          (⟨x.1.1, x.2.1⟩ : squareChart.target)) :=
      Measurable.subtype_mk
        (measurable_fst.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.target ×ˢ spinChart.target) →
              ℝˣ × V.RealSpecialOrthogonalGroup)))
    have hsnd : Measurable
        (fun x : (squareChart.target ×ˢ spinChart.target) =>
          (⟨x.1.2, x.2.2⟩ : spinChart.target)) :=
      Measurable.subtype_mk
        (measurable_snd.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.target ×ˢ spinChart.target) →
              ℝˣ × V.RealSpecialOrthogonalGroup)))
    simpa only [targetSplit, Homeomorph.Set.prod_apply] using hfst.prodMk hsnd
  have hcomponentMeasurable : Measurable componentChart :=
    componentChart.measurable
  have hcommute :
      componentChart ∘ sourceSplit =
        targetSplit ∘ productChart.toHomeomorphSourceTarget := by
    funext x
    rfl
  apply componentChart.toMeasurableEquiv.measurableEmbedding.map_injective
  calc
    Measure.map componentChart
        (Measure.map sourceSplit
          V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure) =
        Measure.map targetSplit
          (Measure.map productChart.toHomeomorphSourceTarget
            V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure) := by
      rw [Measure.map_map hcomponentMeasurable hsourceMeasurable,
        Measure.map_map htargetMeasurable
          productChart.toHomeomorphSourceTarget.measurable,
        hcommute]
    _ = Measure.map targetSplit
        V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure := by
      rw [V.map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure]
    _ = realUnitSquareIdentityChartTargetMeasure.prod
        V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
      exact
        V.map_realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure_split
    _ = (Measure.map squareChart.toHomeomorphSourceTarget
          realUnitSquareIdentityChartSourceMeasure).prod
        (Measure.map spinChart.toHomeomorphSourceTarget
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
      simp only [squareChart, spinChart,
        map_realUnitSquareIdentityChartSourceMeasure,
        V.map_realCliffordSpinCandidateIdentityChartSourceMeasure]
    _ = Measure.map componentChart
        (realUnitSquareIdentityChartSourceMeasure.prod
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
      simpa only [componentChart, Homeomorph.coe_prodCongr] using
        (Measure.map_prod_map
          realUnitSquareIdentityChartSourceMeasure
          V.realCliffordSpinCandidateIdentityChartSourceMeasure
          squareChart.toHomeomorphSourceTarget.measurable
          spinChart.toHomeomorphSourceTarget.measurable)

/-! ## P-adic square coordinate -/

noncomputable local instance localSquareFactorPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance localSquareFactorPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance localSquareFactorPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance localSquareFactorPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance localSquareFactorPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- Multiplicative Haar restricted to the target of the p-adic square branch. -/
noncomputable def padicUnitSquareIdentityChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (Rat.unitSquareIdentityChart ℚ_[p]).target :=
  Measure.comap Subtype.val (Measure.haar : Measure ℚ_[p]ˣ)

/-- Inverse transport of p-adic multiplicative Haar through the chosen square
branch.  Comparing this measure with ambient Haar on the branch source is the
remaining one-dimensional change-of-variables theorem. -/
noncomputable def padicUnitSquareIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (Rat.unitSquareIdentityChart ℚ_[p]).source :=
  Measure.map
    (Rat.unitSquareIdentityChart ℚ_[p]).toHomeomorphSourceTarget.symm
    (padicUnitSquareIdentityChartTargetMeasure p)

theorem map_padicUnitSquareIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (Rat.unitSquareIdentityChart ℚ_[p]).toHomeomorphSourceTarget
        (padicUnitSquareIdentityChartSourceMeasure p) =
      padicUnitSquareIdentityChartTargetMeasure p := by
  rw [padicUnitSquareIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (Rat.unitSquareIdentityChart ℚ_[p]).toHomeomorphSourceTarget.toMeasurableEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The p-adic horizontal target restriction is exactly the product of its
square coordinate and Spin-to-`SO` coordinate. -/
theorem map_padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure_split
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℚ_[p]).target
          (V.padicCliffordSpinCandidateIdentityChart p).target)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) =
      (padicUnitSquareIdentityChartTargetMeasure p).prod
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) := by
    exact Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite
      (Measure.comap Subtype.val (Measure.haar : Measure ℚ_[p]ˣ) :
        Measure (Rat.unitSquareIdentityChart ℚ_[p]).target) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (Rat.unitSquareIdentityChart ℚ_[p]).open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      (Measure.comap Subtype.val (V.padicInvariantDifferentialGroupMeasure p) :
        Measure (V.padicCliffordSpinCandidateIdentityChart p).target) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [map_comap_subtype_coe
      (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet]
    infer_instance
  rw [padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure,
    padicCliffordGeneralSpinHorizontalDifferentialProductMeasure,
    padicUnitSquareIdentityChartTargetMeasure,
    padicCliffordSpinCandidateIdentityChartTargetMeasure]
  exact map_setProd_comap_prod _ _
    (Rat.unitSquareIdentityChart ℚ_[p]).open_target.measurableSet
    (V.padicCliffordSpinCandidateIdentityChart p).open_target.measurableSet _ _

set_option backward.isDefEq.respectTransparency false in
/-- The p-adic horizontal source inverse transport splits exactly into the
one-dimensional square inverse transport and the existing Spin chart source
measure. -/
theorem map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_split
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℚ_[p]).source
          (V.padicCliffordSpinCandidateIdentityChart p).source)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      (padicUnitSquareIdentityChartSourceMeasure p).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
  let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
  let spinChart := V.padicCliffordSpinCandidateIdentityChart p
  let productChart := V.padicCliffordGeneralSpinHorizontalProductIdentityChart p
  let sourceSplit := Homeomorph.Set.prod squareChart.source spinChart.source
  let targetSplit := Homeomorph.Set.prod squareChart.target spinChart.target
  let componentChart := squareChart.toHomeomorphSourceTarget.prodCongr
    spinChart.toHomeomorphSourceTarget
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) := by
    exact Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite (padicUnitSquareIdentityChartTargetMeasure p) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [padicUnitSquareIdentityChartTargetMeasure,
      map_comap_subtype_coe squareChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite (padicUnitSquareIdentityChartSourceMeasure p) := by
    rw [padicUnitSquareIdentityChartSourceMeasure]
    exact squareChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe spinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  have hsourceMeasurable : Measurable sourceSplit := by
    have hfst : Measurable
        (fun x : (squareChart.source ×ˢ spinChart.source) =>
          (⟨x.1.1, x.2.1⟩ : squareChart.source)) :=
      Measurable.subtype_mk
        (measurable_fst.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.source ×ˢ spinChart.source) →
              ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p)))
    have hsnd : Measurable
        (fun x : (squareChart.source ×ˢ spinChart.source) =>
          (⟨x.1.2, x.2.2⟩ : spinChart.source)) :=
      Measurable.subtype_mk
        (measurable_snd.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.source ×ˢ spinChart.source) →
              ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p)))
    simpa only [sourceSplit, Homeomorph.Set.prod_apply] using hfst.prodMk hsnd
  have htargetMeasurable : Measurable targetSplit := by
    have hfst : Measurable
        (fun x : (squareChart.target ×ˢ spinChart.target) =>
          (⟨x.1.1, x.2.1⟩ : squareChart.target)) :=
      Measurable.subtype_mk
        (measurable_fst.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.target ×ˢ spinChart.target) →
              ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p])))
    have hsnd : Measurable
        (fun x : (squareChart.target ×ˢ spinChart.target) =>
          (⟨x.1.2, x.2.2⟩ : spinChart.target)) :=
      Measurable.subtype_mk
        (measurable_snd.comp
          (measurable_subtype_coe : Measurable
            (Subtype.val : (squareChart.target ×ˢ spinChart.target) →
              ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p])))
    simpa only [targetSplit, Homeomorph.Set.prod_apply] using hfst.prodMk hsnd
  have hcomponentMeasurable : Measurable componentChart :=
    componentChart.measurable
  have hcommute :
      componentChart ∘ sourceSplit =
        targetSplit ∘ productChart.toHomeomorphSourceTarget := by
    funext x
    rfl
  apply componentChart.toMeasurableEquiv.measurableEmbedding.map_injective
  calc
    Measure.map componentChart
        (Measure.map sourceSplit
          (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)) =
        Measure.map targetSplit
          (Measure.map productChart.toHomeomorphSourceTarget
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)) := by
      rw [Measure.map_map hcomponentMeasurable hsourceMeasurable,
        Measure.map_map htargetMeasurable
          productChart.toHomeomorphSourceTarget.measurable,
        hcommute]
    _ = Measure.map targetSplit
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) := by
      rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p]
    _ = (padicUnitSquareIdentityChartTargetMeasure p).prod
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      exact
        V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure_split p
    _ = (Measure.map squareChart.toHomeomorphSourceTarget
          (padicUnitSquareIdentityChartSourceMeasure p)).prod
        (Measure.map spinChart.toHomeomorphSourceTarget
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
      simp only [squareChart, spinChart,
        map_padicUnitSquareIdentityChartSourceMeasure,
        V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure]
    _ = Measure.map componentChart
        ((padicUnitSquareIdentityChartSourceMeasure p).prod
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
      simpa only [componentChart, Homeomorph.coe_prodCongr] using
        (Measure.map_prod_map
          (padicUnitSquareIdentityChartSourceMeasure p)
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)
          squareChart.toHomeomorphSourceTarget.measurable
          spinChart.toHomeomorphSourceTarget.measurable)

/-! ## Exact one-dimensional normalization -/

/-- Ambient real multiplicative Haar restricted to the chosen square-source
branch. -/
noncomputable def realUnitSquareIdentityChartAmbientSourceMeasure :
    Measure (Rat.unitSquareIdentityChart ℝ).source :=
  Measure.comap Subtype.val (Measure.haar : Measure ℝˣ)

/-- The exact real branchwise square change-of-variables statement still to
be proved.  Its orientation says inverse transport from the square target is
`|2|_∞` times ambient Haar on the injective source branch. -/
def RealUnitSquareBranchChangeOfVariables : Prop :=
  realUnitSquareIdentityChartSourceMeasure =
    rationalIdeleRealSquareModulus •
      realUnitSquareIdentityChartAmbientSourceMeasure

set_option backward.isDefEq.respectTransparency false in
/-- Once the one-dimensional real square identity is supplied, the complete
horizontal product chart has exactly that coefficient and no Spin or sheet
coefficient. -/
theorem realHorizontalProductSourceMeasure_split_of_squareChangeOfVariables
    (h : RealUnitSquareBranchChangeOfVariables) :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℝ).source
          V.realCliffordSpinCandidateIdentityChart.source)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      rationalIdeleRealSquareModulus •
        (realUnitSquareIdentityChartAmbientSourceMeasure.prod
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
  let spinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite
      V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe spinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
    rw [realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  rw [V.map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_split,
    h]
  change (((rationalIdeleRealSquareModulus : ℝ≥0) : ENNReal) •
      realUnitSquareIdentityChartAmbientSourceMeasure).prod
        V.realCliffordSpinCandidateIdentityChartSourceMeasure = _
  exact Measure.prod_smul_left _

/-- Ambient p-adic multiplicative Haar restricted to the chosen square-source
branch. -/
noncomputable def padicUnitSquareIdentityChartAmbientSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (Rat.unitSquareIdentityChart ℚ_[p]).source :=
  Measure.comap Subtype.val (Measure.haar : Measure ℚ_[p]ˣ)

/-- The exact p-adic branchwise square change-of-variables statement.  This
definition records the remaining local proposition without assuming it. -/
def PadicUnitSquareBranchChangeOfVariables
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  padicUnitSquareIdentityChartSourceMeasure p =
    rationalIdelePadicSquareModulus p •
      padicUnitSquareIdentityChartAmbientSourceMeasure p

set_option backward.isDefEq.respectTransparency false in
/-- A p-adic square-branch identity propagates to the full local horizontal
product chart with precisely its named modulus. -/
theorem padicHorizontalProductSourceMeasure_split_of_squareChangeOfVariables
    (p : ℕ) [Fact (Nat.Prime p)]
    (h : PadicUnitSquareBranchChangeOfVariables p) :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℚ_[p]).source
          (V.padicCliffordSpinCandidateIdentityChart p).source)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      rationalIdelePadicSquareModulus p •
        ((padicUnitSquareIdentityChartAmbientSourceMeasure p).prod
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
  let spinChart := V.padicCliffordSpinCandidateIdentityChart p
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe spinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_split p,
    h]
  change (((rationalIdelePadicSquareModulus p : ℝ≥0) : ENNReal) •
      padicUnitSquareIdentityChartAmbientSourceMeasure p).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) = _
  exact Measure.prod_smul_left _

end RationalQuadraticSpaceMatrix
