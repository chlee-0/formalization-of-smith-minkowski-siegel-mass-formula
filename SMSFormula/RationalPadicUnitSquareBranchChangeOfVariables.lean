import SMSFormula.RationalCliffordGeneralSpinLocalDifferentialSquareFactor

/-!
# Branchwise p-adic unit-square change of variables

The global square map on `Q_p^*` has two algebraic sheets.  Its pushforward
onto the open square subgroup has scalar two at odd places and scalar four at
the dyadic place.  Restriction to the chosen identity chart splits that global
pushforward into two equal translated sheets.  Thus the inverse transport on
one sheet has coefficient one at odd places and `2^-1` at the dyadic place.

This is the isolated one-dimensional input required by the horizontal local
`GSpin` differential chart.  No Spin, detector, or restricted-product sheet
coefficient occurs here.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace MeasureTheory.TranslatedHomChart

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- Restrict a globally normalized two-sheet pushforward to the identity
chart.  The full target preimage is the disjoint union of the chart source and
its kernel translate, and left invariance gives the two sheets equal mass.
Thus the global range scalar is exactly twice the one-branch scalar. -/
theorem two_smul_map_identityChart_comap_eq_smul_comap_of_rangeRestrict
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hf : Continuous f) (hfe : (f : G → H) = e)
    (hrange : IsOpen (f.range : Set H))
    (k : G) (hk : f k = 1) (hkone : k ≠ 1)
    (hker : ∀ x : G, f x = 1 → x = 1 ∨ x = k)
    (μ : Measure G) [Measure.IsMulLeftInvariant μ] (ν : Measure H)
    (q : NNReal)
    (hglobal : Measure.map f.rangeRestrict μ =
      q • Measure.comap f.range.subtype ν) :
    (2 : NNReal) •
        Measure.map e.toHomeomorphSourceTarget
          (Measure.comap (Subtype.val : e.source → G) μ) =
      q • Measure.comap (Subtype.val : e.target → H) ν := by
  have hfmeas : Measurable f := hf.measurable
  have hsourceMeas : MeasurableSet e.source := e.open_source.measurableSet
  have htargetMeas : MeasurableSet e.target := e.open_target.measurableSet
  have htranslateMeas : MeasurableSet (source e k) :=
    (isOpen_source e k).measurableSet
  have hpre : f ⁻¹' e.target = e.source ∪ source e k :=
    preimage_target_eq_source_union_of_two_point_kernel f e hfe k hk hker
  have hdisj : Disjoint e.source (source e k) :=
    disjoint_source_translate_of_kernel_point f e hfe k hk hkone
  have hmul :
      Measure.map (Homeomorph.mulLeft k) (μ.restrict e.source) =
        μ.restrict (source e k) := by
    calc
      Measure.map (Homeomorph.mulLeft k) (μ.restrict e.source) =
          (Measure.map (Homeomorph.mulLeft k) μ).restrict (source e k) := by
        symm
        rw [Measure.restrict_map (Homeomorph.mulLeft k).measurable htranslateMeas]
        congr 1
        ext x
        simp [source]
      _ = μ.restrict (source e k) := by
        have hmap : Measure.map (Homeomorph.mulLeft k) μ = μ := by
          simpa only [Homeomorph.coe_mulLeft] using
            (Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := μ) k)
        rw [hmap]
  have hmapTranslate :
      Measure.map f (μ.restrict (source e k)) =
        Measure.map f (μ.restrict e.source) := by
    rw [← hmul, Measure.map_map hfmeas (Homeomorph.mulLeft k).measurable]
    congr 1
    funext x
    simp [hk]
  have htwoAmbient :
      (Measure.map f μ).restrict e.target =
        (2 : NNReal) • Measure.map f (μ.restrict e.source) := by
    calc
      (Measure.map f μ).restrict e.target =
          Measure.map f (μ.restrict (f ⁻¹' e.target)) :=
        Measure.restrict_map hfmeas htargetMeas
      _ = Measure.map f (μ.restrict (e.source ∪ source e k)) := by rw [hpre]
      _ = Measure.map f
          (μ.restrict e.source + μ.restrict (source e k)) := by
        rw [Measure.restrict_union hdisj htranslateMeas]
      _ = Measure.map f (μ.restrict e.source) +
          Measure.map f (μ.restrict (source e k)) := by
        exact Measure.map_add _ _ hfmeas
      _ = Measure.map f (μ.restrict e.source) +
          Measure.map f (μ.restrict e.source) := by rw [hmapTranslate]
      _ = (2 : NNReal) • Measure.map f (μ.restrict e.source) := by
        ext A hA
        rw [Measure.add_apply, Measure.smul_apply]
        change _ + _ = (2 : ENNReal) * _
        rw [two_mul]
  have htargetSubset : e.target ⊆ (f.range : Set H) := by
    intro y hy
    rw [← e.image_source_eq_target] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, congrFun hfe x⟩
  have hambient : Measure.map f μ = q • ν.restrict (f.range : Set H) := by
    have hfr : Measurable f.rangeRestrict := Measurable.subtype_mk hfmeas
    calc
      Measure.map f μ = Measure.map f.range.subtype
          (Measure.map f.rangeRestrict μ) := by
        symm
        change Measure.map (Subtype.val : f.range → H)
          (Measure.map f.rangeRestrict μ) = Measure.map f μ
        rw [Measure.map_map continuous_subtype_val.measurable hfr]
        rfl
      _ = Measure.map f.range.subtype
          (q • Measure.comap f.range.subtype ν) := congrArg _ hglobal
      _ = q • Measure.map f.range.subtype
          (Measure.comap f.range.subtype ν) := by rw [Measure.map_smul]
      _ = q • ν.restrict (f.range : Set H) := by
        congr 1
        exact map_comap_subtype_coe hrange.measurableSet ν
  have hrestricted :
      (Measure.map f μ).restrict e.target = q • ν.restrict e.target := by
    rw [hambient, Measure.restrict_smul,
      Measure.restrict_restrict htargetMeas]
    congr 2
    exact Set.inter_eq_left.mpr htargetSubset
  let j : e.target → H := Subtype.val
  have hj : MeasurableEmbedding j :=
    e.open_target.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hsourcePush :
      Measure.map (j ∘ e.toHomeomorphSourceTarget)
          (Measure.comap (Subtype.val : e.source → G) μ) =
        Measure.map f (μ.restrict e.source) := by
    calc
      Measure.map (j ∘ e.toHomeomorphSourceTarget)
          (Measure.comap (Subtype.val : e.source → G) μ) =
          Measure.map (fun x : e.source => f x.1)
            (Measure.comap (Subtype.val : e.source → G) μ) := by
        congr 1
        funext x
        change e x.1 = f x.1
        exact (congrFun hfe x).symm
      _ = Measure.map f
          (Measure.map (Subtype.val : e.source → G)
            (Measure.comap (Subtype.val : e.source → G) μ)) := by
        symm
        rw [Measure.map_map hfmeas continuous_subtype_val.measurable]
        rfl
      _ = Measure.map f (μ.restrict e.source) := by
        rw [map_comap_subtype_coe hsourceMeas]
  have htargetPush :
      Measure.map j (Measure.comap (Subtype.val : e.target → H) ν) =
        ν.restrict e.target :=
    map_comap_subtype_coe htargetMeas ν
  apply hj.map_injective
  calc
    Measure.map j
        ((2 : NNReal) • Measure.map e.toHomeomorphSourceTarget
          (Measure.comap (Subtype.val : e.source → G) μ)) =
        (2 : NNReal) • Measure.map f (μ.restrict e.source) := by
      rw [Measure.map_smul, Measure.map_map hj.measurable
        e.toHomeomorphSourceTarget.measurable, hsourcePush]
    _ = (Measure.map f μ).restrict e.target := htwoAmbient.symm
    _ = q • ν.restrict e.target := hrestricted
    _ = Measure.map j
        (q • Measure.comap (Subtype.val : e.target → H) ν) := by
      rw [Measure.map_smul, htargetPush]

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 1600000

noncomputable local instance padicSquareBranchMeasurableSpace
    (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance padicSquareBranchBorelSpace
    (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance padicSquareBranchSecondCountable
    (p : ℕ) [Fact p.Prime] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem two_smul_measure_injective
    {alpha : Type*} [MeasurableSpace alpha] {mu nu : Measure alpha}
    (h : (2 : NNReal) • mu = (2 : NNReal) • nu) : mu = nu := by
  ext A hA
  have h' := congrArg (fun m : Measure alpha => m A) h
  change ((2 : NNReal) • mu) A = ((2 : NNReal) • nu) A at h'
  rw [Measure.smul_apply, Measure.smul_apply] at h'
  apply (ENNReal.mul_left_inj (c := (2 : ENNReal)) (by norm_num) (by norm_num)).mp
  simpa [mul_comm] using h'

private theorem two_smul_map_padicUnitSquareIdentityChartAmbientSourceMeasure
    (p : ℕ) [Fact p.Prime] (q : NNReal)
    (hglobal :
      Measure.map (Rat.unitSquareMonoidHom ℚ_[p]).rangeRestrict
          (Measure.haar : Measure ℚ_[p]ˣ) =
        q • Measure.comap (Rat.unitSquareMonoidHom ℚ_[p]).range.subtype
          (Measure.haar : Measure ℚ_[p]ˣ)) :
    (2 : NNReal) •
        Measure.map
          (Rat.unitSquareIdentityChart ℚ_[p]).toHomeomorphSourceTarget
          (padicUnitSquareIdentityChartAmbientSourceMeasure p) =
      q • padicUnitSquareIdentityChartTargetMeasure p := by
  apply
    MeasureTheory.TranslatedHomChart.two_smul_map_identityChart_comap_eq_smul_comap_of_rangeRestrict
      (Rat.unitSquareMonoidHom ℚ_[p])
      (Rat.unitSquareIdentityChart ℚ_[p])
      (continuous_pow 2)
      (Rat.unitSquareIdentityChart_coe ℚ_[p])
      (by
        rw [Rat.unitSquareMonoidHom_range_eq_square p]
        exact Rat.isOpen_square_padicUnitsSubgroup p)
      (-1 : ℚ_[p]ˣ)
      (Rat.unitSquareMonoidHom_neg_one p)
      (Rat.neg_one_ne_one_padicUnit p)
      (Rat.eq_one_or_neg_one_of_unitSquareMonoidHom_eq_one p)
      (Measure.haar : Measure ℚ_[p]ˣ)
      (Measure.haar : Measure ℚ_[p]ˣ)
      q hglobal

/-- At an odd p-adic place, inverse square transport on the chosen identity
sheet is exactly ambient multiplicative Haar restricted to that sheet. -/
theorem padicUnitSquareBranchChangeOfVariables_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    PadicUnitSquareBranchChangeOfVariables p := by
  let chart := Rat.unitSquareIdentityChart ℚ_[p]
  have htwo :
      (2 : NNReal) •
          Measure.map chart.toHomeomorphSourceTarget
            (padicUnitSquareIdentityChartAmbientSourceMeasure p) =
        (2 : NNReal) • padicUnitSquareIdentityChartTargetMeasure p :=
    two_smul_map_padicUnitSquareIdentityChartAmbientSourceMeasure p 2
      (Rat.map_unitSquareMonoidHom_rangeRestrict_eq_two_smul_comap_of_ne_two p hp)
  have hbranch :
      Measure.map chart.toHomeomorphSourceTarget
          (padicUnitSquareIdentityChartAmbientSourceMeasure p) =
        padicUnitSquareIdentityChartTargetMeasure p :=
    two_smul_measure_injective htwo
  rw [PadicUnitSquareBranchChangeOfVariables,
    rationalIdelePadicSquareModulus_eq_one_of_ne_two p hp, one_smul]
  apply chart.toHomeomorphSourceTarget.measurableEmbedding.map_injective
  dsimp only [chart]
  rw [map_padicUnitSquareIdentityChartSourceMeasure]
  exact hbranch.symm

/-- At the dyadic place, inverse square transport on the chosen identity
sheet is one half of ambient multiplicative Haar restricted to that sheet. -/
theorem padicUnitSquareBranchChangeOfVariables_two :
    PadicUnitSquareBranchChangeOfVariables 2 := by
  let chart := Rat.unitSquareIdentityChart ℚ_[2]
  have htwo :
      (2 : NNReal) •
          Measure.map chart.toHomeomorphSourceTarget
            (padicUnitSquareIdentityChartAmbientSourceMeasure 2) =
        (4 : NNReal) • padicUnitSquareIdentityChartTargetMeasure 2 :=
    two_smul_map_padicUnitSquareIdentityChartAmbientSourceMeasure 2 4
      Rat.map_unitSquareMonoidHom_rangeRestrict_two_eq_four_smul_comap
  have hbranch :
      Measure.map chart.toHomeomorphSourceTarget
          (padicUnitSquareIdentityChartAmbientSourceMeasure 2) =
        (2 : NNReal) • padicUnitSquareIdentityChartTargetMeasure 2 := by
    apply two_smul_measure_injective
    calc
      (2 : NNReal) •
          Measure.map chart.toHomeomorphSourceTarget
            (padicUnitSquareIdentityChartAmbientSourceMeasure 2) =
          (4 : NNReal) • padicUnitSquareIdentityChartTargetMeasure 2 := htwo
      _ = (2 : NNReal) •
          ((2 : NNReal) • padicUnitSquareIdentityChartTargetMeasure 2) := by
        rw [smul_smul]
        norm_num
  rw [PadicUnitSquareBranchChangeOfVariables,
    rationalIdelePadicSquareModulus_two]
  apply chart.toHomeomorphSourceTarget.measurableEmbedding.map_injective
  dsimp only [chart]
  rw [map_padicUnitSquareIdentityChartSourceMeasure, Measure.map_smul,
    hbranch, smul_smul]
  norm_num

/-- The exact branchwise square change of variables at every p-adic place. -/
theorem padicUnitSquareBranchChangeOfVariables
    (p : ℕ) [Fact p.Prime] :
    PadicUnitSquareBranchChangeOfVariables p := by
  by_cases hp : p = 2
  · subst p
    exact padicUnitSquareBranchChangeOfVariables_two
  · exact padicUnitSquareBranchChangeOfVariables_of_ne_two p hp

end RationalQuadraticSpaceMatrix
