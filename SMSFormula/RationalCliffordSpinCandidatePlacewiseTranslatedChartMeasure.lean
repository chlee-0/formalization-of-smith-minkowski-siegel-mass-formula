import SMSFormula.RationalCliffordSpinCandidatePlacewiseChartMeasurePrecursor

/-!
# Translated placewise chart measures for the Spin candidate

The identity-centered Spin charts are translated by the group laws at the
real and p-adic places.  This file first proves the reusable topological
measure statement for a continuous homomorphism with one open local chart:

* left translation gives compatible source and target subtype homeomorphisms;
* the translated chart is still given by the original homomorphism;
* the target measure is the comap of one fixed left-invariant ambient measure;
* inverse chart transport defines the translated source measure;
* translated source measures agree exactly on every same-point overlap.

Specializing the ambient measure to the invariant-differential `SO` Haar
measure gives real and p-adic translated Spin chart measures.  This is local
gluing data; no ambient Spin measure is constructed here.  Nor is the
transported local measure identified with the absolute-value density of the
chosen Spin top form; that is a separate analytic change-of-variables step.
-/

noncomputable section

open MeasureTheory
open Topology

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- The left translate of the source of an identity-centered chart. -/
def source (e : OpenPartialHomeomorph G H) (g : G) : Set G :=
  {x | g⁻¹ * x ∈ e.source}

/-- The matching left translate of the target of a homomorphism chart. -/
def target (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G) : Set H :=
  {y | (f g)⁻¹ * y ∈ e.target}

omit [MeasurableSpace G] [BorelSpace G] [Group H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] in
theorem isOpen_source (e : OpenPartialHomeomorph G H) (g : G) :
    IsOpen (source e g) :=
  e.open_source.preimage (continuous_const.mul continuous_id)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H] in
theorem isOpen_target (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G) :
    IsOpen (target f e g) :=
  e.open_target.preimage (continuous_const.mul continuous_id)

theorem self_mem_source (e : OpenPartialHomeomorph G H)
    (hone : (1 : G) ∈ e.source) (g : G) : g ∈ source e g := by
  change g⁻¹ * g ∈ e.source
  simpa using hone

/-- Left multiplication identifies the identity source with its translate. -/
def sourceLeftHomeomorph (e : OpenPartialHomeomorph G H) (g : G) :
    e.source ≃ₜ source e g where
  toFun x := ⟨g * x.1, by
    change g⁻¹ * (g * x.1) ∈ e.source
    convert x.2 using 1
    simp⟩
  invFun x := ⟨g⁻¹ * x.1, x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Left multiplication identifies the identity target with its translate. -/
def targetLeftHomeomorph (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G) :
    e.target ≃ₜ target f e g where
  toFun x := ⟨f g * x.1, by
    change (f g)⁻¹ * (f g * x.1) ∈ e.target
    convert x.2 using 1
    simp⟩
  invFun x := ⟨(f g)⁻¹ * x.1, x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The identity chart translated compatibly in source and target. -/
def chart (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G) :
    source e g ≃ₜ target f e g :=
  (sourceLeftHomeomorph e g).symm.trans
    (e.toHomeomorphSourceTarget.trans (targetLeftHomeomorph f e g))

/-- When the identity chart is literally a homomorphism, every translated
chart is literally that same homomorphism on its translated source. -/
theorem chart_apply (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (g : G) (x : source e g) :
    (chart f e g x).1 = f x.1 := by
  simp only [chart, Homeomorph.trans_apply, sourceLeftHomeomorph,
    targetLeftHomeomorph]
  change f g * e (g⁻¹ * x.1) = f x.1
  rw [← congrFun hfe (g⁻¹ * x.1)]
  simp

/-- The translated chart has the translated target as its literal range
under the ambient homomorphism. -/
theorem range_pointMap (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (g : G) :
    Set.range (fun x : source e g ↦ f x.1) = target f e g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [chart_apply f e hfe g] using (chart f e g x).2
  · intro hy
    let y' : target f e g := ⟨y, hy⟩
    let x := (chart f e g).symm y'
    refine ⟨x, ?_⟩
    change f x.1 = y
    rw [← chart_apply f e hfe g x]
    exact congrArg Subtype.val ((chart f e g).apply_symm_apply y')

/-- The literal homomorphism restricted to a translated source is an open
embedding into the ambient target group. -/
theorem isOpenEmbedding_pointMap (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e) (g : G) :
    IsOpenEmbedding (fun x : source e g ↦ f x.1) := by
  have hchart : IsOpenEmbedding (chart f e g) :=
    (chart f e g).isOpenEmbedding
  have hsub : IsOpenEmbedding
      (Subtype.val : target f e g → H) :=
    (isOpen_target f e g).isOpenEmbedding_subtypeVal
  have hcomp := hsub.comp hchart
  have hfun : (fun x : source e g ↦ f x.1) =
      (Subtype.val ∘ chart f e g) := by
    funext x
    exact (chart_apply f e hfe g x).symm
  rw [hfun]
  exact hcomp

/-- Restrict an ambient measure to the translated chart target, expressed as
the exact subtype comap. -/
def targetMeasure (f : G →* H) (e : OpenPartialHomeomorph G H)
    (g : G) (μ : Measure H) : Measure (target f e g) :=
  Measure.comap Subtype.val μ

/-- Pull the translated target measure back through the exact translated
chart. -/
def sourceMeasure (f : G →* H) (e : OpenPartialHomeomorph G H)
    (g : G) (μ : Measure H) : Measure (source e g) :=
  Measure.map (chart f e g).symm (targetMeasure f e g μ)

/-- The target measure before translation. -/
def identityTargetMeasure (e : OpenPartialHomeomorph G H) (μ : Measure H) :
    Measure e.target :=
  Measure.comap Subtype.val μ

/-- The source measure before translation. -/
def identitySourceMeasure (e : OpenPartialHomeomorph G H) (μ : Measure H) :
    Measure e.source :=
  Measure.map e.toHomeomorphSourceTarget.symm (identityTargetMeasure e μ)

theorem map_sourceMeasure_chart (f : G →* H)
    (e : OpenPartialHomeomorph G H) (g : G) (μ : Measure H) :
    Measure.map (chart f e g) (sourceMeasure f e g μ) =
      targetMeasure f e g μ := by
  rw [sourceMeasure]
  exact MeasurableEquiv.map_map_symm (chart f e g).toMeasurableEquiv

theorem map_targetMeasure_subtype (f : G →* H)
    (e : OpenPartialHomeomorph G H) (g : G) (μ : Measure H) :
    Measure.map Subtype.val (targetMeasure f e g μ) =
      μ.restrict (target f e g) := by
  rw [targetMeasure]
  exact map_comap_subtype_coe (isOpen_target f e g).measurableSet μ

/-- The literal homomorphism sends every translated source measure to the
restriction of the fixed ambient measure to the matching translated target. -/
theorem map_sourceMeasure_pointMap (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (g : G) (μ : Measure H) :
    Measure.map (fun x : source e g ↦ f x.1) (sourceMeasure f e g μ) =
      μ.restrict (target f e g) := by
  calc
    Measure.map (fun x : source e g ↦ f x.1) (sourceMeasure f e g μ) =
        Measure.map Subtype.val
          (Measure.map (chart f e g) (sourceMeasure f e g μ)) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (chart f e g).measurable]
      congr 1
      funext x
      exact (chart_apply f e hfe g x).symm
    _ = Measure.map Subtype.val (targetMeasure f e g μ) := by
      rw [map_sourceMeasure_chart]
    _ = μ.restrict (target f e g) :=
      map_targetMeasure_subtype f e g μ

private theorem map_mulLeft_restrict_open
    (a : H) (μ : Measure H) [Measure.IsMulLeftInvariant μ]
    (U : Set H) (hU : IsOpen U) :
    Measure.map (Homeomorph.mulLeft a) (μ.restrict U) =
      μ.restrict {y | a⁻¹ * y ∈ U} := by
  let L := Homeomorph.mulLeft a
  let T : Set H := {y | a⁻¹ * y ∈ U}
  have hT : MeasurableSet T :=
    (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  calc
    Measure.map L (μ.restrict U) = (Measure.map L μ).restrict T := by
      symm
      rw [Measure.restrict_map L.continuous.measurable hT]
      congr 1
      ext x
      simp [L, T]
    _ = μ.restrict T := by
      have hmap : Measure.map L μ = μ := by
        simpa only [L, Homeomorph.coe_mulLeft] using
          (Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := μ) a)
      rw [hmap]

/-- The translated target measure is exactly the left translate of the
identity target measure. -/
theorem map_identityTargetMeasure_targetLeftHomeomorph
    (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ] :
    Measure.map (targetLeftHomeomorph f e g) (identityTargetMeasure e μ) =
      targetMeasure f e g μ := by
  let j : target f e g → H := Subtype.val
  have hj : MeasurableEmbedding j :=
    (isOpen_target f e g).isOpenEmbedding_subtypeVal.measurableEmbedding
  apply hj.map_injective
  calc
    Measure.map j
        (Measure.map (targetLeftHomeomorph f e g) (identityTargetMeasure e μ)) =
        Measure.map (Homeomorph.mulLeft (f g))
          (Measure.map (Subtype.val : e.target → H) (identityTargetMeasure e μ)) := by
      rw [Measure.map_map hj.measurable
        (targetLeftHomeomorph f e g).measurable,
        Measure.map_map (Homeomorph.mulLeft (f g)).measurable
          continuous_subtype_val.measurable]
      congr 1
    _ = Measure.map (Homeomorph.mulLeft (f g))
        (μ.restrict e.target) := by
      rw [identityTargetMeasure,
        map_comap_subtype_coe e.open_target.measurableSet]
    _ = μ.restrict (target f e g) :=
      map_mulLeft_restrict_open (f g) μ e.target e.open_target
    _ = Measure.map j (targetMeasure f e g μ) := by
      rw [map_targetMeasure_subtype]

/-- The translated source measure is exactly the left translate of the
identity source measure. -/
theorem map_identitySourceMeasure_sourceLeftHomeomorph
    (f : G →* H) (e : OpenPartialHomeomorph G H) (g : G)
    (μ : Measure H) [Measure.IsMulLeftInvariant μ] :
    Measure.map (sourceLeftHomeomorph e g) (identitySourceMeasure e μ) =
      sourceMeasure f e g μ := by
  have hchart : MeasurableEmbedding (chart f e g) :=
    (chart f e g).toMeasurableEquiv.measurableEmbedding
  apply hchart.map_injective
  calc
    Measure.map (chart f e g)
        (Measure.map (sourceLeftHomeomorph e g) (identitySourceMeasure e μ)) =
        Measure.map (targetLeftHomeomorph f e g)
          (Measure.map e.toHomeomorphSourceTarget (identitySourceMeasure e μ)) := by
      rw [Measure.map_map (chart f e g).measurable
        (sourceLeftHomeomorph e g).measurable,
        Measure.map_map (targetLeftHomeomorph f e g).measurable
          e.toHomeomorphSourceTarget.measurable]
      congr 1
      funext x
      apply Subtype.ext
      simp only [Function.comp_apply, chart, Homeomorph.trans_apply]
      rw [(sourceLeftHomeomorph e g).symm_apply_apply]
    _ = Measure.map (targetLeftHomeomorph f e g) (identityTargetMeasure e μ) := by
      rw [identitySourceMeasure]
      congr 1
      exact MeasurableEquiv.map_map_symm
        e.toHomeomorphSourceTarget.toMeasurableEquiv
    _ = targetMeasure f e g μ :=
      map_identityTargetMeasure_targetLeftHomeomorph f e g μ
    _ = Measure.map (chart f e g) (sourceMeasure f e g μ) := by
      rw [map_sourceMeasure_chart]

/-- Intrinsically, a translated source measure is the comap of the one
ambient measure through the literal restricted homomorphism. -/
theorem sourceMeasure_eq_comap_pointMap (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (g : G) (μ : Measure H) :
    sourceMeasure f e g μ =
      Measure.comap (fun x : source e g ↦ f x.1) μ := by
  let j : source e g → H := fun x ↦ f x.1
  have hj : MeasurableEmbedding j :=
    (isOpenEmbedding_pointMap f e hfe g).measurableEmbedding
  apply hj.map_injective
  rw [map_sourceMeasure_pointMap f e hfe g μ, hj.map_comap]
  congr 1
  exact (range_pointMap f e hfe g).symm

/-- The same-point overlap of two translated sources. -/
def sourceOverlap (e : OpenPartialHomeomorph G H) (g h : G) : Set G :=
  source e g ∩ source e h

abbrev SourceOverlap (e : OpenPartialHomeomorph G H) (g h : G) :=
  {x // x ∈ sourceOverlap e g h}

def sourceOverlapToLeft (e : OpenPartialHomeomorph G H) (g h : G) :
    SourceOverlap e g h → source e g :=
  fun x ↦ ⟨x.1, x.2.1⟩

def sourceOverlapToRight (e : OpenPartialHomeomorph G H) (g h : G) :
    SourceOverlap e g h → source e h :=
  fun x ↦ ⟨x.1, x.2.2⟩

private def sourceOverlapWithinLeft (e : OpenPartialHomeomorph G H)
    (g h : G) : Set (source e g) :=
  Subtype.val ⁻¹' source e h

private def sourceOverlapWithinRight (e : OpenPartialHomeomorph G H)
    (g h : G) : Set (source e h) :=
  Subtype.val ⁻¹' source e g

private def sourceOverlapLeftHomeomorph (e : OpenPartialHomeomorph G H)
    (g h : G) : SourceOverlap e g h ≃ₜ sourceOverlapWithinLeft e g h where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def sourceOverlapRightHomeomorph (e : OpenPartialHomeomorph G H)
    (g h : G) : SourceOverlap e g h ≃ₜ sourceOverlapWithinRight e g h where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private theorem measurableEmbedding_sourceOverlapToLeft
    (e : OpenPartialHomeomorph G H) (g h : G) :
    MeasurableEmbedding (sourceOverlapToLeft e g h) := by
  let E := sourceOverlapLeftHomeomorph e g h
  have hE : MeasurableEmbedding E := E.toMeasurableEquiv.measurableEmbedding
  have hU : IsOpen (sourceOverlapWithinLeft e g h) :=
    (isOpen_source e h).preimage continuous_subtype_val
  have hi : MeasurableEmbedding
      (Subtype.val : sourceOverlapWithinLeft e g h → source e g) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  simpa [E, Function.comp_def, sourceOverlapLeftHomeomorph,
    sourceOverlapToLeft] using hi.comp hE

private theorem measurableEmbedding_sourceOverlapToRight
    (e : OpenPartialHomeomorph G H) (g h : G) :
    MeasurableEmbedding (sourceOverlapToRight e g h) := by
  let E := sourceOverlapRightHomeomorph e g h
  have hE : MeasurableEmbedding E := E.toMeasurableEquiv.measurableEmbedding
  have hU : IsOpen (sourceOverlapWithinRight e g h) :=
    (isOpen_source e g).preimage continuous_subtype_val
  have hi : MeasurableEmbedding
      (Subtype.val : sourceOverlapWithinRight e g h → source e h) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  simpa [E, Function.comp_def, sourceOverlapRightHomeomorph,
    sourceOverlapToRight] using hi.comp hE

/-- The measures induced by two translated homomorphism charts agree exactly
after comap to their same-point source overlap. -/
theorem comap_sourceMeasure_overlap (f : G →* H)
    (e : OpenPartialHomeomorph G H) (hfe : (f : G → H) = e)
    (g h : G) (μ : Measure H) :
    Measure.comap (sourceOverlapToLeft e g h) (sourceMeasure f e g μ) =
      Measure.comap (sourceOverlapToRight e g h) (sourceMeasure f e h μ) := by
  let i := sourceOverlapToLeft e g h
  let j := sourceOverlapToRight e g h
  let fg : source e g → H := fun x ↦ f x.1
  let fh : source e h → H := fun x ↦ f x.1
  have hi : MeasurableEmbedding i := measurableEmbedding_sourceOverlapToLeft e g h
  have hj : MeasurableEmbedding j := measurableEmbedding_sourceOverlapToRight e g h
  have hfg : MeasurableEmbedding fg :=
    (isOpenEmbedding_pointMap f e hfe g).measurableEmbedding
  have hfh : MeasurableEmbedding fh :=
    (isOpenEmbedding_pointMap f e hfe h).measurableEmbedding
  rw [sourceMeasure_eq_comap_pointMap f e hfe g μ,
    sourceMeasure_eq_comap_pointMap f e hfe h μ]
  calc
    Measure.comap i (Measure.comap fg μ) =
        Measure.comap (fg ∘ i) μ :=
      Measure.comap_comap
        (fun s hs ↦ hi.measurableSet_image.2 hs) hfg.injective
        (fun s hs ↦ hfg.measurableSet_image.2 hs) μ
    _ = Measure.comap (fh ∘ j) μ := by
      rfl
    _ = Measure.comap j (Measure.comap fh μ) := by
      symm
      exact Measure.comap_comap
        (fun s hs ↦ hj.measurableSet_image.2 hs) hfh.injective
        (fun s hs ↦ hfh.measurableSet_image.2 hs) μ

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

open MeasureTheory.TranslatedHomChart

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance translatedChartRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance translatedChartRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance translatedChartPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance translatedChartPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

local instance translatedChartRealCarrierBorelSpace :
    BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩

local instance translatedChartPadicCarrierBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

/-! ## Real translated chart measures -/

abbrev RealCliffordSpinCandidateTranslatedChartSource
    (g : V.RealCliffordSpinCandidateGroup) :=
  source V.realCliffordSpinCandidateIdentityChart g

abbrev RealCliffordSpinCandidateTranslatedChartTarget
    (g : V.RealCliffordSpinCandidateGroup) :=
  target V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g

noncomputable def realCliffordSpinCandidateTranslatedChart
    (g : V.RealCliffordSpinCandidateGroup) :
    V.RealCliffordSpinCandidateTranslatedChartSource g ≃ₜ
      V.RealCliffordSpinCandidateTranslatedChartTarget g :=
  chart V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g

theorem realCliffordSpinCandidateTranslatedChart_apply
    (g : V.RealCliffordSpinCandidateGroup)
    (x : V.RealCliffordSpinCandidateTranslatedChartSource g) :
    (V.realCliffordSpinCandidateTranslatedChart g x).1 =
      V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1 :=
  chart_apply V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe g x

noncomputable def realCliffordSpinCandidateTranslatedChartTargetMeasure
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure (V.RealCliffordSpinCandidateTranslatedChartTarget g) :=
  targetMeasure V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g
    V.realInvariantDifferentialGroupMeasure

noncomputable def realCliffordSpinCandidateTranslatedChartSourceMeasure
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure (V.RealCliffordSpinCandidateTranslatedChartSource g) :=
  sourceMeasure V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart g
    V.realInvariantDifferentialGroupMeasure

@[simp]
theorem self_mem_realCliffordSpinCandidateTranslatedChartSource
    (g : V.RealCliffordSpinCandidateGroup) :
    g ∈ source V.realCliffordSpinCandidateIdentityChart g :=
  self_mem_source V.realCliffordSpinCandidateIdentityChart
    V.one_mem_realCliffordSpinCandidateIdentityChart_source g

set_option backward.isDefEq.respectTransparency false in
/-- Left translation transports the chosen identity source measure exactly to
the source measure of the real chart centered at `g`. -/
theorem map_realCliffordSpinCandidateIdentityChartSourceMeasure_left
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure.map
        (sourceLeftHomeomorph V.realCliffordSpinCandidateIdentityChart g)
        V.realCliffordSpinCandidateIdentityChartSourceMeasure =
      V.realCliffordSpinCandidateTranslatedChartSourceMeasure g := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  simpa [realCliffordSpinCandidateIdentityChartSourceMeasure,
    realCliffordSpinCandidateIdentityChartTargetMeasure,
    realCliffordSpinCandidateTranslatedChartSourceMeasure,
    identitySourceMeasure, identityTargetMeasure] using
    (map_identitySourceMeasure_sourceLeftHomeomorph
      (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
      V.realCliffordSpinCandidateToSpecialOrthogonalHom
      V.realCliffordSpinCandidateIdentityChart g
      V.realInvariantDifferentialGroupMeasure)

set_option backward.isDefEq.respectTransparency false in
/-- The analogous exact target-side translation statement. -/
theorem map_realCliffordSpinCandidateIdentityChartTargetMeasure_left
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure.map
        (targetLeftHomeomorph
          V.realCliffordSpinCandidateToSpecialOrthogonalHom
          V.realCliffordSpinCandidateIdentityChart g)
        V.realCliffordSpinCandidateIdentityChartTargetMeasure =
      V.realCliffordSpinCandidateTranslatedChartTargetMeasure g := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  simpa [realCliffordSpinCandidateIdentityChartTargetMeasure,
    realCliffordSpinCandidateTranslatedChartTargetMeasure,
    identityTargetMeasure] using
    (map_identityTargetMeasure_targetLeftHomeomorph
      (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
      V.realCliffordSpinCandidateToSpecialOrthogonalHom
      V.realCliffordSpinCandidateIdentityChart g
      V.realInvariantDifferentialGroupMeasure)

set_option backward.isDefEq.respectTransparency false in
theorem map_realCliffordSpinCandidateTranslatedChartSourceMeasure_pointMap
    (g : V.RealCliffordSpinCandidateGroup) :
    Measure.map
        (fun x : V.RealCliffordSpinCandidateTranslatedChartSource g ↦
          V.realCliffordSpinCandidateToSpecialOrthogonalHom x.1)
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure g) =
      V.realInvariantDifferentialGroupMeasure.restrict
        (target V.realCliffordSpinCandidateToSpecialOrthogonalHom
          V.realCliffordSpinCandidateIdentityChart g) :=
  map_sourceMeasure_pointMap
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe g
    V.realInvariantDifferentialGroupMeasure

set_option backward.isDefEq.respectTransparency false in
theorem comap_realCliffordSpinCandidateTranslatedChartSourceMeasure_overlap
    (g h : V.RealCliffordSpinCandidateGroup) :
    Measure.comap
        (sourceOverlapToLeft V.realCliffordSpinCandidateIdentityChart g h)
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure g) =
      Measure.comap
        (sourceOverlapToRight V.realCliffordSpinCandidateIdentityChart g h)
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure h) :=
  comap_sourceMeasure_overlap
    (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    V.realCliffordSpinCandidateIdentityChart
    V.realCliffordSpinCandidateIdentityChart_coe g h
    V.realInvariantDifferentialGroupMeasure

/-! ## P-adic translated chart measures -/

abbrev PadicCliffordSpinCandidateTranslatedChartSource
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :=
  source (V.padicCliffordSpinCandidateIdentityChart p) g

abbrev PadicCliffordSpinCandidateTranslatedChartTarget
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :=
  target (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g

noncomputable def padicCliffordSpinCandidateTranslatedChart
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    V.PadicCliffordSpinCandidateTranslatedChartSource p g ≃ₜ
      V.PadicCliffordSpinCandidateTranslatedChartTarget p g :=
  chart (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g

theorem padicCliffordSpinCandidateTranslatedChart_apply
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p)
    (x : V.PadicCliffordSpinCandidateTranslatedChartSource p g) :
    (V.padicCliffordSpinCandidateTranslatedChart p g x).1 =
      V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1 :=
  chart_apply (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p) g x

noncomputable def padicCliffordSpinCandidateTranslatedChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure (V.PadicCliffordSpinCandidateTranslatedChartTarget p g) :=
  targetMeasure (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g
    (V.padicInvariantDifferentialGroupMeasure p)

noncomputable def padicCliffordSpinCandidateTranslatedChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure (V.PadicCliffordSpinCandidateTranslatedChartSource p g) :=
  sourceMeasure (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p) g
    (V.padicInvariantDifferentialGroupMeasure p)

@[simp]
theorem self_mem_padicCliffordSpinCandidateTranslatedChartSource
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    g ∈ source (V.padicCliffordSpinCandidateIdentityChart p) g :=
  self_mem_source (V.padicCliffordSpinCandidateIdentityChart p)
    (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p) g

set_option backward.isDefEq.respectTransparency false in
/-- Left translation transports the chosen p-adic identity source measure
exactly to the source measure of the chart centered at `g`. -/
theorem map_padicCliffordSpinCandidateIdentityChartSourceMeasure_left
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure.map
        (sourceLeftHomeomorph
          (V.padicCliffordSpinCandidateIdentityChart p) g)
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) =
      V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g := by
  letI : Measure.IsHaarMeasure
      (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  simpa [padicCliffordSpinCandidateIdentityChartSourceMeasure,
    padicCliffordSpinCandidateIdentityChartTargetMeasure,
    padicCliffordSpinCandidateTranslatedChartSourceMeasure,
    identitySourceMeasure, identityTargetMeasure] using
    (map_identitySourceMeasure_sourceLeftHomeomorph
      (G := V.PadicCliffordSpinCandidateGroup p)
      (H := V.specialOrthogonalMatrixGroup ℚ_[p])
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart p) g
      (V.padicInvariantDifferentialGroupMeasure p))

set_option backward.isDefEq.respectTransparency false in
/-- The analogous exact p-adic target-side translation statement. -/
theorem map_padicCliffordSpinCandidateIdentityChartTargetMeasure_left
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure.map
        (targetLeftHomeomorph
          (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
          (V.padicCliffordSpinCandidateIdentityChart p) g)
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) =
      V.padicCliffordSpinCandidateTranslatedChartTargetMeasure p g := by
  letI : Measure.IsHaarMeasure
      (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  simpa [padicCliffordSpinCandidateIdentityChartTargetMeasure,
    padicCliffordSpinCandidateTranslatedChartTargetMeasure,
    identityTargetMeasure] using
    (map_identityTargetMeasure_targetLeftHomeomorph
      (G := V.PadicCliffordSpinCandidateGroup p)
      (H := V.specialOrthogonalMatrixGroup ℚ_[p])
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart p) g
      (V.padicInvariantDifferentialGroupMeasure p))

set_option backward.isDefEq.respectTransparency false in
theorem map_padicCliffordSpinCandidateTranslatedChartSourceMeasure_pointMap
    (p : ℕ) [Fact (Nat.Prime p)] (g : V.PadicCliffordSpinCandidateGroup p) :
    Measure.map
        (fun x : V.PadicCliffordSpinCandidateTranslatedChartSource p g ↦
          V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.1)
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g) =
      (V.padicInvariantDifferentialGroupMeasure p).restrict
        (target (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
          (V.padicCliffordSpinCandidateIdentityChart p) g) :=
  map_sourceMeasure_pointMap
    (G := V.PadicCliffordSpinCandidateGroup p)
    (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p) g
    (V.padicInvariantDifferentialGroupMeasure p)

set_option backward.isDefEq.respectTransparency false in
theorem comap_padicCliffordSpinCandidateTranslatedChartSourceMeasure_overlap
    (p : ℕ) [Fact (Nat.Prime p)]
    (g h : V.PadicCliffordSpinCandidateGroup p) :
    Measure.comap
        (sourceOverlapToLeft
          (V.padicCliffordSpinCandidateIdentityChart p) g h)
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p g) =
      Measure.comap
        (sourceOverlapToRight
          (V.padicCliffordSpinCandidateIdentityChart p) g h)
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p h) :=
  comap_sourceMeasure_overlap
    (G := V.PadicCliffordSpinCandidateGroup p)
    (H := V.specialOrthogonalMatrixGroup ℚ_[p])
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicCliffordSpinCandidateIdentityChart p)
    (V.padicCliffordSpinCandidateIdentityChart_coe p) g h
    (V.padicInvariantDifferentialGroupMeasure p)

end RationalQuadraticSpaceMatrix
