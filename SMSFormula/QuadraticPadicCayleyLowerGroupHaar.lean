import SMSFormula.QuadraticPadicCayleyProductSourceHaar

/-! Lower side on the lower group. The lower Cayley density times the repository
lower coordinate measure, times horizontal unit Haar, is transported through the
lower identity Cayley chart to the repository lower group Haar times
horizontal unit Haar (existing chart recovery for the lower form). General
measure-theoretic lemmas: comaps along measurable embeddings stay sigma-finite,
and lintegrals against a product measure over a subset of (range of an
embedding) x everything pull back to the comap product measure. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

/-- Pulling a sigma-finite measure back along a measurable embedding keeps it
sigma-finite. -/
theorem MeasurableEmbedding.sigmaFinite_comap {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {i : α → β} (hi : MeasurableEmbedding i) (μ : Measure β)
    [SigmaFinite μ] : SigmaFinite (μ.comap i) :=
  ⟨⟨{ set := fun k ↦ i ⁻¹' spanningSets μ k
      set_mem := fun _ ↦ trivial
      finite := fun k ↦ by
        rw [hi.comap_apply]
        exact (measure_mono (image_preimage_subset _ _)).trans_lt (measure_spanningSets_lt_top μ k)
      spanning := by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ] }⟩⟩

/-- Lintegrals against a product measure over a subset of (range i) × everything
pull back to the product of the comap measure. No measurability of the set or
the integrand is needed. -/
theorem MeasurableEmbedding.setLIntegral_prod_comap {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {i : γ → α} (hi : MeasurableEmbedding i)
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] [SFinite (μ.comap i)]
    {T : Set (α × β)} (hT : T ⊆ range i ×ˢ univ) (K : α × β → ℝ≥0∞) :
    ∫⁻ x in T, K x ∂(μ.prod ν) =
      ∫⁻ y in Prod.map i _root_.id ⁻¹' T, K (i y.1, y.2) ∂((μ.comap i).prod ν) := by
  have hpm : MeasurableEmbedding (Prod.map i (_root_.id : β → β)) := hi.prodMap MeasurableEmbedding.id
  have hR : MeasurableSet (range i ×ˢ (univ : Set β)) :=
    hi.measurableSet_range.prod MeasurableSet.univ
  have hmap : ((μ.comap i).prod ν).map (Prod.map i _root_.id) = (μ.prod ν).restrict (range i ×ˢ univ) := by
    rw [← Measure.map_prod_map _ _ hi.measurable measurable_id, hi.map_comap, Measure.map_id,
      ← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
  have hres : (μ.prod ν).restrict T = ((μ.prod ν).restrict (range i ×ˢ univ)).restrict T := by
    rw [Measure.restrict_restrict' hR, inter_eq_left.mpr hT]
  rw [hres, ← hmap, hpm.restrict_map, hpm.lintegral_map]
  rfl

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]

section LowerGroupHaar

local instance lghPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance lghPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance lghLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance lghLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance lghLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance lghLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance lghLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance lghLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- A lower-group × horizontal test function read on the lower Lie algebra
through the lower identity Cayley chart (junk zero off the exact source). -/
def lastCayleyLowerChartPullback
    (K : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) ×
      (Fin n → ℚ_[p]) → ℝ≥0∞)
    (q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) : ℝ≥0∞ := by
  classical
  exact if hq : (q.1 : (skewAdjointMatricesLieSubalgebra
      (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈ skewAdjointPadicCayleySource W.pairingMatrix p then
    K ((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 ⟨q.1, hq⟩).1, q.2)
  else 0

/-- The repository lower coordinate measure is sigma-finite. -/
theorem skewAdjointPadicCoordinateMeasure_sigmaFinite :
    SigmaFinite (skewAdjointPadicCoordinateMeasure W.pairingMatrix p) := by
  rw [W.skewAdjointPadicCoordinateMeasure_eq_map_unitHaar p]
  exact (skewAdjointPadicCoordinateEquiv W.pairingMatrix p).symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

set_option backward.isDefEq.respectTransparency false in
/-- Lower side on the lower group: for a measurable set `U` of lower Lie-algebra ×
horizontal points with lower coordinate in the exact lower Cayley source, the
lower-Cayley-density-weighted lintegral against (repository lower coordinate
measure) × (horizontal unit Haar) equals the lintegral against (repository lower
group Haar) × (horizontal unit Haar) over the chart image. -/
theorem lastCayleyLower_setLIntegral_eq_groupHaar
    (U : Set (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])))
    (hUm : MeasurableSet U)
    (hU : ∀ q ∈ U, (q.1 : (skewAdjointMatricesLieSubalgebra
      (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (K : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) ×
      (Fin n → ℚ_[p]) → ℝ≥0∞) :
    ∫⁻ q in U, skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix q.1 *
        W.lastCayleyLowerChartPullback p K q
        ∂((skewAdjointPadicCoordinateMeasure W.pairingMatrix p).prod (Padic.unitHaar p (Fin n))) =
      ∫⁻ x in Prod.map (fun X : skewAdjointPadicCayleySource W.pairingMatrix p ↦
            ((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 X).1))
          _root_.id '' (Prod.map Subtype.val _root_.id ⁻¹' U),
        K x ∂((padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero).prod
          (Padic.unitHaar p (Fin n))) := by
  classical
  set src := skewAdjointPadicCayleySource W.pairingMatrix p with hsrc
  set h1 := skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 with hh1
  set μW := skewAdjointPadicCoordinateMeasure W.pairingMatrix p with hμW
  set μH := padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero with hμH
  set ν := Padic.unitHaar p (Fin n) with hν
  set A : Set (src × (Fin n → ℚ_[p])) := Prod.map Subtype.val _root_.id ⁻¹' U with hA
  haveI : SigmaFinite μW := W.skewAdjointPadicCoordinateMeasure_sigmaFinite p
  have hiS : MeasurableEmbedding (Subtype.val : src → _) :=
    MeasurableEmbedding.subtype_coe (isOpen_skewAdjointPadicCayleySource _ p).measurableSet
  haveI : SigmaFinite (μW.comap Subtype.val) := hiS.sigmaFinite_comap μW
  haveI : SigmaFinite μH :=
    padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite p n W.pairingMatrix W.form_symm
      W.form_det_ne_zero
  have hiT : MeasurableEmbedding (Subtype.val :
      padicCayleySpecialOrthogonalTranslatedTarget W.pairingMatrix p 1 →
        specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    MeasurableEmbedding.subtype_coe
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget _ p 1).measurableSet
  haveI : SigmaFinite (μH.comap Subtype.val) := hiT.sigmaFinite_comap μH
  have hemb : MeasurableEmbedding h1 := h1.measurableEmbedding
  have hAm : MeasurableSet A := (measurable_subtype_coe.prodMap measurable_id) hUm
  -- step a: pull the lower coordinate side back to the source subtype
  have ha := hiS.setLIntegral_prod_comap μW ν (T := U)
    (fun q hq ↦ ⟨⟨⟨q.1, hU q hq⟩, rfl⟩, trivial⟩)
    (fun q ↦ skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix q.1 *
      W.lastCayleyLowerChartPullback p K q)
  rw [ha]
  -- step b: identify the integrand and absorb the density
  have hint : ∫⁻ y in A, skewAdjointPadicCayleyAmbientDensity p n W.pairingMatrix y.1.1 *
        W.lastCayleyLowerChartPullback p K (y.1.1, y.2) ∂((μW.comap Subtype.val).prod ν) =
      ∫⁻ y in A, ((skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ∘ Prod.fst :
          src × (Fin n → ℚ_[p]) → ℝ≥0∞) *
        fun y : src × (Fin n → ℚ_[p]) ↦ K ((h1 y.1).1, y.2)) y ∂((μW.comap Subtype.val).prod ν) := by
    apply setLIntegral_congr_fun hAm
    intro y _
    simp only [Pi.mul_apply, Function.comp_apply, lastCayleyLowerChartPullback]
    rw [dif_pos y.1.2]
    rfl
  rw [hint, ← setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
      ((Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal p n _).comp
        measurable_fst) _ hAm
      (Eventually.of_forall fun z ↦ by
        change skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix z.1 < ⊤
        rw [Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe]
        exact ENNReal.coe_lt_top),
    show (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ∘
      Prod.fst : src × (Fin n → ℚ_[p]) → ℝ≥0∞) =
      fun z ↦ skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix z.1 from rfl,
    ← MeasureTheory.prod_withDensity_left
      (Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal p n _)]
  -- step d: the right side through the lower group and the chart
  set σW := (μW.comap Subtype.val).withDensity
    (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix) with hσW
  have hchart : μH.comap Subtype.val = σW.map h1 := by
    rw [comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget p n W.pairingMatrix
      W.form_symm W.form_det_ne_zero 1]
    rfl
  haveI : SFinite (σW.map h1) := by rw [← hchart]; infer_instance
  haveI : SFinite ((σW.map h1).comap h1) := by rw [hemb.comap_map]; infer_instance
  set T := Prod.map (fun X : src ↦ (h1 X).1) _root_.id '' A with hT
  have hTsub : T ⊆ range (Subtype.val : padicCayleySpecialOrthogonalTranslatedTarget W.pairingMatrix p 1 → _)
      ×ˢ univ := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨⟨h1 y.1, rfl⟩, trivial⟩
  have hd1 := hiT.setLIntegral_prod_comap μH ν hTsub K
  rw [hd1, hchart]
  have hT2sub : Prod.map Subtype.val _root_.id ⁻¹' T ⊆ range h1 ×ˢ univ := by
    rintro y -
    exact ⟨⟨h1.symm y.1, h1.apply_symm_apply y.1⟩, trivial⟩
  have hd2 := hemb.setLIntegral_prod_comap (σW.map h1) ν hT2sub (fun y ↦ K (y.1.1, y.2))
  rw [hd2, hemb.comap_map]
  have hpre : Prod.map h1 _root_.id ⁻¹' (Prod.map Subtype.val _root_.id ⁻¹' T) = A := by
    have hinj : Function.Injective (Prod.map (fun X : src ↦ (h1 X).1) (_root_.id : (Fin n → ℚ_[p]) → _)) :=
      fun a b hab ↦ by
        simp only [Prod.map, Prod.mk.injEq] at hab
        exact Prod.ext (h1.injective (Subtype.val_injective hab.1)) hab.2
    have hcomp : (Prod.map Subtype.val _root_.id ∘ Prod.map h1 _root_.id) =
        Prod.map (fun X : src ↦ (h1 X).1) (_root_.id : (Fin n → ℚ_[p]) → _) := rfl
    rw [← preimage_comp, hcomp, hT]
    exact hinj.preimage_image A
  rw [hpre]

end LowerGroupHaar

section BothGroups

variable (a : ℚ) (ha : a ≠ 0)

local instance bgPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance bgPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance bgSkewMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance bgSkewBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance bgLowerMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance bgLowerBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance bgGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance bgGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance bgLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance bgLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance bgLowerLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance bgLowerLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩
local instance bgHigherLieMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  borel _
local instance bgHigherLieBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :=
  ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

/-- A higher-group test function read on (lower group × horizontal coefficients)
through the lower chart inverse and the actual product (junk zero off the
lower identity chart target). -/
def lastCayleyProductLowerGroupTest
    (G : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞)
    (x : specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) ×
      (Fin n → ℚ_[p])) : ℝ≥0∞ := by
  classical
  exact if hx : x.1 ∈ padicCayleySpecialOrthogonalTranslatedTarget W.pairingMatrix p 1 then
    W.lastCayleyChartPullback a ha p G (W.lastCayleyProductFrameValue a ha p S z v
      (((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1).symm
        ⟨x.1, hx⟩).1, x.2))
  else 0

set_option backward.isDefEq.respectTransparency false in
include hs hv in
/-- Relative fiber product with both sides on groups: on every sufficiently small
exact compact open coordinate ball `U` around `(Y, 0)`, the repository higher
group-Haar lintegral over the Cayley image of the actual product equals
|r| · |orbit-relative| times the lintegral against (repository lower group Haar)
× (horizontal unit Haar) over the lower chart image of `U`, of the same test
read through the lower chart and the actual product. -/
theorem lastCayleyProduct_exists_forall_lintegral_bothGroups :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ G : specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) → ℝ≥0∞,
        ∫⁻ x in Subtype.val '' (skewAdjointPadicCayleyTranslatedHomeomorph
              (W.nonisotropicLastExtension a ha).pairingMatrix p
              (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ''
            (Subtype.val ⁻¹' (W.lastCayleyProductFrameValue a ha p S z v ''
              ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)))),
            G x ∂(padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_det_ne_zero) =
          (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
            (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
              lastCoordinateVector
              (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
              (fun j ↦ W.lastCayleyProductIntrinsicDerivative a ha p S dS z hSs.hasFDerivAt hSO
                Y hY X hX hproduct (0, v j))‖₊ : ℝ≥0∞) *
            ∫⁻ x in Prod.map (fun X : skewAdjointPadicCayleySource W.pairingMatrix p ↦
                  ((skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 X).1))
                _root_.id '' (Prod.map Subtype.val _root_.id ⁻¹'
                  ((W.lastCayleyProductSourceCoordinates p) ⁻¹'
                    closedBall (W.lastCayleyProductSourceCoordinates p (Y,0)) r)),
              W.lastCayleyProductLowerGroupTest p a ha S z v G x
              ∂((padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero).prod
                (Padic.unitHaar p (Fin n))) := by
  classical
  set eE := W.lastCayleyProductSourceCoordinates p with heE
  set h1 := skewAdjointPadicCayleyTranslatedHomeomorph W.pairingMatrix p W.form_det_ne_zero 1 with hh1
  obtain ⟨δ1, hδ1, hG⟩ := W.lastCayleyProduct_exists_forall_lintegral_groupHaar_repository p a ha S dS
    z hSs hSO Y hY X hX hproduct v hs hv
  -- lower coordinates stay in the exact lower Cayley source near the base point
  have hsrcN : {q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p]) | (q.1 : (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p} ∈ 𝓝 ((Y,0) : skewAdjointMatricesLieSubalgebra
      (W.specialOrthogonalMappedFormMatrix ℚ_[p]) × (Fin n → ℚ_[p])) :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_skewAdjointPadicCayleySource _ p).mem_nhds hY)
  have hsrcC : {x | ((eE.symm x).1 : (skewAdjointMatricesLieSubalgebra
      (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p} ∈ 𝓝 (eE (Y,0)) := by
    have hcont : ContinuousAt eE.symm (eE (Y,0)) := eE.symm.continuous.continuousAt
    rw [← eE.symm_apply_apply (Y,0)] at hsrcN
    exact hcont.preimage_mem_nhds hsrcN
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hsrcC
  refine ⟨min δ1 ε, lt_min hδ1 hε, fun r hr hrδ G ↦ ?_⟩
  obtain ⟨-, -, hlaw⟩ := hG r hr (hrδ.trans_le (min_le_left _ _))
  set U := eE ⁻¹' closedBall (eE (Y,0)) r with hU
  have hUm : MeasurableSet U := (isClosed_closedBall.preimage eE.continuous).measurableSet
  have hUsrc : ∀ q ∈ U, (q.1 : (skewAdjointMatricesLieSubalgebra
      (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) ∈
        skewAdjointPadicCayleySource W.pairingMatrix p := by
    intro q hq
    have := hεsub (closedBall_subset_ball (hrδ.trans_le (min_le_right _ _)) hq)
    simpa only [Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] using this
  rw [hlaw G]
  congr 1
  rw [← W.lastCayleyLower_setLIntegral_eq_groupHaar p U hUm hUsrc]
  apply setLIntegral_congr_fun hUm
  intro q hq
  simp only [lastCayleyLowerChartPullback, dif_pos (hUsrc q hq)]
  congr 1
  simp only [lastCayleyProductLowerGroupTest]
  rw [dif_pos (h1 ⟨q.1, hUsrc q hq⟩).2]
  simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]

end BothGroups

end RationalQuadraticSpaceMatrix
