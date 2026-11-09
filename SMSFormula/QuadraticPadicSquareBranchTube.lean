import SMSFormula.QuadraticPadicSquareBranchAtlasGlue

/-! The tube (coarea) formula for the normalized branch measures and their
atlas glue. For a measurable set `T` of vectors inside the square-branch
region of a nonisotropic point and a measurable value set `B`,
`vol(T ∩ Q⁻¹ B) = ∫_B (normalized branch measure at t)(T_t) dν(t)`; this is the
value-measure identity `map_padicSquareBranch_withDensity` at the weight
`1_T`. Summing over the `disjointed` pieces of a supplied countable atlas of
branch regions covering `T` gives the same formula with the atlas glue in place
of the branch measure. When the glued fiber mass of `T` is constant on `B`, the
tube volume is that mass times `ν(B)`: this is the form in which the glued mass
of an integral set is read as a value-density quotient. No chart, point, cutoff
or Haar normalization is chosen here. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicTubeMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicTubeBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space] [LocallyCompactSpace space]

omit [LocallyCompactSpace space] in
/-- The branch-measure mass of the slice of a measurable set is the value
density of its indicator. -/
theorem padicSquareBranchFiberMeasure_preimage_eq_valueDensity
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime])
    {T : Set space} (hT : MeasurableSet T) :
    form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value
        (Subtype.val ⁻¹' T) =
      form.padicSquareBranchValueDensity prime point transverseHaar (T.indicator 1) value := by
  rw [← form.lintegral_padicSquareBranchFiberMeasure_restrict_weight prime point hpoint
    transverseHaar value (T.indicator 1) (measurable_one.indicator hT),
    ← lintegral_indicator_one (measurable_subtype_coe hT)]
  rfl

/-- Single-branch tube formula. -/
theorem padicSquareBranch_measure_inter_preimage_eq_lintegral
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ {vector | ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv
      point hpoint).symm vector).2 ∈ Rat.padicUnitSquareScalarSource prime})
    {B : Set ℚ_[prime]} (hB : MeasurableSet B) :
    vectorHaar (T ∩ form ⁻¹' B) =
      ∫⁻ value in B, ((form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar
          scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value)
        (Subtype.val ⁻¹' T) ∂scalarHaar := by
  set c := (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar
    scalarHaar vectorHaar : ℝ≥0∞) with hc
  have hc0 : c ≠ 0 := ENNReal.coe_ne_zero.mpr (form.anisotropicOrthogonalProductHaarScalar_pos
    point hpoint transverseHaar scalarHaar vectorHaar).ne'
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  have hmeasure := form.map_padicSquareBranch_withDensity prime point hpoint
    transverseHaar scalarHaar vectorHaar (T.indicator 1) (measurable_one.indicator hT)
  have hweight : form.padicSquareBranchWeight prime point hpoint (T.indicator 1) = T.indicator 1 := by
    rw [padicSquareBranchWeight, Set.indicator_indicator]
    exact congrArg (fun S ↦ S.indicator (1 : space → ℝ≥0∞)) (Set.inter_eq_right.mpr hsub)
  rw [hweight] at hmeasure
  have happ := congrArg (fun m : Measure ℚ_[prime] ↦ m B) hmeasure
  simp only [Measure.smul_apply, smul_eq_mul] at happ
  rw [Measure.map_apply hform.measurable hB, withDensity_apply _ (hform.measurable hB),
    lintegral_indicator_one hT, Measure.restrict_apply hT, withDensity_apply _ hB] at happ
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)]
  simp_rw [form.padicSquareBranchFiberMeasure_preimage_eq_valueDensity prime point hpoint
    transverseHaar _ hT]
  rw [← happ, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]

/-- The normalized branch mass of the slice of a measurable set is measurable in
the value. -/
theorem measurable_padicSquareBranchFiberMeasure_normalized_preimage
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T) :
    Measurable (fun value ↦ ((form.anisotropicOrthogonalProductHaarScalar point hpoint
        transverseHaar scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
      form.padicSquareBranchFiberMeasure prime point hpoint transverseHaar value)
        (Subtype.val ⁻¹' T)) := by
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [form.padicSquareBranchFiberMeasure_preimage_eq_valueDensity prime point hpoint
    transverseHaar _ hT]
  exact measurable_const.mul (form.measurable_padicSquareBranchValueDensity prime point
    transverseHaar _ (measurable_one.indicator hT))

/-- The square-branch region of the `i`-th supplied atlas point, as a set of
vectors. -/
def padicSquareBranchAtlasRegion (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space)
    (hpoint : ∀ i, form (point i) ≠ 0) (i : ℕ) : Set space :=
  {vector | ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv
    (point i) (hpoint i)).symm vector).2 ∈ Rat.padicUnitSquareScalarSource prime}

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space]
  [LocallyCompactSpace space] in
theorem isOpen_padicSquareBranchAtlasRegion (form : QuadraticForm ℚ_[prime] space)
    (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0) (i : ℕ) :
    IsOpen (form.padicSquareBranchAtlasRegion prime point hpoint i) :=
  (Rat.isOpen_padicUnitSquareScalarSource prime).preimage
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv
      (point i) (hpoint i)).symm.continuous.snd)

/-- The glued slice mass of a set inside the `i`-th region is its normalized
branch slice mass. -/
theorem padicSquareBranchAtlasGlue_preimage_of_subset_region
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime]) (i : ℕ)
    {P : Set space} (hP : MeasurableSet P)
    (hPR : P ⊆ form.padicSquareBranchAtlasRegion prime point hpoint i) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar value (Subtype.val ⁻¹' P) =
      ((form.anisotropicOrthogonalProductHaarScalar (point i) (hpoint i) (transverseHaar i)
          scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime (point i) (hpoint i) (transverseHaar i) value)
        (Subtype.val ⁻¹' P) := by
  refine form.padicSquareBranchAtlasGlue_apply_of_subset prime point hpoint transverseHaar
    scalarHaar vectorHaar value i (measurable_subtype_coe hP) ?_
  rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) value]
  exact fun vector hvector ↦ hPR hvector

/-- The glued slice mass of a covered set is the sum of the normalized branch
slice masses of its `disjointed` pieces. -/
theorem padicSquareBranchAtlasGlue_preimage_eq_tsum
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i) (value : ℚ_[prime]) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar value (Subtype.val ⁻¹' T) =
      ∑' i, ((form.anisotropicOrthogonalProductHaarScalar (point i) (hpoint i) (transverseHaar i)
          scalarHaar vectorHaar : ℝ≥0∞)⁻¹ •
        form.padicSquareBranchFiberMeasure prime (point i) (hpoint i) (transverseHaar i) value)
        (Subtype.val ⁻¹' (T ∩ disjointed (form.padicSquareBranchAtlasRegion prime point hpoint) i)) := by
  set R := form.padicSquareBranchAtlasRegion prime point hpoint with hRdef
  have hR : ∀ i, MeasurableSet (R i) := fun i ↦
    (form.isOpen_padicSquareBranchAtlasRegion prime point hpoint i).measurableSet
  have hP : ∀ i, MeasurableSet (T ∩ disjointed R i) := fun i ↦
    hT.inter (MeasurableSet.disjointed hR i)
  conv_lhs => rw [show T = ⋃ i, (T ∩ disjointed R i) by
    rw [← Set.inter_iUnion, iUnion_disjointed]; exact (Set.inter_eq_left.mpr hsub).symm]
  rw [Set.preimage_iUnion, measure_iUnion (fun i j hij ↦
    ((disjoint_disjointed R hij).mono Set.inter_subset_right Set.inter_subset_right).preimage _)
    (fun i ↦ measurable_subtype_coe (hP i))]
  exact tsum_congr fun i ↦ form.padicSquareBranchAtlasGlue_preimage_of_subset_region prime point
    hpoint transverseHaar scalarHaar vectorHaar value i (hP i)
    (Set.inter_subset_right.trans (disjointed_subset R i))

/-- The glued slice mass of a covered measurable set is measurable in the value. -/
theorem measurable_padicSquareBranchAtlasGlue_preimage
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i) :
    Measurable (fun value ↦ form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar value (Subtype.val ⁻¹' T)) := by
  simp_rw [form.padicSquareBranchAtlasGlue_preimage_eq_tsum prime point hpoint transverseHaar
    scalarHaar vectorHaar hT hsub]
  exact Measurable.ennreal_tsum fun i ↦
    form.measurable_padicSquareBranchFiberMeasure_normalized_preimage prime (point i) (hpoint i)
      (transverseHaar i) scalarHaar vectorHaar (hT.inter (MeasurableSet.disjointed
        (fun j ↦ (form.isOpen_padicSquareBranchAtlasRegion prime point hpoint j).measurableSet) i))

/-- Atlas tube formula: for a measurable set covered by the branch regions of a
supplied countable atlas, the volume of its value tube over `B` is the integral
over `B` of the atlas-glued fiber mass of its slices. -/
theorem padicSquareBranchAtlasGlue_measure_inter_preimage_eq_lintegral
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    {B : Set ℚ_[prime]} (hB : MeasurableSet B) :
    vectorHaar (T ∩ form ⁻¹' B) =
      ∫⁻ value in B, form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
        scalarHaar vectorHaar value (Subtype.val ⁻¹' T) ∂scalarHaar := by
  set R := form.padicSquareBranchAtlasRegion prime point hpoint with hRdef
  have hR : ∀ i, MeasurableSet (R i) := fun i ↦
    (form.isOpen_padicSquareBranchAtlasRegion prime point hpoint i).measurableSet
  have hP : ∀ i, MeasurableSet (T ∩ disjointed R i) := fun i ↦
    hT.inter (MeasurableSet.disjointed hR i)
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  simp_rw [form.padicSquareBranchAtlasGlue_preimage_eq_tsum prime point hpoint transverseHaar
    scalarHaar vectorHaar hT hsub]
  rw [lintegral_tsum fun i ↦ (form.measurable_padicSquareBranchFiberMeasure_normalized_preimage
    prime (point i) (hpoint i) (transverseHaar i) scalarHaar vectorHaar (hP i)).aemeasurable]
  conv_lhs => rw [show T = ⋃ i, (T ∩ disjointed R i) by
    rw [← Set.inter_iUnion, iUnion_disjointed]; exact (Set.inter_eq_left.mpr hsub).symm]
  rw [Set.iUnion_inter, measure_iUnion (fun i j hij ↦
    ((disjoint_disjointed R hij).mono Set.inter_subset_right Set.inter_subset_right).mono
      Set.inter_subset_left Set.inter_subset_left) (fun i ↦ (hP i).inter (hform.measurable hB))]
  exact tsum_congr fun i ↦ form.padicSquareBranch_measure_inter_preimage_eq_lintegral prime
    (point i) (hpoint i) (transverseHaar i) scalarHaar vectorHaar (hP i)
    (Set.inter_subset_right.trans (disjointed_subset R i)) hB

/-- Atlas coarea formula: the value distribution of a covered measurable set has
the atlas-glued slice mass as its density. -/
theorem map_restrict_eq_withDensity_padicSquareBranchAtlasGlue
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i) :
    Measure.map form (vectorHaar.restrict T) =
      scalarHaar.withDensity (fun value ↦ form.padicSquareBranchAtlasGlue prime point hpoint
        transverseHaar scalarHaar vectorHaar value (Subtype.val ⁻¹' T)) := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  ext B hB
  rw [Measure.map_apply hform.measurable hB, Measure.restrict_apply (hform.measurable hB),
    withDensity_apply _ hB, Set.inter_comm]
  exact form.padicSquareBranchAtlasGlue_measure_inter_preimage_eq_lintegral prime point hpoint
    transverseHaar scalarHaar vectorHaar hT hsub hB

/-- Any value density of a covered measurable set agrees almost everywhere
with its atlas-glued slice mass. -/
theorem padicSquareBranchAtlasGlue_preimage_ae_eq_of_map_restrict
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    {density : ℚ_[prime] → ℝ≥0∞} (hdensity : AEMeasurable density scalarHaar)
    (hmap : Measure.map form (vectorHaar.restrict T) = scalarHaar.withDensity density) :
    (fun value ↦ form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar value (Subtype.val ⁻¹' T)) =ᵐ[scalarHaar] density := by
  haveI : ProperSpace ℚ_[prime] := inferInstance
  refine (withDensity_eq_iff_of_sigmaFinite
    (form.measurable_padicSquareBranchAtlasGlue_preimage prime point hpoint transverseHaar
      scalarHaar vectorHaar hT hsub).aemeasurable hdensity).mp ?_
  rw [← hmap, form.map_restrict_eq_withDensity_padicSquareBranchAtlasGlue prime point hpoint
    transverseHaar scalarHaar vectorHaar hT hsub]

/-- Constant glued slice mass: if the atlas-glued slice mass of `T` is constant
equal to `m` on `B`, the tube volume is `m · ν(B)`. -/
theorem padicSquareBranchAtlasGlue_measure_inter_preimage_eq_mul
    (form : QuadraticForm ℚ_[prime] space) (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set space} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    {B : Set ℚ_[prime]} (hB : MeasurableSet B) {m : ℝ≥0∞}
    (hm : ∀ value ∈ B, form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar value (Subtype.val ⁻¹' T) = m) :
    vectorHaar (T ∩ form ⁻¹' B) = m * scalarHaar B := by
  rw [form.padicSquareBranchAtlasGlue_measure_inter_preimage_eq_lintegral prime point hpoint
    transverseHaar scalarHaar vectorHaar hT hsub hB, setLIntegral_congr_fun hB hm,
    setLIntegral_const]

end QuadraticMap
