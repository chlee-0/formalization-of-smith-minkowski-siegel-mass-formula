import SMSFormula.QuadraticPadicSquareBranchTube
import SMSFormula.QuadraticPadicSquareBranchFiberGlueScalar

/-! Scalar covariance of the atlas glue and unit-square invariance of glued slice
masses. On coordinate space, for a nonzero scalar `u` the fiber scaling
`x ↦ u x` from `{Q = a}` to `{Q = u² a}` multiplies atlas-glued masses by
`|u|^(rank-2)` on sets covered at both values (branch scalar covariance at the
scaled atlas points, glued through the compatibility with further points).
Consequently the glued slice mass of a vector set `T` stable under a unit `u`
takes the same value at `a` and `u² a`; with the atlas tube formula the tube
volume of `T` over any value set inside the unit-square class of `a` is that
slice mass times the value measure. Countable atlases covering all nonisotropic
vectors exist (Lindelöf). The atlas points and Haars are supplied or obtained by
the existence statement; no chart, cutoff or Haar normalization is chosen. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicAtlasScalarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicAtlasScalarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

section Generic

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

/-- Every nonisotropic vector lies in its own square-branch region. -/
theorem mem_padicSquareBranchRegion_self (form : QuadraticForm ℚ_[prime] space)
    (vector : space) (hvector : form vector ≠ 0) :
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv vector hvector).symm
      vector).2 ∈ Rat.padicUnitSquareScalarSource prime := by
  have h : (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv vector hvector).symm
      vector = (0, 1) := by
    rw [ContinuousLinearEquiv.symm_apply_eq,
      form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply]
    simp
  rw [h]
  exact ⟨1, Rat.one_mem_unitSquareIdentityChart_source _, rfl⟩

/-- Countable atlas existence: when the form is not identically zero, countably
many nonisotropic points have branch regions covering all nonisotropic vectors. -/
theorem exists_padicSquareBranchAtlas_cover [SecondCountableTopology space]
    (form : QuadraticForm ℚ_[prime] space) (hform : ∃ vector, form vector ≠ 0) :
    ∃ (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0),
      {vector | form vector ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i := by
  let U : {vector : space // form vector ≠ 0} → Set space := fun v ↦
    {w | ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv v.val v.property).symm
      w).2 ∈ Rat.padicUnitSquareScalarSource prime}
  have hU : ∀ v, IsOpen (U v) := fun v ↦ (Rat.isOpen_padicUnitSquareScalarSource prime).preimage
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv v.val v.property).symm.continuous.snd)
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  have hcover : {vector | form vector ≠ 0} ⊆ ⋃ v ∈ S, U v := by
    rw [hSU]
    intro w hw
    exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, form.mem_padicSquareBranchRegion_self prime w hw⟩
  obtain ⟨w, hw⟩ := hform
  by_cases hSne : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hSne
    refine ⟨fun i ↦ (f i).val, fun i ↦ (f i).property, fun x hx ↦ ?_⟩
    obtain ⟨v, hvS, hxv⟩ := Set.mem_iUnion₂.mp (hcover hx)
    rw [hf] at hvS
    obtain ⟨i, rfl⟩ := hvS
    exact Set.mem_iUnion.mpr ⟨i, hxv⟩
  · exfalso
    have hx := hcover (show w ∈ {vector | form vector ≠ 0} from hw)
    rw [Set.not_nonempty_iff_eq_empty.mp hSne] at hx
    simp at hx

end Generic

variable {rank : ℕ}

local notation "E" => Fin rank → ℚ_[prime]

/-- Scalar covariance of the atlas glue: on sets covered at both values, the
atlas glue at `u² a` is `|u|^(rank-2)` times the atlas glue at `a` pulled back by
the fiber scaling. -/
theorem padicSquareBranchAtlasGlue_scalar (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0) (value : ℚ_[prime])
    {S : Set {vector : E // form vector = scalar ^ 2 * value}} (hS : MeasurableSet S)
    (hcov : S ⊆ ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i)
      (scalar ^ 2 * value)))
    (hcov' : form.scalarValueFiberMap scalar value ⁻¹' S ⊆
      ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value)) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
        (scalar ^ 2 * value) S =
      (‖scalar‖₊ : ℝ≥0∞) ^ ((rank : ℤ) - 2) *
        form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
          value (form.scalarValueFiberMap scalar value ⁻¹' S) := by
  set φ := form.scalarValueFiberMap scalar value with hφ
  have hφm : Measurable φ := (form.continuous_scalarValueFiberMap scalar value).measurable
  set R := form.padicSquareBranchAtlasRegion prime point hpoint with hRdef
  have hR : ∀ i, MeasurableSet (R i) := fun i ↦
    (form.isOpen_padicSquareBranchAtlasRegion prime point hpoint i).measurableSet
  -- pieces of `S`, cut by the scaled disjointed regions
  set P : ℕ → Set {vector : E // form vector = scalar ^ 2 * value} := fun i ↦
    S ∩ {y | scalar⁻¹ • y.val ∈ disjointed R i} with hPdef
  have hPm : ∀ i, MeasurableSet (P i) := fun i ↦ hS.inter
    ((MeasurableSet.disjointed hR i).preimage
      ((continuous_const.smul continuous_subtype_val).measurable))
  have hPdisj : Pairwise (Function.onFun Disjoint P) := fun i j hij ↦
    ((disjoint_disjointed R hij).preimage (fun y : {vector : E // form vector = scalar ^ 2 * value}
      ↦ scalar⁻¹ • y.val)).mono Set.inter_subset_right Set.inter_subset_right
  have hunscale : ∀ y : {vector : E // form vector = scalar ^ 2 * value},
      ∃ x : {vector : E // form vector = value}, φ x = y ∧ x.val = scalar⁻¹ • y.val := by
    intro y
    refine ⟨⟨scalar⁻¹ • y.val, ?_⟩, Subtype.ext ?_, rfl⟩
    · rw [QuadraticMap.map_smul, y.property, smul_eq_mul]
      field_simp
    · change scalar • scalar⁻¹ • y.val = y.val
      rw [smul_inv_smul₀ hscalar]
  have hSP : S = ⋃ i, P i := by
    ext y
    simp only [hPdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hy
      obtain ⟨x, hxy, hxval⟩ := hunscale y
      have hx : x ∈ φ ⁻¹' S := by rw [Set.mem_preimage, hxy]; exact hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov' hx)
      rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) value] at hi
      have hxR : scalar⁻¹ • y.val ∈ ⋃ i, R i := hxval ▸ Set.mem_iUnion.mpr ⟨i, hi⟩
      rw [← iUnion_disjointed] at hxR
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxR
      exact ⟨j, hy, hj⟩
    · rintro ⟨i, hy, _⟩
      exact hy
  have hpreP : φ ⁻¹' S = ⋃ i, φ ⁻¹' P i := by rw [← Set.preimage_iUnion, ← hSP]
  -- each piece is inside the scaled branch range and the unscaled branch range
  have hscaledRange : ∀ i, P i ⊆ Set.range (form.padicSquareBranchFiberMap prime
      (scalar • point i) (form.quadratic_smul_ne_zero (point i) (hpoint i) scalar hscalar)
      (scalar ^ 2 * value)) := by
    intro i y hy
    obtain ⟨x, hxy, hxval⟩ := hunscale y
    have hx : x ∈ Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value) := by
      rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) value]
      exact disjointed_subset R i (hxval ▸ hy.2)
    rw [← form.padicSquareBranchFiberMap_preimage_range_scalar prime (point i) (hpoint i) scalar
      hscalar value] at hx
    rw [← hxy]
    exact hx
  have hunscaledRange : ∀ i, φ ⁻¹' P i ⊆
      Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value) := by
    intro i x hx
    rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) value]
    have hval : scalar⁻¹ • (φ x).val = x.val := by
      change scalar⁻¹ • scalar • x.val = x.val
      rw [inv_smul_smul₀ hscalar]
    exact disjointed_subset R i (hval ▸ hx.2)
  -- piecewise comparison
  have hpiece : ∀ i, form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar
      scalarHaar vectorHaar (scalar ^ 2 * value) (P i) =
      (‖scalar‖₊ : ℝ≥0∞) ^ ((rank : ℤ) - 2) *
        form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
          value (φ ⁻¹' P i) := by
    intro i
    let haar₀ : Measure (form.anisotropicOrthogonal (scalar • point i)) := Measure.addHaar
    have hsub : P i ⊆ Set.range (form.padicSquareBranchFiberMap prime (scalar • point i)
        (form.quadratic_smul_ne_zero (point i) (hpoint i) scalar hscalar) (scalar ^ 2 * value)) ∩
        ⋃ j, Set.range (form.padicSquareBranchFiberMap prime (point j) (hpoint j)
          (scalar ^ 2 * value)) :=
      fun y hy ↦ ⟨hscaledRange i hy, hcov hy.1⟩
    have hrestrict := form.padicSquareBranchAtlasGlue_restrict_of_point prime point hpoint
      transverseHaar scalarHaar vectorHaar (scalar ^ 2 * value) (scalar • point i)
      (form.quadratic_smul_ne_zero (point i) (hpoint i) scalar hscalar) haar₀
    have happ := congrArg (fun m : Measure {vector : E // form vector = scalar ^ 2 * value} ↦
      m (P i)) hrestrict
    simp only [Measure.restrict_apply (hPm i), Set.inter_eq_left.mpr hsub] at happ
    rw [happ, form.padicCoordinateBranch_normalized_scalar prime (point i) (hpoint i) scalar
      hscalar (transverseHaar i) haar₀ scalarHaar vectorHaar value,
      Measure.smul_apply, smul_eq_mul, Measure.map_apply hφm (hPm i),
      form.padicSquareBranchAtlasGlue_apply_of_subset prime point hpoint transverseHaar
        scalarHaar vectorHaar value i (hφm (hPm i)) (hunscaledRange i)]
  rw [hpreP, measure_iUnion (fun i j hij ↦ (hPdisj hij).preimage φ) (fun i ↦ hφm (hPm i)),
    ENNReal.tsum_mul_left.symm]
  conv_lhs => rw [hSP]
  rw [measure_iUnion hPdisj hPm]
  exact tsum_congr hpiece

/-- Unit-square invariance of glued slice masses: for a covered vector set `T`
stable under a unit `u`, the glued slice masses at `a` and `u² a` agree. -/
theorem padicSquareBranchAtlasGlue_preimage_unit_sq_mul (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set E} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (unit : ℚ_[prime]) (hunit : ‖unit‖ = 1) (hstable : ∀ vector, unit • vector ∈ T ↔ vector ∈ T)
    (value : ℚ_[prime]) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
        (unit ^ 2 * value) (Subtype.val ⁻¹' T) =
      form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
        value (Subtype.val ⁻¹' T) := by
  have hunit0 : unit ≠ 0 := by
    intro h
    rw [h, norm_zero] at hunit
    exact zero_ne_one hunit
  have hcover : ∀ t : ℚ_[prime], (Subtype.val ⁻¹' T : Set {vector : E // form vector = t}) ⊆
      ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) t) := by
    intro t y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hy)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [form.range_padicSquareBranchFiberMap prime (point i) (hpoint i) t]
    exact hi
  have hpre : form.scalarValueFiberMap unit value ⁻¹' (Subtype.val ⁻¹' T) =
      (Subtype.val ⁻¹' T : Set {vector : E // form vector = value}) := by
    ext x
    exact hstable x.val
  have hnorm : (‖unit‖₊ : ℝ≥0∞) = 1 := by
    rw [ENNReal.coe_eq_one, ← NNReal.coe_eq_one, coe_nnnorm, hunit]
  rw [form.padicSquareBranchAtlasGlue_scalar prime point hpoint transverseHaar scalarHaar
    vectorHaar unit hunit0 value (measurable_subtype_coe hT) (hcover _) (hpre ▸ hcover value),
    hpre, hnorm]
  have hone : ∀ n : ℤ, (1 : ℝ≥0∞) ^ n = 1 := fun n ↦ by cases n <;> simp [zpow_negSucc]
  rw [hone, one_mul]

/-- Local-density form of the tube formula: for a covered vector set `T` stable
under all units and a value set `B` inside the unit-square class of `a`, the tube
volume of `T` over `B` is the glued slice mass of `T` at `a` times `ν(B)`. -/
theorem padicSquareBranchAtlasGlue_measure_inter_preimage_eq_mul_of_unitSquareClass
    (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    {T : Set E} (hT : MeasurableSet T)
    (hsub : T ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (hstable : ∀ unit : ℚ_[prime], ‖unit‖ = 1 → ∀ vector, unit • vector ∈ T ↔ vector ∈ T)
    (value : ℚ_[prime]) {B : Set ℚ_[prime]} (hB : MeasurableSet B)
    (hclass : ∀ t ∈ B, ∃ unit : ℚ_[prime], ‖unit‖ = 1 ∧ t = unit ^ 2 * value) :
    vectorHaar (T ∩ form ⁻¹' B) =
      form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
        value (Subtype.val ⁻¹' T) * scalarHaar B := by
  refine form.padicSquareBranchAtlasGlue_measure_inter_preimage_eq_mul prime point hpoint
    transverseHaar scalarHaar vectorHaar hT hsub hB fun t ht ↦ ?_
  obtain ⟨unit, hunit, rfl⟩ := hclass t ht
  exact form.padicSquareBranchAtlasGlue_preimage_unit_sq_mul prime point hpoint transverseHaar
    scalarHaar vectorHaar hT hsub unit hunit (hstable unit hunit) value

/-- Integral points: for a nonzero value `a`, an atlas covering the nonisotropic
vectors and a supplied value set `B` inside the unit-square class of `a`, the
volume of the integral vectors with value in `B` is the glued mass of the
integral points of `{Q = a}` times `ν(B)`. -/
theorem padicSquareBranchAtlasGlue_integralPoints_mul (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (hcover : {vector | form vector ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (value : ℚ_[prime]) (hvalue : value ≠ 0) {B : Set ℚ_[prime]} (hB : MeasurableSet B)
    (hclass : ∀ t ∈ B, ∃ unit : ℚ_[prime], ‖unit‖ = 1 ∧ t = unit ^ 2 * value) :
    vectorHaar ({vector : E | ‖vector‖ ≤ 1} ∩ form ⁻¹' B) =
      form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
        value {x | ‖x.val‖ ≤ 1} * scalarHaar B := by
  have hform : Continuous form := continuous_iff_continuousAt.mpr
    (fun vector ↦ (form.hasStrictFDerivAt_valueDifferential vector).continuousAt)
  set T : Set E := {vector | ‖vector‖ ≤ 1} ∩ {vector | form vector ≠ 0} with hTdef
  have hT : MeasurableSet T :=
    (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (isOpen_ne_fun hform continuous_const).measurableSet
  have hne : ∀ t ∈ B, t ≠ 0 := by
    intro t ht
    obtain ⟨unit, hunit, rfl⟩ := hclass t ht
    have hunit0 : unit ≠ 0 := by
      intro h; rw [h, norm_zero] at hunit; exact zero_ne_one hunit
    exact mul_ne_zero (pow_ne_zero 2 hunit0) hvalue
  have htube : T ∩ form ⁻¹' B = {vector : E | ‖vector‖ ≤ 1} ∩ form ⁻¹' B := by
    ext v
    simp only [hTdef, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hne _ h.2⟩, h.2⟩⟩
  have hslice : (Subtype.val ⁻¹' T : Set {vector : E // form vector = value}) =
      {x | ‖x.val‖ ≤ 1} := by
    ext x
    simp only [hTdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, x.property]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hvalue⟩⟩
  have hstable : ∀ unit : ℚ_[prime], ‖unit‖ = 1 → ∀ vector, unit • vector ∈ T ↔ vector ∈ T := by
    intro unit hunit vector
    have hunit0 : unit ≠ 0 := by
      intro h; rw [h, norm_zero] at hunit; exact zero_ne_one hunit
    simp only [hTdef, Set.mem_inter_iff, Set.mem_setOf_eq, norm_smul, hunit, one_mul,
      QuadraticMap.map_smul, smul_eq_mul, ne_eq, mul_eq_zero, hunit0,
      false_or]
  rw [← htube, ← hslice]
  exact form.padicSquareBranchAtlasGlue_measure_inter_preimage_eq_mul_of_unitSquareClass prime
    point hpoint transverseHaar scalarHaar vectorHaar hT (Set.inter_subset_right.trans hcover)
    hstable value hB hclass

/-- Open value neighborhood: for a nonzero value `a` there is an open neighborhood
`B₀` of `a` (from the identity unit-square chart) such that every measurable
`B ⊆ B₀` satisfies `vol({‖v‖ ≤ 1} ∩ Q⁻¹B) = glue_a(X_a(ℤ_p)) · ν(B)`. -/
theorem exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul
    (form : QuadraticForm ℚ_[prime] E)
    (point : ℕ → E) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure E)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (hcover : {vector | form vector ≠ 0} ⊆ ⋃ i, form.padicSquareBranchAtlasRegion prime point hpoint i)
    (value : ℚ_[prime]) (hvalue : value ≠ 0) :
    ∃ B₀ : Set ℚ_[prime], IsOpen B₀ ∧ value ∈ B₀ ∧ ∀ B ⊆ B₀, MeasurableSet B →
      vectorHaar ({vector : E | ‖vector‖ ≤ 1} ∩ form ⁻¹' B) =
        form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar
          value {x | ‖x.val‖ ≤ 1} * scalarHaar B := by
  set chart := Rat.unitSquareIdentityChart ℚ_[prime] with hchart
  refine ⟨(fun t ↦ t / value) ⁻¹' (Rat.padicUnitSquareScalarTarget prime ∩ Metric.sphere 0 1),
    ((Rat.isOpen_padicUnitSquareScalarTarget prime).inter
      (IsUltrametricDist.isOpen_sphere (0 : ℚ_[prime]) one_ne_zero)).preimage
      (continuous_id.div_const value), ?_, fun B hB hBm ↦ ?_⟩
  · refine ⟨⟨chart 1, chart.map_source (Rat.one_mem_unitSquareIdentityChart_source _), ?_⟩, ?_⟩
    · simp [hchart, div_self hvalue]
    · simp [div_self hvalue]
  refine form.padicSquareBranchAtlasGlue_integralPoints_mul prime point hpoint transverseHaar
    scalarHaar vectorHaar hcover value hvalue hBm fun t ht ↦ ?_
  obtain ⟨⟨w, hw, hwt⟩, hsph⟩ := hB ht
  have hsq : ((chart.symm w : ℚ_[prime]ˣ) : ℚ_[prime]) ^ 2 = (w : ℚ_[prime]) := by
    have h := chart.right_inv hw
    rw [hchart, Rat.unitSquareIdentityChart_apply] at h
    rw [← Units.val_pow_eq_pow_val, h]
  have hnorm : ‖t / value‖ = 1 := mem_sphere_zero_iff_norm.mp hsph
  refine ⟨(chart.symm w : ℚ_[prime]), ?_, ?_⟩
  · have h2 : ‖((chart.symm w : ℚ_[prime]ˣ) : ℚ_[prime])‖ ^ 2 = 1 := by
      rw [← norm_pow, hsq, hwt, hnorm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · rw [hsq, hwt, div_mul_cancel₀ t hvalue]

end QuadraticMap
