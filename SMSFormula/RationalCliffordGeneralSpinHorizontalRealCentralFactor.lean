import SMSFormula.RationalCliffordGeneralSpinHorizontalTwoSheet
import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity
import SMSFormula.RationalCliffordGeneralSpinHorizontalExactness
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalUnimodular

/-! The real GSpin central factor. The real horizontal differential Haar on
intrinsic `GSpin(V)(ℝ)` is glued from `Haar(ℝˣ) × μ_SO` through the central fiber
map `φ = (similitude, toSO)` with kernel `{1, -1}`, so (two sheets)

`μ_GSpin(φ⁻¹ B) = 2 · (Haar × μ_SO)(B ∩ range φ)`.

Over `ℝ` every `SO` point lifts (field surjectivity), and the fiber of `range φ`
over `g` is `ν(y)·(ℝˣ)²`, a half-line. For a measurable `T ⊆ ℝˣ` stable under `-1`
each slice therefore has Haar mass `Haar(T)/2`, and

`μ_GSpin({ν ∈ T, toSO ∈ S}) = Haar(T) · μ_SO(S)`

for every measurable `S`: the archimedean analogue of the p-adic
`v^G = Haar(ℤ_p^×) · vol_SO`. The central factor `Haar(T)` is the same for `V` and
`W`, so it cancels in `z_G/z_H` for matched `T`. No section, sheet, square root or
normalization is chosen. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1200000

noncomputable local instance realCentralUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance realCentralUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance realCentralSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance realCentralSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

local instance realCentralSchemeSOIsTopologicalGroup :
    IsTopologicalGroup (V.specialOrthogonalMatrixGroup ℝ) := by
  change IsTopologicalGroup
    (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℝ)))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Real two-sheet mass: `μ_GSpin(φ⁻¹ B) = 2 · (Haar × μ_SO)(B ∩ range φ)`. -/
theorem realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage
    {B : Set (ℝˣ × V.specialOrthogonalMatrixGroup ℝ)} (hB : MeasurableSet B) :
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹' B) =
      2 * V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure
        (B ∩ Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)) := by
  have hfe := V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
  have hone := V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
  have hcont : Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) := by
    refine continuous_of_continuousAt_one
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) ?_
    have h := V.realCliffordGeneralSpinCentralFiberIdentityChart.continuousAt hone
    rwa [← hfe] at h
  exact MeasureTheory.TranslatedHomChart.gluedMeasure_preimage_eq_two_mul
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ) _ _ hfe hone _
    (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint_ne_one V ℝ)
    (MeasureTheory.TranslatedHomChart.fiber_iff_of_ker_eq_pair _
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_ker_eq_pair V ℝ))
    hcont hB

/-- A real unit is a square of a unit iff it is positive. -/
theorem Units.exists_sq_eq_iff_pos (u : ℝˣ) : (∃ b : ℝˣ, u = b ^ 2) ↔ 0 < (u : ℝ) := by
  constructor
  · rintro ⟨b, rfl⟩
    simpa [pow_two] using mul_self_pos.mpr b.ne_zero
  · intro hu
    refine ⟨Units.mk0 (Real.sqrt u) (Real.sqrt_ne_zero'.mpr hu), ?_⟩
    ext
    simp [Real.sq_sqrt hu.le]

/-- Half-line Haar: for `T ⊆ ℝˣ` stable under `-1`, each half `T ∩ {0 < c t}` carries
half of the Haar mass of `T`. -/
theorem two_mul_haar_inter_half (T : Set ℝˣ) (hT : MeasurableSet T)
    (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T) (c : ℝˣ) :
    2 * (Measure.haar : Measure ℝˣ) (T ∩ {t | 0 < (t : ℝ) * (c : ℝ)}) =
      (Measure.haar : Measure ℝˣ) T := by
  have hc := c.ne_zero
  have hmP : MeasurableSet {t : ℝˣ | 0 < (t : ℝ) * (c : ℝ)} :=
    (isOpen_lt continuous_const ((Units.continuous_val).mul continuous_const)).measurableSet
  have hmN : MeasurableSet {t : ℝˣ | 0 < -((t : ℝ) * (c : ℝ))} :=
    (isOpen_lt continuous_const ((Units.continuous_val).mul continuous_const).neg).measurableSet
  have hsplit : T = (T ∩ {t | 0 < (t : ℝ) * (c : ℝ)}) ∪ (T ∩ {t | 0 < -((t : ℝ) * (c : ℝ))}) := by
    ext t
    simp only [mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro ht
      rcases lt_or_gt_of_ne (mul_ne_zero t.ne_zero hc) with h | h
      · exact Or.inr ⟨ht, by linarith⟩
      · exact Or.inl ⟨ht, h⟩
    · rintro (⟨ht, -⟩ | ⟨ht, -⟩) <;> exact ht
  have hdisj : Disjoint (T ∩ {t | 0 < (t : ℝ) * (c : ℝ)}) (T ∩ {t | 0 < -((t : ℝ) * (c : ℝ))}) := by
    rw [Set.disjoint_left]
    rintro t ⟨-, h1⟩ ⟨-, h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hneghalf : (Measure.haar : Measure ℝˣ) (T ∩ {t | 0 < -((t : ℝ) * (c : ℝ))}) =
      (Measure.haar : Measure ℝˣ) (T ∩ {t | 0 < (t : ℝ) * (c : ℝ)}) := by
    have hpre : (fun t : ℝˣ ↦ (-1 : ℝˣ) * t) ⁻¹' (T ∩ {t | 0 < (t : ℝ) * (c : ℝ)}) =
        T ∩ {t | 0 < -((t : ℝ) * (c : ℝ))} := by
      ext t
      simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, neg_mul, one_mul, Units.val_neg]
      rw [hneg]
    rw [← hpre, measure_preimage_mul]
  conv_rhs => rw [hsplit]
  rw [measure_union hdisj (hT.inter hmN), hneghalf, two_mul]

variable {V}

/-- The slice of the central-fiber image over `g = toSO y`: `ν(y) · (ℝˣ)²`. -/
theorem mem_range_centralFiberGroupHom_iff (y : V.CliffordGeneralSpinIntrinsicPoint ℝ) (t : ℝˣ) :
    (t, CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℝ y) ∈
        Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) ↔
      0 < (t : ℝ) * (y.similitude : ℝ) := by
  have hy := y.similitude.ne_zero
  constructor
  · rintro ⟨x, hx⟩
    have hxν : x.similitude = t := congrArg Prod.fst hx
    have hxπ : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ x =
        CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y := congrArg Prod.snd hx
    have hker : x * y⁻¹ ∈ (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, mul_inv_cancel]
    rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
      at hker
    obtain ⟨a, ha⟩ := hker
    have hxa : x = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ a * y := by
      rw [ha, inv_mul_cancel_right]
    have htt : t = a ^ 2 * y.similitude := by
      rw [← hxν, hxa, CliffordGeneralSpinIntrinsicPoint.mul_similitude]; rfl
    rw [htt]
    push_cast
    have := mul_self_pos.mpr (mul_ne_zero (a.ne_zero) hy)
    nlinarith [this]
  · intro hpos
    have hq : 0 < ((t * y.similitude⁻¹ : ℝˣ) : ℝ) := by
      push_cast
      have : 0 < (y.similitude : ℝ) * (y.similitude : ℝ) := mul_self_pos.mpr hy
      rw [show (t : ℝ) * (y.similitude : ℝ)⁻¹ = (t : ℝ) * (y.similitude : ℝ) /
        ((y.similitude : ℝ) * (y.similitude : ℝ)) by field_simp]
      exact div_pos hpos this
    obtain ⟨b, hb⟩ := (Units.exists_sq_eq_iff_pos _).mpr hq
    refine ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y, Prod.ext ?_ ?_⟩
    · change (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y).similitude = t
      rw [CliffordGeneralSpinIntrinsicPoint.mul_similitude]
      change b ^ 2 * y.similitude = t
      rw [← hb, inv_mul_cancel_right]
    · change CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y) =
        CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y
      rw [map_mul]
      have : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b ∈
          (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
        rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
        exact ⟨b, rfl⟩
      rw [MonoidHom.mem_ker.mp this, one_mul]

variable (V)

set_option backward.isDefEq.respectTransparency false in
/-- The real central factor: for measurable `T ⊆ ℝˣ` stable under `-1` and measurable
`S ⊆ SO(V)(ℝ)`, `μ_GSpin({ν ∈ T, toSO ∈ S}) = Haar(T) · μ_SO(S)`. -/
theorem realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber
    (T : Set ℝˣ) (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (S : Set (V.specialOrthogonalMatrixGroup ℝ)) (hS : MeasurableSet S) :
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹' (T ×ˢ S)) =
      (Measure.haar : Measure ℝˣ) T * V.realInvariantDifferentialGroupMeasure S := by
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by
    infer_instance
  have hRo := V.isOpen_realCliffordGeneralSpinCentralFiberImage
  rw [MonoidHom.coe_range] at hRo
  have hA : MeasurableSet ((T ×ˢ S) ∩
      Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)) :=
    (hT.prod hS).inter hRo.measurableSet
  have hslice : ∀ g : V.specialOrthogonalMatrixGroup ℝ,
      2 * (Measure.haar : Measure ℝˣ) ((fun t ↦ (t, g)) ⁻¹' ((T ×ˢ S) ∩
        Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ))) =
      S.indicator (fun _ ↦ (Measure.haar : Measure ℝˣ) T) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      obtain ⟨y, hyg⟩ := CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective V ℝ g
      have hsl : (fun t ↦ (t, g)) ⁻¹' ((T ×ˢ S) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)) =
          T ∩ {t | 0 < (t : ℝ) * (y.similitude : ℝ)} := by
        ext t
        simp only [mem_preimage, mem_inter_iff, mem_prod, mem_setOf_eq]
        rw [← hyg, mem_range_centralFiberGroupHom_iff]
        simp [hyg, hg]
      rw [hsl, two_mul_haar_inter_half T hT hneg]
    · rw [Set.indicator_of_notMem hg]
      exact mul_eq_zero_of_right _ (measure_mono_null (fun t ht ↦ (hg ht.1.2).elim) measure_empty)
  rw [V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage (hT.prod hS),
    realCliffordGeneralSpinHorizontalDifferentialProductMeasure]
  erw [Measure.prod_apply_symm hA]
  rw [← lintegral_const_mul _ (measurable_measure_prodMk_right hA)]
  simp_rw [hslice]
  rw [lintegral_indicator_const hS]
  rfl

end RationalQuadraticSpaceMatrix
