import SMSFormula.AdelicSpinDiagonalBlockQuotientVolume
import SMSFormula.AdelicSpinFiniteBlockCylinder
import SMSFormula.HaarMeasureEqOfApplyEq

/-!
# The adelic block measure identity from local identities

The raw differential Spin measure of `U = T ⊥ ⟨f₀f₁f₂⟩` is the image of the product of two raw
differential Spin measures of `T` under the block isomorphism `Φ_𝔸`, provided:
* (local) at every finite place `Φ_v` carries `μ_{T,v} ⊗ μ_{T,v}` to `c_v μ_{U,v}`, `c_v = 1`
  outside a finite set, and `Φ_v` matches the integral loci there;
* (real) the real total masses satisfy `μ_{T,∞}(1)² = c_∞ μ_{U,∞}(1)`;
* (product formula) `c_∞ ∏_v c_v = 1`.
Both raw measures are Haar, so they agree once they agree on one set of finite positive mass;
the set used is the fully integral cylinder, evaluated by the block-source identity.  The
finite scales are compared on the same good set.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix Filter Topology
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

local instance blockAssemblyFiniteGroupMeasurableSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup := borel _

local instance blockAssemblyFiniteGroupBorelSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup := ⟨rfl⟩

/-! ## Finite scales over the same good set -/

section FiniteScale

local instance finiteScaleDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

theorem integralVolume_ne_zero_of_not_mem {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    {v : IsDedekindDomain.HeightOneSpectrum ℤ} (hv : v ∉ S) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v ≠ 0 :=
  V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero S
    ⟨v, fun h ↦ by
      rcases Finset.mem_union.1 h with h | h
      · exact hv h
      · exact hv (hV h)⟩

/-- Beyond the primes of `S` the inverse-volume cutoff splits off the block weight of `S`. -/
theorem integralInverseVolumePartialProduct_eq_blockWeight_mul {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    {N : ℕ} (hN : S ⊆ cliffordSpinCandidateRationalHeightOnePlacesUpTo N) :
    V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
        ∏ v ∈ cliffordSpinCandidateRationalHeightOnePlacesUpTo N \ S,
          (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
  rw [cliffordSpinCandidateIntegralInverseVolumePartialProduct,
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces, ← Finset.prod_union]
  · congr 1
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hvN, hvb⟩
      by_cases hvS : v ∈ S
      · exact Or.inl ⟨hvS, hvb⟩
      · exact Or.inr ⟨hvN, hvS⟩
    · rintro (⟨hvS, hvb⟩ | ⟨hvN, hvS⟩)
      · exact ⟨hN hvS, hvb⟩
      · exact ⟨hvN, fun hb ↦ hvS (hV hb)⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.1 hv').2 (Finset.mem_sdiff.1 hv).1

theorem exists_placesUpTo_superset (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → S ⊆ cliffordSpinCandidateRationalHeightOnePlacesUpTo N := by
  refine ⟨S.sup fun v ↦ (Rat.HeightOneSpectrum.primesEquiv v).1, fun N hN v hv ↦ ?_⟩
  rw [mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff]
  exact (Finset.le_sup (f := fun v ↦ (Rat.HeightOneSpectrum.primesEquiv v).1) hv).trans hN

/-- The finite scales over the same good set: if the good integral volumes of `W` are the squares of
those of `V`, then `s_W w_W(S) = (s_V w_V(S))²`. -/
theorem finiteScale_mul_blockWeight_eq_sq {n m : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (W : RationalQuadraticSpaceMatrix m) {sV sW : ℝ≥0}
    (CV : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate sV)
    (CW : W.CliffordSpinCandidateRawDifferentialVolumeProductCertificate sW)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hvol : ∀ v ∉ S, W.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v *
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v) :
    (sW : ℝ≥0∞) * W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S =
      ((sV : ℝ≥0∞) * V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) *
        ((sV : ℝ≥0∞) * V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) := by
  obtain ⟨N₀, hN₀⟩ := exists_placesUpTo_superset S
  set wV := V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S with hwV
  set wW := W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S with hwW
  have hwV0 : wV ≠ 0 := V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S
  have hwVt : wV ≠ ⊤ := V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top S
  have hwW0 : wW ≠ 0 := W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S
  have hwWt : wW ≠ ⊤ := W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top S
  let QV : ℕ → ℝ≥0∞ := fun N ↦ ∏ v ∈ cliffordSpinCandidateRationalHeightOnePlacesUpTo N \ S,
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹
  let QW : ℕ → ℝ≥0∞ := fun N ↦ ∏ v ∈ cliffordSpinCandidateRationalHeightOnePlacesUpTo N \ S,
    (W.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹
  have hQV : Tendsto QV atTop (𝓝 (wV⁻¹ * (sV : ℝ≥0∞)⁻¹)) := by
    have h := ENNReal.Tendsto.const_mul CV.inverseVolumeProduct_tendsto (a := wV⁻¹) (Or.inr (ENNReal.inv_ne_top.2 hwV0))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with N hN
    rw [V.integralInverseVolumePartialProduct_eq_blockWeight_mul hV (hN₀ N hN), ← mul_assoc,
      ENNReal.inv_mul_cancel hwV0 hwVt, one_mul]
  have hQW : Tendsto QW atTop (𝓝 (wW⁻¹ * (sW : ℝ≥0∞)⁻¹)) := by
    have h := ENNReal.Tendsto.const_mul CW.inverseVolumeProduct_tendsto (a := wW⁻¹) (Or.inr (ENNReal.inv_ne_top.2 hwW0))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with N hN
    rw [W.integralInverseVolumePartialProduct_eq_blockWeight_mul hW (hN₀ N hN), ← mul_assoc,
      ENNReal.inv_mul_cancel hwW0 hwWt, one_mul]
  have hQWV : ∀ N, QW N = QV N * QV N := fun N ↦ by
    simp only [QW, QV, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have hvS := (Finset.mem_sdiff.1 hv).2
    rw [hvol v hvS, ENNReal.mul_inv (Or.inl (integralVolume_ne_zero_of_not_mem V hV hvS))
      (Or.inl (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v))]
  have hsV : (sV : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 CV.finiteScale_ne_zero)
  have hlimV : wV⁻¹ * (sV : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hwV0) hsV
  have hQV2 : Tendsto (fun N ↦ QV N * QV N) atTop
      (𝓝 ((wV⁻¹ * (sV : ℝ≥0∞)⁻¹) * (wV⁻¹ * (sV : ℝ≥0∞)⁻¹))) :=
    ENNReal.Tendsto.mul hQV (Or.inr hlimV) hQV (Or.inr hlimV)
  have heq : wW⁻¹ * (sW : ℝ≥0∞)⁻¹ = (wV⁻¹ * (sV : ℝ≥0∞)⁻¹) * (wV⁻¹ * (sV : ℝ≥0∞)⁻¹) :=
    tendsto_nhds_unique (hQW.congr fun N ↦ hQWV N) hQV2
  have hsV0 : (sV : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 CV.finiteScale_ne_zero
  have hsW0 : (sW : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 CW.finiteScale_ne_zero
  have h1 : (wW⁻¹ * (sW : ℝ≥0∞)⁻¹)⁻¹ = wW * sW := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hwWt)) (Or.inl (ENNReal.inv_ne_top.2 hwW0)),
      inv_inv, inv_inv]
  have h2 : (wV⁻¹ * (sV : ℝ≥0∞)⁻¹)⁻¹ = wV * sV := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hwVt)) (Or.inl (ENNReal.inv_ne_top.2 hwV0)),
      inv_inv, inv_inv]
  have h3 := ENNReal.mul_inv (a := wV⁻¹ * (sV : ℝ≥0∞)⁻¹) (b := wV⁻¹ * (sV : ℝ≥0∞)⁻¹)
    (Or.inr hlimV) (Or.inl hlimV)
  have key := congrArg (fun x : ℝ≥0∞ ↦ x⁻¹) heq
  simp only at key
  rw [h1, h3, h2] at key
  rw [mul_comm (sW : ℝ≥0∞), mul_comm (sV : ℝ≥0∞)]
  exact key

end FiniteScale

/-! ## Φ is placewise -/

section Placewise

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

theorem diagonalBlock_realFinite_fst (x y : T.FullAdelicCliffordSpinCandidateGroup) :
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
        (T.diagonalBlockSpinGroupMulEquiv hT hδ RationalAdele (x, y))).1 =
      T.diagonalBlockSpinGroupMulEquiv hT hδ ℝ
        ((T.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).1,
          (T.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv y).1) := by
  simp only [fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv_apply_real,
    cliffordSpinCandidateGroupMap_apply]
  rw [T.diagonalBlockSpinGroupMulEquiv_comp hT hδ, T.diagonalBlockSpinGroupMulEquiv_comp hT hδ]
  rfl

theorem diagonalBlock_realFinite_snd (x y : T.FullAdelicCliffordSpinCandidateGroup) :
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
        (T.diagonalBlockSpinGroupMulEquiv hT hδ RationalAdele (x, y))).2 =
      T.diagonalBlockSpinGroupMulEquiv hT hδ RationalFiniteAdele
        ((T.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).2,
          (T.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv y).2) := by
  simp only [fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv_apply_finite,
    cliffordSpinCandidateGroupMap_apply]
  rw [T.diagonalBlockSpinGroupMulEquiv_comp hT hδ]
  rfl

theorem diagonalBlock_finiteComponent (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x y : T.FiniteAdelicCliffordSpinCandidateGroup) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (T.diagonalBlockSpinGroupMulEquiv hT hδ RationalFiniteAdele (x, y)) =
      T.diagonalBlockSpinGroupMulEquiv hT hδ _
        (T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x,
          T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v y) := by
  simp only [finiteAdelicCliffordSpinCandidateHeightOneComponentHom_apply]
  rw [T.diagonalBlockSpinGroupMulEquiv_comp hT hδ]

end Placewise

/-! ## Raw full-adelic mass of real × finite rectangles -/

theorem fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite_preimage {n : ℕ}
    (V : RationalQuadraticSpaceMatrix n) (s : ℝ≥0) {A : Set V.RealCliffordSpinCandidateGroup}
    {C : Set V.FiniteAdelicCliffordSpinCandidateGroup} (hA : MeasurableSet A) (hC : MeasurableSet C) :
    V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure s
        (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv ⁻¹' (A ×ˢ C)) =
      V.realCliffordSpinCandidateChartGluedMeasure A *
        V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure s C := by
  have h := congrArg (fun μ : Measure _ ↦ μ (A ×ˢ C))
    (V.map_fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite s)
  simp only at h
  rw [Measure.map_apply (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph.measurable)
    (hA.prod hC)] at h
  rw [show (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv ⁻¹' (A ×ˢ C)) =
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph ⁻¹' (A ×ˢ C) from rfl, h]
  haveI : SFinite (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure s) := by
    unfold finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    haveI := V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
    infer_instance
  exact Measure.prod_prod _ _

/-! ## The assembly -/

section Assembly

local instance blockAssemblyDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance blockAssemblyPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem mem_admissibleExceptionalPlaces_iff {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S ↔ v ∈ S := by
  unfold cliffordSpinCandidateAdmissibleExceptionalPlaces
  rw [Finset.mem_union]
  exact ⟨fun h ↦ h.elim id (fun h ↦ hV h), Or.inl⟩

theorem admissibleExceptionalPlaces_eq {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    V.cliffordSpinCandidateAdmissibleExceptionalPlaces S = S := by
  ext v
  exact V.mem_admissibleExceptionalPlaces_iff hV v

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

/-- The local block map at a height-one place. -/
abbrev diagonalBlockLocalEquiv (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]

/-- Local good volumes: under the local identity with constant one and matching integral loci, the
integral volume of `U` is the square of that of `T`. -/
theorem diagonalBlock_integralVolume_eq_sq (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hL : Measure.map (T.diagonalBlockLocalEquiv hT hδ v)
        ((T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v).prod
          (T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)) =
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)
    (hK : ∀ a b : T.HeightOnePadicCliffordSpinCandidateGroup v,
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).HeightOnePadicCliffordSpinCandidateIsIntegral v
          (T.diagonalBlockLocalEquiv hT hδ v (a, b)) ↔
        T.HeightOnePadicCliffordSpinCandidateIsIntegral v a ∧ T.HeightOnePadicCliffordSpinCandidateIsIntegral v b) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      T.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v *
        T.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v := by
  have hmeasU := ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).isOpen_heightOnePadicCliffordSpinCandidateIsIntegral
    v).measurableSet
  have hmeasT := (T.isOpen_heightOnePadicCliffordSpinCandidateIsIntegral v).measurableSet
  unfold heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
  change (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v _ =
    T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v _ *
      T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v _
  rw [← hL, Measure.map_apply (map_continuous (T.diagonalBlockLocalEquiv hT hδ v)).measurable hmeasU]
  have hpre : (T.diagonalBlockLocalEquiv hT hδ v) ⁻¹'
      {g | (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).HeightOnePadicCliffordSpinCandidateIsIntegral v g} =
      {g | T.HeightOnePadicCliffordSpinCandidateIsIntegral v g} ×ˢ
        {g | T.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
    ext ⟨a, b⟩
    exact hK a b
  rw [hpre, Measure.prod_prod]

/-- Local exceptional masses: `c_v · μ_{U,v}(Φ_v(K × K)) = μ_{T,v}(K)²`. -/
theorem diagonalBlock_local_mass (v : IsDedekindDomain.HeightOneSpectrum ℤ) (c : ℝ≥0∞)
    (hL : Measure.map (T.diagonalBlockLocalEquiv hT hδ v)
        ((T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v).prod
          (T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)) =
      c • (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)
    {K : Set (T.HeightOnePadicCliffordSpinCandidateGroup v)} (hK : MeasurableSet K) :
    c * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
        ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K ×ˢ K)) =
      T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v K *
        T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v K := by
  have hmeas : MeasurableSet ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K ×ˢ K)) :=
    (map_continuous (T.diagonalBlockLocalEquiv hT hδ v).symm).measurable (hK.prod hK)
  have h := congrArg (fun μ : Measure _ ↦ μ ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K ×ˢ K))) hL
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [← h, Measure.map_apply (map_continuous (T.diagonalBlockLocalEquiv hT hδ v)).measurable hmeas,
    ← Set.preimage_comp]
  have : ((T.diagonalBlockLocalEquiv hT hδ v).symm ∘ (T.diagonalBlockLocalEquiv hT hδ v)) = id := by
    funext p
    exact (T.diagonalBlockLocalEquiv hT hδ v).symm_apply_apply p
  rw [this, Set.preimage_id, Measure.prod_prod]

/-- The block cylinders correspond: `Φ_f(x, y)` lies in the `U`-cylinder of the transported
neighbourhoods iff `x` and `y` lie in the `T`-cylinder, whenever the integral loci match off `S`. -/
theorem diagonalBlock_mem_finiteBlockCylinder_iff {S₀ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hTS : T.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hUS : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hS₀ : S₀ ⊆ S)
    (HK : ∀ v ∉ S₀, ∀ a b : T.HeightOnePadicCliffordSpinCandidateGroup v,
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).HeightOnePadicCliffordSpinCandidateIsIntegral v
          (T.diagonalBlockLocalEquiv hT hδ v (a, b)) ↔
        T.HeightOnePadicCliffordSpinCandidateIsIntegral v a ∧ T.HeightOnePadicCliffordSpinCandidateIsIntegral v b)
    (K : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, Set (T.HeightOnePadicCliffordSpinCandidateGroup v))
    (x y : T.FiniteAdelicCliffordSpinCandidateGroup) :
    T.diagonalBlockSpinGroupMulEquiv hT hδ RationalFiniteAdele (x, y) ∈
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteBlockCylinder S
          (fun v ↦ (T.diagonalBlockLocalEquiv hT hδ v.1).symm ⁻¹' (K v.1 ×ˢ K v.1)) ↔
      x ∈ T.finiteBlockCylinder S (fun v ↦ K v.1) ∧ y ∈ T.finiteBlockCylinder S (fun v ↦ K v.1) := by
  have hU := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).mem_admissibleExceptionalPlaces_iff hUS
  have hTe := T.mem_admissibleExceptionalPlaces_iff hTS
  rw [mem_finiteBlockCylinder_iff, mem_finiteBlockCylinder_iff, mem_finiteBlockCylinder_iff]
  simp only [T.diagonalBlock_finiteComponent hT hδ]
  have hsymm : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (a b : T.HeightOnePadicCliffordSpinCandidateGroup v),
      (T.diagonalBlockLocalEquiv hT hδ v).symm (T.diagonalBlockSpinGroupMulEquiv hT hδ _ (a, b)) = (a, b) :=
    fun v a b ↦ (T.diagonalBlockLocalEquiv hT hδ v).symm_apply_apply (a, b)
  simp only [Set.mem_preimage, hsymm, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : ∀ v : {v // v ∈ T.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 x ∈ K v.1 ∧
          T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y ∈ K v.1 :=
      fun v ↦ h1 ⟨v.1, (hU v.1).2 ((hTe v.1).1 v.2)⟩
    have hI : ∀ v, v ∉ T.cliffordSpinCandidateAdmissibleExceptionalPlaces S →
        T.HeightOnePadicCliffordSpinCandidateIsIntegral v (T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x) ∧
          T.HeightOnePadicCliffordSpinCandidateIsIntegral v
            (T.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v y) := fun v hv ↦ by
      have hvS : v ∉ S := fun h ↦ hv ((hTe v).2 h)
      exact (HK v (fun h ↦ hvS (hS₀ h)) _ _).1 (h2 v (fun h ↦ hvS ((hU v).1 h)))
    exact ⟨⟨fun v ↦ (hx v).1, fun v hv ↦ (hI v hv).1⟩, ⟨fun v ↦ (hx v).2, fun v hv ↦ (hI v hv).2⟩⟩
  · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    refine ⟨fun v ↦ ⟨hx1 ⟨v.1, (hTe v.1).2 ((hU v.1).1 v.2)⟩, hy1 ⟨v.1, (hTe v.1).2 ((hU v.1).1 v.2)⟩⟩,
      fun v hv ↦ ?_⟩
    have hvS : v ∉ S := fun h ↦ hv ((hU v).2 h)
    have hvT : v ∉ T.cliffordSpinCandidateAdmissibleExceptionalPlaces S := fun h ↦ hvS ((hTe v).1 h)
    exact (HK v (fun h ↦ hvS (hS₀ h)) _ _).2 ⟨hx2 v hvT, hy2 v hvT⟩

/-- The adelic block measure identity from the local identities, the real total masses and the
product formula. -/
theorem map_diagonalBlock_rawDifferentialGroupMeasure_of_local {sT sU : ℝ≥0}
    (CT : T.CliffordSpinCandidateRawDifferentialVolumeProductCertificate sT)
    (CU : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      sU)
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (c : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0)
    (cInf : ℝ≥0) (hc0 : ∀ v, c v ≠ 0) (hc1 : ∀ v ∉ S₀, c v = 1)
    (HL : ∀ v, Measure.map (T.diagonalBlockLocalEquiv hT hδ v)
        ((T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v).prod
          (T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)) =
      (c v : ℝ≥0∞) •
        (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v)
    (HK : ∀ v ∉ S₀, ∀ a b : T.HeightOnePadicCliffordSpinCandidateGroup v,
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).HeightOnePadicCliffordSpinCandidateIsIntegral v
          (T.diagonalBlockLocalEquiv hT hδ v (a, b)) ↔
        T.HeightOnePadicCliffordSpinCandidateIsIntegral v a ∧ T.HeightOnePadicCliffordSpinCandidateIsIntegral v b)
    (HR : T.realCliffordSpinCandidateChartGluedMeasure Set.univ * T.realCliffordSpinCandidateChartGluedMeasure Set.univ =
      (cInf : ℝ≥0∞) * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ)
    (hR0 : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ ≠ 0)
    (hRtop : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ ≠ ⊤)
    (Hprod : (cInf : ℝ≥0∞) * ∏ v ∈ S₀, (c v : ℝ≥0∞) = 1) :
    Measure.map (T.diagonalBlockFullAdelicEquiv hT hδ)
        ((T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sT).prod
          (T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sT)) =
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sU := by
  -- compact neighbourhoods of the identity at every place
  choose K hKc hKn using fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
    exists_compact_mem_nhds (1 : T.HeightOnePadicCliffordSpinCandidateGroup v)
  have hKmeas : ∀ v, MeasurableSet (K v) := fun v ↦ by
    letI : T2Space (T.HeightOnePadicCliffordSpinCandidateGroup v) := T.cliffordSpinCandidateGroupT2Space _
    exact (hKc v).measurableSet
  have hμK0 : ∀ v, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) ≠ 0 := fun v ↦ by
    haveI := T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure v
    exact (Measure.measure_pos_of_mem_nhds _ (hKn v)).ne'
  have hμKt : ∀ v, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) ≠ ⊤ := fun v ↦ by
    haveI := T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure v
    exact (hKc v).measure_lt_top.ne
  -- the common finite set of places
  let S := S₀ ∪ T.cliffordSpinCandidateAdmissibleBadPlaces ∪
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleBadPlaces
  have hS₀ : S₀ ⊆ S := fun v hv ↦ Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hTS : T.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S :=
    fun v hv ↦ Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hUS : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleBadPlaces ⊆ S :=
    fun v hv ↦ Finset.mem_union_right _ hv
  -- the evaluation sets
  let CTc := T.finiteBlockCylinder S (fun v ↦ K v.1)
  let CUc := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteBlockCylinder S
    (fun v ↦ (T.diagonalBlockLocalEquiv hT hδ v.1).symm ⁻¹' (K v.1 ×ˢ K v.1))
  have hEU : ∀ v : {v // v ∈ (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleExceptionalPlaces S},
      MeasurableSet ((T.diagonalBlockLocalEquiv hT hδ v.1).symm ⁻¹' (K v.1 ×ˢ K v.1)) := fun v ↦
    (map_continuous (T.diagonalBlockLocalEquiv hT hδ v.1).symm).measurable ((hKmeas v.1).prod (hKmeas v.1))
  have hCT : MeasurableSet CTc := T.measurableSet_finiteBlockCylinder S (fun v ↦ hKmeas v.1)
  have hCU : MeasurableSet CUc := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).measurableSet_finiteBlockCylinder S hEU
  let WT := T.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv ⁻¹' (Set.univ ×ˢ CTc)
  let WU := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv ⁻¹'
    (Set.univ ×ˢ CUc)
  have hWU : MeasurableSet WU :=
    (map_continuous (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv).measurable
      (MeasurableSet.univ.prod hCU)
  have hpre : (T.diagonalBlockFullAdelicEquiv hT hδ) ⁻¹' WU = WT ×ˢ WT := by
    ext ⟨x, y⟩
    simp only [WU, WT, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    change ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
      (T.diagonalBlockSpinGroupMulEquiv hT hδ RationalAdele (x, y))).2 ∈ CUc ↔ _
    rw [T.diagonalBlock_realFinite_snd hT hδ]
    exact T.diagonalBlock_mem_finiteBlockCylinder_iff hT hδ hTS hUS hS₀ HK K _ _
  -- Haar structure
  haveI := T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure sT CT
  haveI := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
    sU CU
  haveI := T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_sFinite sT
  -- local inputs
  have hloc : ∀ v, (c v : ℝ≥0∞) *
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
        ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v)) =
      T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) *
        T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) :=
    fun v ↦ T.diagonalBlock_local_mass hT hδ v (c v) (HL v) (hKmeas v)
  have hvol : ∀ v ∉ S,
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
        T.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v *
          T.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v := fun v hv ↦ by
    have hv₀ : v ∉ S₀ := fun h ↦ hv (hS₀ h)
    refine T.diagonalBlock_integralVolume_eq_sq hT hδ v ?_ (HK v hv₀)
    rw [HL v, hc1 v hv₀, ENNReal.coe_one, one_smul]
  have hscale := finiteScale_mul_blockWeight_eq_sq T (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ) CT CU hTS hUS hvol
  -- masses of the evaluation sets
  have hmT := T.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite_preimage sT
    MeasurableSet.univ hCT
  rw [T.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_finiteBlockCylinder S sT (fun v ↦ hKmeas v.1)]
    at hmT
  have hmU := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite_preimage
    sU MeasurableSet.univ hCU
  rw [(T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_finiteBlockCylinder
    S sU hEU] at hmU
  -- products over the common set `S`
  have hPT : (∏ v : {v // v ∈ T.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
      T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1 (K v.1)) =
      ∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) := by
    rw [Finset.prod_coe_sort (T.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
      (fun v ↦ T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v)),
      T.admissibleExceptionalPlaces_eq hTS]
  have hPU : (∏ v : {v // v ∈
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleExceptionalPlaces S},
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
        ((T.diagonalBlockLocalEquiv hT hδ v.1).symm ⁻¹' (K v.1 ×ˢ K v.1))) =
      ∏ v ∈ S, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
        ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v)) := by
    rw [Finset.prod_coe_sort
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateAdmissibleExceptionalPlaces S)
      (fun v ↦ (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
        ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v))),
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).admissibleExceptionalPlaces_eq hUS]
  rw [hPT] at hmT
  rw [hPU] at hmU
  have hPc : ∏ v ∈ S, (c v : ℝ≥0∞) = ∏ v ∈ S₀, (c v : ℝ≥0∞) :=
    (Finset.prod_subset hS₀ fun v _ hv ↦ by rw [hc1 v hv, ENNReal.coe_one]).symm
  have hPUT : (∏ v ∈ S, (c v : ℝ≥0∞)) *
      ∏ v ∈ S, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
        ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v)) =
      (∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v)) *
        ∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ ↦ hloc v
  -- nonvanishing and finiteness of the `U`-mass
  have hEU0 : ∀ v, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
      ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v)) ≠ 0 := fun v h ↦ by
    have := hloc v
    rw [h, mul_zero] at this
    exact (mul_ne_zero (hμK0 v) (hμK0 v)) this.symm
  have hEUt : ∀ v, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
      ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v)) ≠ ⊤ := fun v h ↦ by
    have := hloc v
    rw [h, ENNReal.mul_top (ENNReal.coe_ne_zero.2 (hc0 v))] at this
    exact ENNReal.mul_ne_top (hμKt v) (hμKt v) this.symm
  have hsU0 : (sU : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 CU.finiteScale_ne_zero
  have hwU0 := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S
  have hwUt := (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top S
  have hmU0 : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sU
      WU ≠ 0 := by
    rw [hmU]
    exact mul_ne_zero hR0 (mul_ne_zero (mul_ne_zero hsU0 hwU0) (Finset.prod_ne_zero_iff.2 fun v _ ↦ hEU0 v))
  have hmUt : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure sU
      WU ≠ ⊤ := by
    rw [hmU]
    exact ENNReal.mul_ne_top hRtop (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hwUt)
      (ENNReal.prod_ne_top fun v _ ↦ hEUt v))
  -- the evaluation
  refine Measure.eq_of_isHaarMeasure_of_apply_eq _ _ hmU0 hmUt ?_
  rw [Measure.map_apply (map_continuous (T.diagonalBlockFullAdelicEquiv hT hδ)).measurable hWU, hpre,
    Measure.prod_prod, hmT, hmU]
  calc T.realCliffordSpinCandidateChartGluedMeasure Set.univ *
          ((sT : ℝ≥0∞) * T.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
            ∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v)) *
        (T.realCliffordSpinCandidateChartGluedMeasure Set.univ *
          ((sT : ℝ≥0∞) * T.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
            ∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v))) =
        (T.realCliffordSpinCandidateChartGluedMeasure Set.univ *
            T.realCliffordSpinCandidateChartGluedMeasure Set.univ) *
          (((sT : ℝ≥0∞) * T.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) *
            ((sT : ℝ≥0∞) * T.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S)) *
          ((∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v)) *
            ∏ v ∈ S, T.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v (K v)) := by ring
    _ = ((cInf : ℝ≥0∞) * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure
            Set.univ) *
          ((sU : ℝ≥0∞) * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) *
          ((∏ v ∈ S, (c v : ℝ≥0∞)) *
            ∏ v ∈ S, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
              ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v))) := by
      rw [HR, hscale, hPUT]
    _ = (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).realCliffordSpinCandidateChartGluedMeasure Set.univ *
          ((sU : ℝ≥0∞) * (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
            ∏ v ∈ S, (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v
              ((T.diagonalBlockLocalEquiv hT hδ v).symm ⁻¹' (K v ×ˢ K v))) *
          ((cInf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) := by ring
    _ = _ := by rw [hPc, Hprod, mul_one]

end Assembly

end RationalQuadraticSpaceMatrix
