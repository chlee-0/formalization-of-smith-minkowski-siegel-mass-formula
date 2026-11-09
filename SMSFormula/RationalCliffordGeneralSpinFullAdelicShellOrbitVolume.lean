import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellMeasurableWeil

/-!
# The native full-adelic shell measure of a compact open orbit

For a supplied measurable subgroup `K` of the full-adelic block `GSpin` group with measurable
orbit, the existing measurable Weil identity, applied to the indicator of `K`, evaluates the
native shell measure `N` of the orbit `O = K • x_old`:

```text
N(O) · vol_H(K ∩ H) = vol_G(K),
```

with `vol_G` the horizontal full-adelic `GSpin` Haar and `vol_H` the raw
complement-stabilizer Haar.  At an orbit point `k • x_old` (`k ∈ K`) the existing fiber kernel
is `k`-translated stabilizer Haar, so the fiber integral is `vol_H(K ∩ H)`; off the orbit it is
zero because right multiplication by the stabilizer does not move the shell point.  The
representative is the supplied point `k ∈ K` of the orbit, not a chosen section.

Negative scope: neither volume is evaluated or factored into local volumes here.  The real
`GSpin` factor contains the noncompact positive central scalars, so the full-adelic group has
no compact open subgroup; a finite identity needs a central cutoff (`...RealCentralFactor`), which
is not supplied here.  Both sides may be infinite for open `K`.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellOrbitVolumeInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellOrbitVolumeFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellOrbitVolumeT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellOrbitVolumeSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellOrbitVolumeSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellOrbitVolumeSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellOrbitVolumeSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellOrbitVolumeStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellOrbitVolumeQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellOrbitVolumeQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellOrbitVolumeQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellOrbitVolumeQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellOrbitVolumeQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellOrbitVolumeTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellOrbitVolumeTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The fiber integral of the indicator of a subgroup `K` over the native shell kernel is the
stabilizer mass of `K ∩ H` on the orbit `K • x_old` and zero off it. -/
theorem lintegral_indicator_fullAdelicNonisotropicLastShellOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hKm : MeasurableSet (K : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup))
    (y : W.nonisotropicLastQuadraticShell a ha RationalAdele) :
    ∫⁻ g, (K : Set _).indicator 1 g ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha y =
      ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)).indicator
        (fun _ ↦ ∫⁻ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
          (K : Set _).indicator 1 h.1
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) y := by
  have hf : Measurable ((K : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup).indicator
      (1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)) :=
    measurable_one.indicator hKm
  by_cases hy : y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _)
  · rw [Set.indicator_of_mem hy]
    obtain ⟨k, hk, rfl⟩ := hy
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha _ hf k]
    refine lintegral_congr fun h ↦ ?_
    by_cases hh : (h.1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) ∈ K
    · rw [Set.indicator_of_mem (show k * h.1 ∈ (K : Set _) from K.mul_mem hk hh),
        Set.indicator_of_mem (show h.1 ∈ (K : Set _) from hh)]
      rfl
    · have hkh : k * h.1 ∉ (K : Set _) := fun hkh ↦ hh (by
        simpa using K.mul_mem (K.inv_mem hk) hkh)
      rw [Set.indicator_of_notMem hkh, Set.indicator_of_notMem (show h.1 ∉ (K : Set _) from hh)]
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨g, rfl⟩ :=
      CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective W a ha y
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha _ hf g]
    refine (lintegral_congr fun h ↦ ?_).trans (lintegral_zero)
    rw [Set.indicator_of_notMem]
    intro hgh
    apply hy
    refine ⟨g * h.1, hgh, ?_⟩
    exact CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
      W a ha g h.1 h.2

/-- The native shell measure of a compact open orbit: for a supplied measurable subgroup `K`
whose orbit `K • x_old` is measurable, `N(K • x_old) · vol_H(K ∩ H) = vol_G(K)`. -/
theorem fullAdelicNonisotropicLastShellMeasure_orbit_mul_stabilizer
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hKm : MeasurableSet (K : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)) *
      (∫⁻ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
          (K : Set _).indicator 1 h.1
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
        (K : Set _) := by
  have hf : Measurable ((K : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup).indicator
      (1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)) :=
    measurable_one.indicator hKm
  have hW := W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_measurable a ha _ hf
  simp_rw [W.lintegral_indicator_fullAdelicNonisotropicLastShellOrbitFiberKernel a ha K hKm] at hW
  rw [lintegral_indicator_const hOm, lintegral_indicator_one hKm] at hW
  rw [mul_comm]
  exact hW

/-- The orbit of a compact subgroup is compact, hence measurable in the Hausdorff shell. -/
theorem measurableSet_fullAdelicNonisotropicLastShellOrbit_of_isCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hK : IsCompact K) :
    MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' K) :=
  (hK.image (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha)).isClosed.measurableSet

/-- Left-stable sets: if a measurable `A ⊆ G` is stable under left multiplication by a
subgroup `K` and every point of `A` maps into the orbit `K • x_old`, then the fiber integral
of `1_A` is `vol_H(A ∩ H)` on that orbit and zero off it. -/
theorem lintegral_indicator_leftStable_fullAdelicNonisotropicLastShellOrbitFiberKernel
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (A : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hAm : MeasurableSet A) (hKA : ∀ k ∈ K, ∀ g, k * g ∈ A ↔ g ∈ A)
    (hAO : ∀ g ∈ A, CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele g ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _))
    (y : W.nonisotropicLastQuadraticShell a ha RationalAdele) :
    ∫⁻ g, A.indicator 1 g ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha y =
      ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)).indicator
        (fun _ ↦ ∫⁻ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
          A.indicator 1 h.1
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) y := by
  have hf : Measurable (A.indicator
      (1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)) :=
    measurable_one.indicator hAm
  by_cases hy : y ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _)
  · rw [Set.indicator_of_mem hy]
    obtain ⟨k, hk, rfl⟩ := hy
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha _ hf k]
    refine lintegral_congr fun h ↦ ?_
    by_cases hh : (h.1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) ∈ A
    · rw [Set.indicator_of_mem ((hKA k hk h.1).2 hh), Set.indicator_of_mem hh]
      rfl
    · rw [Set.indicator_of_notMem (fun h' ↦ hh ((hKA k hk h.1).1 h')),
        Set.indicator_of_notMem hh]
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨g, rfl⟩ :=
      CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective W a ha y
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha _ hf g]
    refine (lintegral_congr fun h ↦ ?_).trans (lintegral_zero)
    rw [Set.indicator_of_notMem]
    intro hgh
    apply hy
    rw [← CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
      W a ha g h.1 h.2]
    exact hAO _ hgh

/-- The Weil orbit identity for left-stable sets:
`N(K • x_old) · vol_H(A ∩ H) = vol_G(A)`.  This is the form needed for a central cutoff
`A = K · Z_T`, where both sides are finite although no compact open subgroup exists. -/
theorem fullAdelicNonisotropicLastShellMeasure_orbit_mul_stabilizer_of_leftStable
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (A : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hAm : MeasurableSet A) (hKA : ∀ k ∈ K, ∀ g, k * g ∈ A ↔ g ∈ A)
    (hAO : ∀ g ∈ A, CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele g ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)) *
      (∫⁻ h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha,
          A.indicator 1 h.1
          ∂W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure A := by
  have hf : Measurable (A.indicator
      (1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)) :=
    measurable_one.indicator hAm
  have hW := W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_measurable a ha _ hf
  simp_rw [W.lintegral_indicator_leftStable_fullAdelicNonisotropicLastShellOrbitFiberKernel
    a ha K A hAm hKA hAO] at hW
  rw [lintegral_indicator_const hOm, lintegral_indicator_one hAm] at hW
  rw [mul_comm]
  exact hW

noncomputable local instance fullAdelicShellOrbitVolumeLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellOrbitVolumeLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- The relative Weil orbit identity between the two horizontal Haars: through the block
embedding `ι : GSpin_W(A) → Stab_V(x_old)`, for a left-`K`-stable measurable `A` mapping into
`K • x_old`,

`N(K • x_old) · μ_W(ι⁻¹ A) = μ_V(A)`,

with `μ_W`, `μ_V` the horizontal full-adelic `GSpin` Haars of the lower and block forms. -/
theorem fullAdelicNonisotropicLastShellMeasure_orbit_mul_lower_of_leftStable
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (A : Set (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (hAm : MeasurableSet A) (hKA : ∀ k ∈ K, ∀ g, k * g ∈ A ↔ g ∈ A)
    (hAO : ∀ g ∈ A, CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele g ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)) *
      W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
        ((fun x ↦ ((W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha RationalAdele x :
          W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
            (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)) ⁻¹' A) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure A := by
  have hι : Continuous (fun x ↦ ((W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha
      RationalAdele x : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
        (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)) :=
    continuous_subtype_val.comp
      (W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha RationalAdele)
  have hpre : MeasurableSet ((fun x ↦ ((W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalAdele x : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
        (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)) ⁻¹' A) :=
    hι.measurable hAm
  have hf : Measurable (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha ↦
      A.indicator (1 : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
        h.1) :=
    (measurable_one.indicator hAm).comp continuous_subtype_val.measurable
  rw [← W.fullAdelicNonisotropicLastShellMeasure_orbit_mul_stabilizer_of_leftStable a ha K A hAm
    hKA hAO hOm, W.lintegral_fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    a ha _ hf, ← lintegral_indicator_one hpre]
  rfl

noncomputable local instance fullAdelicShellOrbitVolumeFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellOrbitVolumeFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- Real--Finite product sets: the horizontal full-adelic `GSpin` Haar of the preimage of a
measurable rectangle under the real--finite equivalence is the real differential Haar of the
real side times the directed finite Haar of the finite side. -/
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_preimage_prod
    (V : RationalQuadraticSpaceMatrix n)
    {Areal : Set V.RealCliffordGeneralSpinGroup} {Afin : Set V.FiniteAdelicCliffordGeneralSpinGroup}
    (hAreal : MeasurableSet Areal) (hAfin : MeasurableSet Afin) :
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹' (Areal ×ˢ Afin)) =
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure Areal *
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure Afin := by
  have h := congrArg (fun μ ↦ μ (Areal ×ˢ Afin))
    V.map_fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_realFinite
  simp only at h
  rw [Measure.map_apply V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toHomeomorph.measurable
    (hAreal.prod hAfin), Measure.prod_prod] at h
  exact h

/-- The block embedding commutes with the real--finite splittings (naturality). -/
theorem fullAdelicRealFinite_nonisotropicLastComplementGeneralSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (x : W.FullAdelicCliffordGeneralSpinGroup) :
    (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele x) =
      (W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ
          (W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).1,
        W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele
          (W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).2) := by
  apply Prod.ext
  · exact W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha _ x
  · exact W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha _ x

/-- The relative orbit identity on real--Finite rectangles: for `A = e_V⁻¹(A_∞ × A_f)`
left-stable under `K` and mapping into `K • x_old`,

`N(K • x_old) · μ_{W,∞}(ι_∞⁻¹ A_∞) · μ_{W,f}(ι_f⁻¹ A_f) = μ_{V,∞}(A_∞) · μ_{V,f}(A_f)`,

with the real differential and directed finite horizontal Haars of both forms. -/
theorem fullAdelicNonisotropicLastShellMeasure_orbit_mul_realFinite_of_leftStable
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    {Areal : Set (W.nonisotropicLastExtension a ha).RealCliffordGeneralSpinGroup}
    {Afin : Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup}
    (hAreal : MeasurableSet Areal) (hAfin : MeasurableSet Afin)
    (hWreal : MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ ⁻¹' Areal))
    (hWfin : MeasurableSet
      (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin))
    (hKA : ∀ k ∈ K, ∀ g, k * g ∈
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          (Areal ×ˢ Afin) ↔
      g ∈ (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          (Areal ×ˢ Afin))
    (hAO : ∀ g ∈ (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          (Areal ×ˢ Afin),
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)) *
      (W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
          (W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ ⁻¹' Areal) *
        W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin)) =
      (W.nonisotropicLastExtension a ha).realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
          Areal *
        (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          Afin := by
  have hAm : MeasurableSet
      ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
        (Areal ×ˢ Afin)) :=
    (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.continuous.measurable
      (hAreal.prod hAfin)
  have hrel := W.fullAdelicNonisotropicLastShellMeasure_orbit_mul_lower_of_leftStable a ha K _ hAm
    hKA hAO hOm
  have hpre : ((fun x ↦ ((W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha
      RationalAdele x : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
        (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)) ⁻¹'
      ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
        (Areal ×ˢ Afin))) =
      W.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
        ((W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ ⁻¹' Areal) ×ˢ
          (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod]
    rw [coe_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv,
      fullAdelicRealFinite_nonisotropicLastComplementGeneralSpinPoint]
  rw [hpre, W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_preimage_prod hWreal hWfin,
    (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_preimage_prod
      hAreal hAfin] at hrel
  exact hrel

end RationalQuadraticSpaceMatrix

end
