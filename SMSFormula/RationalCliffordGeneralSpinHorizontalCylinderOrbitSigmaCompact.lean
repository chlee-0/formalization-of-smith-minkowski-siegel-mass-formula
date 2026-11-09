import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitIntegralCompletion

/-!
# Orbit measurability from σ-compactness, and the full real special orthogonal group

A σ-compact subset of a Hausdorff space is measurable, and continuous images of σ-compact sets
are σ-compact.  The central-cutoff subgroup `K = e⁻¹({ν² = 1, toSO ∈ S_ℝ} × K_f)` is σ-compact
when `S_ℝ` is closed and `K_f` is σ-compact: its real part is closed in the σ-compact real `GSpin`
group.  Hence the orbit `K • x_old` is measurable and the orbit-measurability hypothesis of the
bad-place orbit identity is discharged.  Taking `S_ℝ` to be the whole real `SO` group, the real
measurability hypotheses are trivial as well.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance cylSigARestrictedDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylSigARestrictedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cylSigARestrictedGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance cylSigARestrictedGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance cylSigARestrictedIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cylSigARestrictedIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance cylSigARestrictedExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylSigARestrictedExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance cylSigARestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylSigARestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance cylSigAAmbientFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance cylSigAAmbientFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance cylSigAAmbientBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance cylSigBInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance cylSigBFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance cylSigBT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance cylSigBSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance cylSigBSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance cylSigBSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylSigBSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylSigBStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance cylSigBQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance cylSigBQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylSigBQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylSigBQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance cylSigBQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance cylSigBTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance cylSigBTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance cylSigBLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylSigBLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylSigBFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylSigBFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylSigBUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance cylSigBUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance cylSigBSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance cylSigBSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- σ-compact subsets of a Hausdorff Borel space are measurable. -/
theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun k ↦ (hK k).isClosed.measurableSet

/-- Products of σ-compact sets are σ-compact. -/
theorem isSigmaCompact_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) :
    IsSigmaCompact (s ×ˢ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  obtain ⟨L, hL, rfl⟩ := ht
  rw [Set.iUnion_prod_const]
  simp_rw [Set.prod_iUnion]
  exact isSigmaCompact_iUnion _ fun k ↦ isSigmaCompact_iUnion _ fun l ↦
    ((hK k).prod (hL l)).isSigmaCompact

/-- The real sign subgroup is closed. -/
theorem isClosed_realSignUnitsSubgroup : IsClosed (realSignUnitsSubgroup : Set ℝˣ) := by
  have h : (realSignUnitsSubgroup : Set ℝˣ) = (fun t : ℝˣ ↦ t ^ 2) ⁻¹' {1} := by
    ext t
    exact mem_realSignUnitsSubgroup_iff t
  rw [h]
  exact isClosed_singleton.preimage (continuous_pow 2)

/-- The central-cutoff subgroup is σ-compact for a closed real `SO` subgroup and a σ-compact
finite part. -/
theorem isSigmaCompact_centralCutoffSubgroup (V : RationalQuadraticSpaceMatrix n)
    (SR : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
    (hSR : IsClosed (SR : Set (V.specialOrthogonalMatrixGroup ℝ)))
    (Kf : Subgroup V.FiniteAdelicCliffordGeneralSpinGroup)
    (hKf : IsSigmaCompact (Kf : Set V.FiniteAdelicCliffordGeneralSpinGroup)) :
    IsSigmaCompact (V.centralCutoffSubgroup SR Kf : Set V.FullAdelicCliffordGeneralSpinGroup) := by
  have hA : IsClosed (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹'
      ((realSignUnitsSubgroup : Set ℝˣ) ×ˢ (SR : Set _))) :=
    (isClosed_realSignUnitsSubgroup.prod hSR).preimage V.continuous_centralFiberGroupHom_real
  have hAs : IsSigmaCompact (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹'
      ((realSignUnitsSubgroup : Set ℝˣ) ×ˢ (SR : Set _))) :=
    isSigmaCompact_univ.of_isClosed_subset hA (Set.subset_univ _)
  have hset : (V.centralCutoffSubgroup SR Kf : Set V.FullAdelicCliffordGeneralSpinGroup) =
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm ''
        ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹'
          ((realSignUnitsSubgroup : Set ℝˣ) ×ˢ (SR : Set _))) ×ˢ (Kf : Set _)) := by
    ext g
    rw [SetLike.mem_coe, mem_centralCutoffSubgroup_iff]
    constructor
    · intro hg
      refine ⟨V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g, ?_,
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm_apply_apply g⟩
      simp only [Set.mem_preimage, Set.mem_prod, SetLike.mem_coe]
      exact ⟨⟨hg.1, hg.2.1⟩, hg.2.2⟩
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod, SetLike.mem_coe] at hy
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact ⟨hy.1.1, hy.1.2, hy.2⟩
  rw [hset]
  exact (isSigmaCompact_prod hAs hKf).image
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.continuous

/-- The orbit of A σ-compact central-cutoff subgroup is measurable. -/
theorem measurableSet_orbit_centralCutoffSubgroup (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (SR : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))
    (hSR : IsClosed (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)))
    (Kf : Subgroup (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)
    (hKf : IsSigmaCompact (Kf : Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)) :
    MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup SR Kf : Set _)) :=
  measurableSet_of_isSigmaCompact
    (((W.nonisotropicLastExtension a ha).isSigmaCompact_centralCutoffSubgroup SR hSR Kf hKf).image
      (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha))

/-- The bad-place orbit identity with the full real `SO` group: all real and orbit measurability
hypotheses are discharged, given a σ-compact finite cylinder:

`N(K • x_old) · μ_{SO_W}(SO_W(ℝ)) · ∏_{v ∈ B} s_W(v) Haar_{W,v}(ι_v⁻¹ t_v)
  = μ_{SO_V}(SO_V(ℝ)) · ∏_{v ∈ B} s_V(v) Haar_{V,v}(t_v)`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_top
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (ht : ∀ v, MeasurableSet
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (htW : ∀ v, MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))
    (hKf : IsSigmaCompact (((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup
      S (W.integralCompletedLocalSubgroups a ha S t)) :
        Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S t)) : Set _)) *
      (W.realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                  v.1)))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1)) := by
  have hOm := W.measurableSet_orbit_centralCutoffSubgroup a ha ⊤
    (by rw [Subgroup.coe_top]; exact isClosed_univ) _ hKf
  have h := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces a ha hT hneg hT0 hTtop
    ⊤ (by rw [Subgroup.coe_top]; exact MeasurableSet.univ)
    (by rw [Subgroup.coe_top, Set.preimage_univ]; exact MeasurableSet.univ) hSB t ht htW hOm
  rwa [Subgroup.coe_top, Set.preimage_univ] at h

/-- The source cylinder over compact local sets is compact: a continuous image of a finite
product of compact sets times the compact integral tail. -/
theorem isCompact_cliffordGeneralSpinHorizontalSourceCylinder (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hs : ∀ v, IsCompact (s v)) :
    IsCompact (V.cliffordGeneralSpinHorizontalSourceCylinder S s) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      CompactSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    isCompact_iff_compactSpace.mp (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
  letI : CompactSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) := by infer_instance
  unfold cliffordGeneralSpinHorizontalSourceCylinder
  have h1 : IsCompact (Set.pi Set.univ s ×ˢ (Set.univ : Set (V.CliffordGeneralSpinHorizontalIntegralTail S))) :=
    (isCompact_univ_pi hs).prod isCompact_univ
  have h2 := h1.image (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).continuous
  have h3 : IsCompact ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S) ⁻¹'
      ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S) ''
        (Set.pi Set.univ s ×ˢ Set.univ))) :=
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).isCompact_preimage.2 h2
  exact h3.image (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)

/-- The integral-completed cylinder is compact when the supplied bad-place subgroups are. -/
theorem isCompact_integralCompletedCylinder (W : RationalQuadraticSpaceMatrix n) (a : ℚ)
    (ha : a ≠ 0) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (ht : ∀ v, IsCompact
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) :
    IsCompact (((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
      (W.integralCompletedLocalSubgroups a ha S t)) :
        Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup) := by
  refine (W.nonisotropicLastExtension a ha).isCompact_cliffordGeneralSpinHorizontalSourceCylinder S _
    fun v ↦ ?_
  unfold integralCompletedLocalSubgroups
  by_cases h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha
  · rw [dif_pos h]; exact ht ⟨v.1, h⟩
  · rw [dif_neg h]
    exact (W.nonisotropicLastExtension a ha).isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup
      ∅ _

/-- The full-`SO` bad-place orbit identity for compact supplied bad-place subgroups: every
hypothesis other than the cutoff and the local measurability is discharged. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_top_of_isCompact
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (ht : ∀ v, MeasurableSet
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (htW : ∀ v, MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))
    (htc : ∀ v, IsCompact
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S t)) : Set _)) *
      (W.realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                  v.1)))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1)) := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_top a ha hT hneg hT0 hTtop hSB
    t ht htW (W.isCompact_integralCompletedCylinder a ha S t htc).isSigmaCompact

end RationalQuadraticSpaceMatrix

end
