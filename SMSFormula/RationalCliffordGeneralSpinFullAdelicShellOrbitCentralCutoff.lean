import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitVolume
import SMSFormula.RationalCliffordGeneralSpinHorizontalRealCentralFactor

/-!
# The real central cutoff cancels in the relative orbit identity

The block embedding `ι` preserves similitude and sends the special-orthogonal image to the
fixed-last-coordinate block embedding `e`.  Hence the pullback of a central cutoff
`A_∞ = {ν ∈ T, toSO ∈ S}` of the block form is the central cutoff `{ν ∈ T, toSO ∈ e⁻¹ S}` of the
lower form.  The real central factor `μ_GSpin(ν ∈ T, toSO ∈ S) = Haar(T) · μ_SO(S)` applies
to both forms with the same `T`, and for `0 < Haar(T) < ∞` the relative orbit identity becomes

```text
N(K • x_old) · μ_{SO_W}(e⁻¹ S) · μ_{W,f}(ι_f⁻¹ A_f) = μ_{SO_V}(S) · μ_{V,f}(A_f).
```

The cutoff `T`, the sets `S`, `A_f` and the subgroup `K` are supplied; no section is chosen.
Negative scope: the left-stability and orbit hypotheses are not discharged here.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000

local instance orbitCentralCutoffInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance orbitCentralCutoffFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance orbitCentralCutoffT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance orbitCentralCutoffSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance orbitCentralCutoffSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance orbitCentralCutoffSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralCutoffSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralCutoffStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance orbitCentralCutoffQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance orbitCentralCutoffQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance orbitCentralCutoffQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance orbitCentralCutoffQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance orbitCentralCutoffQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance orbitCentralCutoffTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance orbitCentralCutoffTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance orbitCentralCutoffLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralCutoffLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralCutoffFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralCutoffFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance orbitCentralUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance orbitCentralSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance orbitCentralSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The real central fiber map `(ν, toSO)` is continuous (identity chart). -/
theorem continuous_centralFiberGroupHom_real (V : RationalQuadraticSpaceMatrix n) :
    Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) := by
  have hfe := V.realCliffordGeneralSpinCentralFiberIdentityChart_coe
  have hone := V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source
  refine continuous_of_continuousAt_one
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) ?_
  have h := V.realCliffordGeneralSpinCentralFiberIdentityChart.continuousAt hone
  rwa [← hfe] at h

/-- The pullback of a block central cutoff through the block embedding is the lower central
cutoff over the pulled-back special-orthogonal set. -/
theorem preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (T : Set ℝˣ)
    (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ ⁻¹'
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
          ℝ ⁻¹' (T ×ˢ S)) =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom W ℝ ⁻¹'
        (T ×ˢ (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹' S)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_apply,
    nonisotropicLastComplementGeneralSpinPoint_similitude,
    nonisotropicLastComplementGeneralSpinPoint_matrixGroup]

/-- The central cutoff cancels: with a supplied `-1`-stable measurable `T` of finite positive
Haar mass, the relative orbit identity on the rectangle `{ν ∈ T, toSO ∈ S} × A_f` holds with the
two special-orthogonal real volumes in place of the real `GSpin` volumes. -/
theorem fullAdelicNonisotropicLastShellMeasure_orbit_mul_centralCutoff_of_leftStable
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (K : Subgroup (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)}
    (hS : MeasurableSet S)
    (hSW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹' S))
    {Afin : Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup}
    (hAfin : MeasurableSet Afin)
    (hWfin : MeasurableSet
      (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin))
    (hKA : ∀ k ∈ K, ∀ g, k * g ∈
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
            ℝ ⁻¹' (T ×ˢ S)) ×ˢ Afin) ↔
      g ∈ (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
            ℝ ⁻¹' (T ×ˢ S)) ×ˢ Afin))
    (hAO : ∀ g ∈ (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
          ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
            ℝ ⁻¹' (T ×ˢ S)) ×ˢ Afin),
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g ∈
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) '' (K : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          (K : Set _)) *
      (W.realInvariantDifferentialGroupMeasure
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹' S) *
        W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin)) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure S *
        (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          Afin := by
  have hcV : Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
      (W.nonisotropicLastExtension a ha) ℝ) :=
    (W.nonisotropicLastExtension a ha).continuous_centralFiberGroupHom_real
  have hcW : Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom W ℝ) :=
    W.continuous_centralFiberGroupHom_real
  have hAreal : MeasurableSet (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
      (W.nonisotropicLastExtension a ha) ℝ ⁻¹' (T ×ˢ S)) := hcV.measurable (hT.prod hS)
  have hWreal : MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha ℝ ⁻¹'
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
        ℝ ⁻¹' (T ×ˢ S))) := by
    rw [preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint]
    exact hcW.measurable (hT.prod hSW)
  have h := W.fullAdelicNonisotropicLastShellMeasure_orbit_mul_realFinite_of_leftStable a ha K
    hAreal hAfin hWreal hWfin hKA hAO hOm
  rw [preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint,
    W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber T hT hneg _ hSW,
    (W.nonisotropicLastExtension a ha).realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber
      T hT hneg S hS] at h
  have h' : (Measure.haar : Measure ℝˣ) T *
      (W.fullAdelicNonisotropicLastShellMeasure a ha
          ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
            (K : Set _)) *
        (W.realInvariantDifferentialGroupMeasure
            (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹' S) *
          W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
            (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' Afin))) =
      (Measure.haar : Measure ℝˣ) T *
        ((W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure S *
          (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
            Afin) := by
    calc _ = _ := by ac_rfl
      _ = _ := h
      _ = _ := by ac_rfl
  exact (ENNReal.mul_right_inj hT0 hTtop).1 h'

end RationalQuadraticSpaceMatrix

end
