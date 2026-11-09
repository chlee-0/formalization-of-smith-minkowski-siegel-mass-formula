import SMSFormula.RationalCliffordGeneralSpinBlockIntegrality
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitCentralSubgroup

/-!
# The central-cutoff orbit identity on source-cylinder subgroups

For supplied local subgroups `s_v` at the exceptional places, the source cylinder is a
subgroup of the finite-adelic block `GSpin` group (local components are a homomorphism and the
integral elements off the exceptional places form a subgroup), measurable when the `s_v` are.
With equal exceptional sets, its block-embedding pullback is the lower source cylinder over
`ι_v⁻¹ s_v`.  Both finite horizontal Haars are the block weights times the local Haars, so
the discharged central-cutoff orbit identity becomes fully explicit on the finite side:

```text
N(K • x_old) · μ_{SO_W}(e⁻¹ S) · (w_W(S) ∏_v Haar_{W,v}(ι_v⁻¹ s_v))
  = μ_{SO_V}(S) · (w_V(S) ∏_v Haar_{V,v}(s_v)).
```

The subgroups, the cutoff and the orbit measurability are supplied; nothing is chosen.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance cylOrbitARestrictedDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylOrbitARestrictedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cylOrbitARestrictedGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance cylOrbitARestrictedGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance cylOrbitARestrictedIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cylOrbitARestrictedIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance cylOrbitARestrictedExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylOrbitARestrictedExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance cylOrbitARestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylOrbitARestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance cylOrbitAAmbientFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance cylOrbitAAmbientFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance cylOrbitAAmbientBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance cylOrbitBInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance cylOrbitBFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance cylOrbitBT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance cylOrbitBSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance cylOrbitBSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance cylOrbitBSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylOrbitBSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylOrbitBStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance cylOrbitBQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance cylOrbitBQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylOrbitBQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylOrbitBQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance cylOrbitBQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance cylOrbitBTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance cylOrbitBTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance cylOrbitBLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylOrbitBLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylOrbitBFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylOrbitBFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylOrbitBUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance cylOrbitBUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance cylOrbitBSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance cylOrbitBSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The source cylinder over supplied local subgroups, as a subgroup. -/
def cliffordGeneralSpinHorizontalCylinderSubgroup (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    Subgroup V.FiniteAdelicCliffordGeneralSpinGroup where
  carrier := V.cliffordGeneralSpinHorizontalSourceCylinder S (fun v ↦ (s v : Set _))
  one_mem' := by
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
    refine ⟨fun v hv ↦ ?_, fun v ↦ ?_⟩
    · have h := (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S ⟨v, hv⟩).one_mem
      rw [mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff] at h
      change V.PadicCliffordGeneralSpinIsIntegral _
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v 1)
      rwa [map_one]
    · change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 1 ∈ s v
      rw [map_one]
      exact (s v).one_mem
  mul_mem' := by
    intro x y hx hy
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
      at hx
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
      at hy
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
    refine ⟨fun v hv ↦ ?_, fun v ↦ ?_⟩
    · have hxv := hx.1 v hv
      have hyv := hy.1 v hv
      rw [← mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff V S ⟨v, hv⟩] at hxv hyv ⊢
      change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v (x * y) ∈ _
      rw [map_mul]
      exact Subgroup.mul_mem _ hxv hyv
    · change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 (x * y) ∈ s v
      rw [map_mul]
      exact (s v).mul_mem (hx.2 v) (hy.2 v)
  inv_mem' := by
    intro x hx
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
      at hx
    rw [mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
    refine ⟨fun v hv ↦ ?_, fun v ↦ ?_⟩
    · have hxv := hx.1 v hv
      rw [← mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff V S ⟨v, hv⟩] at hxv ⊢
      change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x⁻¹ ∈ _
      rw [map_inv]
      exact Subgroup.inv_mem _ hxv
    · change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1 x⁻¹ ∈ s v
      rw [map_inv]
      exact (s v).inv_mem (hx.2 v)

/-- The source cylinder over measurable local sets is measurable. -/
theorem measurableSet_cliffordGeneralSpinHorizontalSourceCylinder (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hs : ∀ v, MeasurableSet (s v)) :
    MeasurableSet (V.cliffordGeneralSpinHorizontalSourceCylinder S s) := by
  unfold cliffordGeneralSpinHorizontalSourceCylinder
  refine (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding S
    ).measurableSet_image.2 ?_
  refine (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).measurable ?_
  refine (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
    ).measurableEmbedding.measurableSet_image.2 ?_
  exact (MeasurableSet.univ_pi hs).prod MeasurableSet.univ

/-- The central-cutoff orbit identity on a source-cylinder subgroup, finite side explicit:

`N(K • x_old) · μ_{SO_W}(e⁻¹ S_ℝ) · (w_W(S) ∏ Haar_{W,v}(ι_v⁻¹ s_v)) =
  μ_{SO_V}(S_ℝ) · (w_V(S) ∏ Haar_{V,v}(s_v))`

with `K` the central-cutoff subgroup over the real `SO` subgroup `S_ℝ` and the finite cylinder
subgroup over the supplied local subgroups `s_v`, for supplied equal exceptional sets. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (SR : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))
    (hSR : MeasurableSet
      (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)))
    (hSRW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
      (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hE : S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces =
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (s : ∀ v : {v // v ∈ S ∪
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (hs : ∀ v, MeasurableSet
      (s v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (hsW : ∀ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
        (s ⟨v.1, by rw [hE]; exact v.2⟩ :
          Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup SR
          ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
          Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup SR
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S s) :
            Set _)) *
      (W.realInvariantDifferentialGroupMeasure
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
            (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))) *
        (W.cliffordGeneralSpinHorizontalRestrictedBlockWeight S *
          ∏ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (s ⟨v.1, by rw [hE]; exact v.2⟩ :
          Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure
          (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)) *
        ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalRestrictedBlockWeight S *
          ∏ v : {v // v ∈ S ∪
              (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (s v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1))) := by
  have hpre := W.preimage_nonisotropicLastComplementGeneralSpinPoint_sourceCylinder_of_eq a ha S hE
    (fun v ↦ (s v : Set _))
  have hKf := (W.nonisotropicLastExtension a ha).measurableSet_cliffordGeneralSpinHorizontalSourceCylinder
    S (fun v ↦ (s v : Set _)) hs
  have hWfin : MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹'
      ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S s :
        Set _)) := by
    change MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹'
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalSourceCylinder S
        (fun v ↦ (s v : Set _)))
    rw [hpre]
    exact W.measurableSet_cliffordGeneralSpinHorizontalSourceCylinder S _ hsW
  have h := W.fullAdelicNonisotropicLastShellMeasure_centralCutoffSubgroup_orbit a ha hT hneg hT0
    hTtop SR hSR hSRW _ hKf hWfin hOm
  change _ * (_ * W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
      (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹'
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalSourceCylinder S
          (fun v ↦ (s v : Set _)))) =
    _ * (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
      ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalSourceCylinder S
        (fun v ↦ (s v : Set _))) at h
  rw [hpre, finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_sourceCylinder,
    finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_sourceCylinder] at h
  exact h

end RationalQuadraticSpaceMatrix

end
