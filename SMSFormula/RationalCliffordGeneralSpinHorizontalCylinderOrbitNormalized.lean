import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitIdentity
import SMSFormula.RationalCliffordGeneralSpinHorizontalBaselineLedger

/-!
# The cylinder orbit identity in baseline-normalized local masses

The block weight `w(S)` is the product of the baseline scales `s(v)` (one on the
horizontal bad places, the inverse integral volume elsewhere) over the exceptional places
`S ∪ bad`, since the extra bad places contribute one.  Hence the cylinder orbit identity is a
product of baseline-normalized local masses `m(v) = s(v) · Haar_v(s_v)`:

```text
N(K • x_old) · μ_{SO_W}(e⁻¹ S_ℝ) · ∏_v s_W(v) Haar_{W,v}(ι_v⁻¹ s_v)
  = μ_{SO_V}(S_ℝ) · ∏_v s_V(v) Haar_{V,v}(s_v),
```

and at every good place whose local subgroup is the integral subgroup the normalized mass is
exactly one.  Only the bad places and the supplied non-integral local subgroups remain.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance cylNormARestrictedDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylNormARestrictedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cylNormARestrictedGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance cylNormARestrictedGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance cylNormARestrictedIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cylNormARestrictedIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance cylNormARestrictedExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylNormARestrictedExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance cylNormARestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylNormARestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance cylNormAAmbientFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance cylNormAAmbientFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance cylNormAAmbientBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance cylNormBInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance cylNormBFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance cylNormBT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance cylNormBSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance cylNormBSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance cylNormBSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylNormBSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylNormBStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance cylNormBQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance cylNormBQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylNormBQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylNormBQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance cylNormBQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance cylNormBTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance cylNormBTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance cylNormBLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylNormBLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylNormBFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylNormBFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylNormBUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance cylNormBUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance cylNormBSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance cylNormBSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The block weight is the product of the baseline scales over the exceptional places. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_exceptional
    (V : RationalQuadraticSpaceMatrix n) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S =
      ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.cliffordGeneralSpinHorizontalBaselineScale v.1 := by
  rw [V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale S,
    Finset.prod_coe_sort (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
      (fun v ↦ V.cliffordGeneralSpinHorizontalBaselineScale v)]
  refine Finset.prod_subset Finset.subset_union_left fun v hv hvS ↦ ?_
  have hbad : v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    rcases Finset.mem_union.1 hv with h | h
    · exact absurd h hvS
    · exact h
  unfold cliffordGeneralSpinHorizontalBaselineScale
  rw [if_pos hbad]

/-- The block weight times the exceptional local masses is the product of normalized masses. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_mul_prod
    (V : RationalQuadraticSpaceMatrix n) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} → ℝ≥0∞) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S * ∏ v, f v =
      ∏ v, V.cliffordGeneralSpinHorizontalBaselineScale v.1 * f v := by
  rw [cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_exceptional, ← Finset.prod_mul_distrib]

/-- At a good place the normalized mass of the integral subgroup is one. -/
theorem cliffordGeneralSpinHorizontalBaselineScale_mul_integralSubgroup
    (V : RationalQuadraticSpaceMatrix n) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.cliffordGeneralSpinHorizontalBaselineScale v.1 *
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v : Set _) = 1 := by
  have hbad : v.1 ∉ V.cliffordGeneralSpinHorizontalIntegralBadPlaces :=
    fun h ↦ v.2 (Finset.mem_union_right S h)
  unfold cliffordGeneralSpinHorizontalBaselineScale
  rw [if_neg hbad]
  change (V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1)⁻¹ *
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 = 1
  exact ENNReal.inv_mul_cancel (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume_lt_top v.1).ne

/-- The cylinder orbit identity in normalized local masses. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_normalized
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
        ∏ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (s ⟨v.1, by rw [hE]; exact v.2⟩ :
                  Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                    v.1)))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure
          (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)) *
        ∏ v : {v // v ∈ S ∪
            (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (s v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1)) := by
  have h := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit a ha hT hneg hT0 hTtop SR hSR
    hSRW S hE s hs hsW hOm
  rwa [cliffordGeneralSpinHorizontalRestrictedBlockWeight_mul_prod,
    cliffordGeneralSpinHorizontalRestrictedBlockWeight_mul_prod] at h

end RationalQuadraticSpaceMatrix

end
