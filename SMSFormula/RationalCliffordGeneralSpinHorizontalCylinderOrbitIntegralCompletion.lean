import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitNormalized

/-!
# The cylinder orbit identity with integral local subgroups off the bad places

Let `B = bad_V ∪ bad_W` be the union of the horizontal bad places of the two forms and let
the supplied block `S` contain `B`.  At the exceptional places outside `B` take the integral
local subgroups, and at the places of `B` supplied local subgroups `t_v`.  At a place outside `B`
the block embedding pulls the `V` integral subgroup back to the `W` integral subgroup (old
integrality compatibility), and both normalized masses are one.  Hence

```text
N(K • x_old) · μ_{SO_W}(e⁻¹ S_ℝ) · ∏_{v ∈ B} s_W(v) Haar_{W,v}(ι_v⁻¹ t_v)
  = μ_{SO_V}(S_ℝ) · ∏_{v ∈ B} s_V(v) Haar_{V,v}(t_v),
```

independently of the block `S ⊇ B`: only the bad places remain.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance cylIntARestrictedDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylIntARestrictedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cylIntARestrictedGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance cylIntARestrictedGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance cylIntARestrictedIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cylIntARestrictedIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance cylIntARestrictedExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylIntARestrictedExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance cylIntARestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cylIntARestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance cylIntAAmbientFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance cylIntAAmbientFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance cylIntAAmbientBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance cylIntBInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance cylIntBFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance cylIntBT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance cylIntBSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance cylIntBSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance cylIntBSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylIntBSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylIntBStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance cylIntBQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance cylIntBQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylIntBQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance cylIntBQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance cylIntBQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance cylIntBTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance cylIntBTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance cylIntBLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylIntBLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylIntBFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance cylIntBFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance cylIntBUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance cylIntBUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance cylIntBSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance cylIntBSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The integral local subgroup measured by the local Haar is measurable. -/
theorem measurableSet_padicCliffordGeneralSpinHorizontalIntegralSubgroup
    (V : RationalQuadraticSpaceMatrix n) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    MeasurableSet (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v :
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :=
  (V.isOpen_padicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1).measurableSet

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The bad places of the last extension `W ⊕ ⟨a⟩`: the horizontal bad places of the block and
lower forms, together with the odd-unimodular bad places of the block and the prime support of
the norm `a`.  Off this set every place is fully good (odd, unimodular block, `a` a unit); the last two
pieces are essential, since for integral forms the horizontal bad places alone need not contain `2`
or the primes of `a` (see `AdelicGaussianCapstoneBadSetRequirement`). -/
def lastExtensionHorizontalBadPlaces : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
    (W.cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
      ((W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces ∪
        rationalPadicNormSupportPlaces a))

theorem mem_lastExtensionHorizontalBadPlaces_of_block {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (h : v ∈ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    v ∈ W.lastExtensionHorizontalBadPlaces a ha :=
  Finset.mem_union_left _ h

theorem mem_lastExtensionHorizontalBadPlaces_of_lower {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (h : v ∈ W.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    v ∈ W.lastExtensionHorizontalBadPlaces a ha :=
  Finset.mem_union_right _ (Finset.mem_union_left _ h)

theorem mem_lastExtensionHorizontalBadPlaces_of_oddUnimodular
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (h : v ∈ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces) :
    v ∈ W.lastExtensionHorizontalBadPlaces a ha :=
  Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ h))

theorem mem_lastExtensionHorizontalBadPlaces_of_normSupport
    {v : IsDedekindDomain.HeightOneSpectrum ℤ} (h : v ∈ rationalPadicNormSupportPlaces a) :
    v ∈ W.lastExtensionHorizontalBadPlaces a ha :=
  Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ h))

/-- The local subgroups: supplied on the bad places, the integral subgroup elsewhere. -/
def integralCompletedLocalSubgroups (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (v : {v // v ∈ S ∪
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1) :=
  if h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha then t ⟨v.1, h⟩
  else (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalIntegralSubgroup ∅
    ⟨v.1, by
      simp only [Finset.empty_union]
      exact fun hb ↦ h (W.mem_lastExtensionHorizontalBadPlaces_of_block a ha hb)⟩

/-- Off the bad places the block embedding pulls the `V` integral subgroup back to the `W` one. -/
theorem preimage_integralSubgroup_eq {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (hv : v ∉ W.lastExtensionHorizontalBadPlaces a ha) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
        ((W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalIntegralSubgroup ∅
          ⟨v, by simp only [Finset.empty_union]; exact fun hb ↦ hv (W.mem_lastExtensionHorizontalBadPlaces_of_block a ha hb)⟩ :
          Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v)) =
      (W.padicCliffordGeneralSpinHorizontalIntegralSubgroup ∅
          ⟨v, by simp only [Finset.empty_union]; exact fun hb ↦ hv (W.mem_lastExtensionHorizontalBadPlaces_of_lower a ha hb)⟩ :
        Set (W.HeightOnePadicCliffordGeneralSpinGroup v)) := by
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe]
  exact W.padicCliffordGeneralSpinIsIntegral_nonisotropicLastComplementGeneralSpinPoint_iff a ha _ y

/-- The `V`-side normalized product reduces to the bad places. -/
theorem prod_normalized_integralCompletedLocalSubgroups
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    ∏ v : {v // v ∈ S ∪
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
        (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (W.integralCompletedLocalSubgroups a ha S t v :
            Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) =
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
          (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
            (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) := by
  classical
  let g : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞ := fun v ↦
    if h : v ∈ W.lastExtensionHorizontalBadPlaces a ha then
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v *
        (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v
          (t ⟨v, h⟩ : Set _)
    else 1
  have h1 : ∀ v : {v // v ∈ S ∪
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
        (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (W.integralCompletedLocalSubgroups a ha S t v : Set _) = g v.1 := by
    intro v
    unfold integralCompletedLocalSubgroups
    by_cases h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha
    · conv_lhs => rw [dif_pos h]
      conv_rhs => simp only [g]
      rw [dif_pos h]
    · conv_lhs => rw [dif_neg h]
      conv_rhs => simp only [g]
      rw [dif_neg h]
      exact (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale_mul_integralSubgroup
        ∅ ⟨v.1, by
          simp only [Finset.empty_union]
          exact fun hb ↦ h (W.mem_lastExtensionHorizontalBadPlaces_of_block a ha hb)⟩
  have hBsub : W.lastExtensionHorizontalBadPlaces a ha ⊆
      S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces :=
    hSB.trans Finset.subset_union_left
  rw [Finset.prod_congr rfl (fun v _ ↦ h1 v),
    Finset.prod_coe_sort (S ∪
      (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces) g,
    ← Finset.prod_subset hBsub (fun v _ hv ↦ dif_neg hv),
    ← Finset.prod_coe_sort (W.lastExtensionHorizontalBadPlaces a ha) g]
  exact Finset.prod_congr rfl fun v _ ↦ dif_pos v.2

/-- The `W`-side normalized product reduces to the bad places. -/
theorem prod_normalized_preimage_integralCompletedLocalSubgroups
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (hE : S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces =
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    ∏ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
        W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
            (W.integralCompletedLocalSubgroups a ha S t ⟨v.1, by rw [hE]; exact v.2⟩ :
              Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) =
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
          W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
            (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
              (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1))) := by
  classical
  let g : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞ := fun v ↦
    if h : v ∈ W.lastExtensionHorizontalBadPlaces a ha then
      W.cliffordGeneralSpinHorizontalBaselineScale v *
        W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v
          (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹' (t ⟨v, h⟩ : Set _))
    else 1
  have h1 : ∀ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
        W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
            (W.integralCompletedLocalSubgroups a ha S t ⟨v.1, by rw [hE]; exact v.2⟩ : Set _)) =
        g v.1 := by
    intro v
    unfold integralCompletedLocalSubgroups
    by_cases h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha
    · conv_lhs => rw [dif_pos h]
      conv_rhs => simp only [g]
      rw [dif_pos h]
    · conv_lhs => rw [dif_neg h]
      conv_rhs => simp only [g]
      rw [dif_neg h, W.preimage_integralSubgroup_eq a ha h]
      exact W.cliffordGeneralSpinHorizontalBaselineScale_mul_integralSubgroup ∅ ⟨v.1, by
        simp only [Finset.empty_union]
        exact fun hb ↦ h (W.mem_lastExtensionHorizontalBadPlaces_of_lower a ha hb)⟩
  have hBsub : W.lastExtensionHorizontalBadPlaces a ha ⊆
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces :=
    hSB.trans Finset.subset_union_left
  rw [Finset.prod_congr rfl (fun v _ ↦ h1 v),
    Finset.prod_coe_sort (S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces) g,
    ← Finset.prod_subset hBsub (fun v _ hv ↦ dif_neg hv),
    ← Finset.prod_coe_sort (W.lastExtensionHorizontalBadPlaces a ha) g]
  exact Finset.prod_congr rfl fun v _ ↦ dif_pos v.2

/-- A block containing both bad sets has equal exceptional sets for the two forms. -/
theorem exceptional_eq_of_badPlaces_subset {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S) :
    S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces =
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
  rw [Finset.union_eq_left.2 (fun v hv ↦ hSB (W.mem_lastExtensionHorizontalBadPlaces_of_block a ha hv)),
    Finset.union_eq_left.2 (fun v hv ↦ hSB (W.mem_lastExtensionHorizontalBadPlaces_of_lower a ha hv))]

/-- The cylinder orbit identity reduced to the bad places: with the integral local subgroups
at the good exceptional places and supplied local subgroups `t_v` at the bad places,

`N(K • x_old) · μ_{SO_W}(e⁻¹ S_ℝ) · ∏_{v ∈ B} s_W(v) Haar_{W,v}(ι_v⁻¹ t_v)
  = μ_{SO_V}(S_ℝ) · ∏_{v ∈ B} s_V(v) Haar_{V,v}(t_v)`,

for every supplied block `S ⊇ B = bad_V ∪ bad_W`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces [NeZero n]
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (SR : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))
    (hSR : MeasurableSet
      (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)))
    (hSRW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
      (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (ht : ∀ v, MeasurableSet
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (htW : ∀ v, MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup SR
          ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
            (W.integralCompletedLocalSubgroups a ha S t)) : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup SR
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S t)) : Set _)) *
      (W.realInvariantDifferentialGroupMeasure
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
            (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))) *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                  v.1)))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure
          (SR : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)) *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1)) := by
  have hE := W.exceptional_eq_of_badPlaces_subset a ha hSB
  have hs : ∀ v, MeasurableSet (W.integralCompletedLocalSubgroups a ha S t v :
      Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) := by
    intro v
    unfold integralCompletedLocalSubgroups
    by_cases h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha
    · rw [dif_pos h]; exact ht ⟨v.1, h⟩
    · rw [dif_neg h]
      exact (W.nonisotropicLastExtension a ha).measurableSet_padicCliffordGeneralSpinHorizontalIntegralSubgroup
        ∅ _
  have hsW : ∀ v : {v // v ∈ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
        (W.integralCompletedLocalSubgroups a ha S t ⟨v.1, by rw [hE]; exact v.2⟩ :
          Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) := by
    intro v
    unfold integralCompletedLocalSubgroups
    by_cases h : v.1 ∈ W.lastExtensionHorizontalBadPlaces a ha
    · rw [dif_pos h]; exact htW ⟨v.1, h⟩
    · rw [dif_neg h, W.preimage_integralSubgroup_eq a ha h]
      exact W.measurableSet_padicCliffordGeneralSpinHorizontalIntegralSubgroup ∅ _
  have hmain := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_normalized a ha hT hneg hT0
    hTtop SR hSR hSRW S hE (W.integralCompletedLocalSubgroups a ha S t) hs hsW hOm
  rwa [W.prod_normalized_integralCompletedLocalSubgroups a ha hSB t,
    W.prod_normalized_preimage_integralCompletedLocalSubgroups a ha hSB hE t] at hmain

end RationalQuadraticSpaceMatrix

end
