import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicMeasure
import SMSFormula.RationalCliffordGeneralSpinHorizontalGenuinePrincipalBlockMeasure
import SMSFormula.RationalCliffordGeneralSpinBlockIntrinsicPoint

/-!
# The finite horizontal Haar of a source cylinder

For a supplied exceptional set `S` and supplied measurable local sets `s_v` at the exceptional
places `v ∈ S ∪ bad`, the source cylinder `∏_v s_v × (integral tail)` is carried by the
exceptional/tail and genuine homeomorphisms into the genuine block and then into the finite-adelic
`GSpin` carrier.  Its directed finite horizontal Haar is

```text
μ_f(cylinder) = w(S) · ∏_{v ∈ S ∪ bad} Haar_v(s_v),
```

with `w(S)` the baseline-relative inverse-volume block weight: the normalized integral tail
contributes exactly one.  This is the first evaluation of the finite horizontal measure on a
concrete set.  Negative scope: no local Haar volume is evaluated here.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance finiteCylinderRestrictedDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteCylinderRestrictedPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteCylinderRestrictedGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance finiteCylinderRestrictedGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance finiteCylinderRestrictedIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteCylinderRestrictedIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance finiteCylinderRestrictedExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteCylinderRestrictedExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteCylinderRestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteCylinderRestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance finiteCylinderAmbientFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance finiteCylinderAmbientFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance finiteCylinderAmbientBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The source cylinder `∏_v s_v × (integral tail)` in the finite-adelic `GSpin` carrier. -/
def cliffordGeneralSpinHorizontalSourceCylinder (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    Set V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S ''
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S ⁻¹'
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S ''
        (Set.pi Set.univ s ×ˢ Set.univ)))

/-- The finite horizontal Haar of a source cylinder:
`μ_f(∏_v s_v × tail) = w(S) · ∏_{v ∈ S ∪ bad} Haar_v(s_v)`. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_sourceCylinder
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
        (V.cliffordGeneralSpinHorizontalSourceCylinder S s) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S *
        ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
          V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1 (s v) := by
  let iS := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  let g := V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let h := V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
  have hiS : MeasurableEmbedding iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding S
  letI : SigmaFinite (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite S
  letI : IsProbabilityMeasure (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability S
  unfold cliffordGeneralSpinHorizontalSourceCylinder
  rw [← hiS.comap_apply, V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_comap_genuineBlock,
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_eq_comap]
  rw [g.measurableEmbedding.comap_apply]
  change (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S)
      (g '' (g ⁻¹' (h '' (Set.pi Set.univ s ×ˢ Set.univ)))) = _
  rw [Set.image_preimage_eq _ g.surjective, cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure,
    Measure.smul_apply, smul_eq_mul, cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure]
  rw [h.measurableEmbedding.map_apply, Set.preimage_image_eq _ h.injective, cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure,
    Measure.prod_prod, measure_univ, mul_one,
    cliffordGeneralSpinHorizontalExceptionalProductMeasure_pi]

/-- Membership in the source cylinder is local: a finite-adelic point lies in it exactly when
its local components are integral outside `S ∪ bad` and lie in `s_v` at every exceptional
place. -/
theorem mem_cliffordGeneralSpinHorizontalSourceCylinder_iff (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1))
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    x ∈ V.cliffordGeneralSpinHorizontalSourceCylinder S s ↔
      V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x) ∧
        ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x).1 v.1 ∈ s v := by
  let g := V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let h := V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
  unfold cliffordGeneralSpinHorizontalSourceCylinder
  constructor
  · rintro ⟨y, ⟨q, hq, hqy⟩, rfl⟩
    refine ⟨y.2, fun v ↦ ?_⟩
    have hval : (g y).1.1 v.1 = (h q).1.1 v.1 := by rw [hqy]
    have hq1 : (h q).1.1 v.1 = q.1 ⟨v.1, v.2⟩ :=
      V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem S q v.1 v.2
    change (g y).1.1 v.1 ∈ s v
    rw [hval, hq1]
    exact hq.1 v (Set.mem_univ _)
  · rintro ⟨hprinc, hloc⟩
    refine ⟨⟨x, hprinc⟩, ⟨h.symm (g ⟨x, hprinc⟩), ⟨fun v _ ↦ ?_, Set.mem_univ _⟩,
      h.apply_symm_apply _⟩, rfl⟩
    have hq1 := V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem S
      (h.symm (g ⟨x, hprinc⟩)) v.1 v.2
    have happ : (h (h.symm (g ⟨x, hprinc⟩))).1.1 v.1 = (g ⟨x, hprinc⟩).1.1 v.1 := by
      rw [h.apply_symm_apply]
    change (h (h.symm (g ⟨x, hprinc⟩))).1.1 v.1 = _ at hq1
    rw [← hq1, happ]
    exact hloc v

/-- Naturality of local components: the block embedding commutes with local evaluation. -/
theorem finiteAdelicRestrictedFamilyMap_nonisotropicLastComplementGeneralSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (x : W.FiniteAdelicCliffordGeneralSpinGroup) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ((W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
        (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele x)).1 v =
      W.nonisotropicLastComplementGeneralSpinPoint a ha _
        ((W.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap x).1 v) :=
  W.nonisotropicLastComplementGeneralSpinPoint_naturality a ha _ x

/-- The pullback of a source cylinder, given a supplied local integrality compatibility of the
block embedding off the exceptional places and equal exceptional sets: the block
embedding pulls the `V`-cylinder over `(s_v)` back to the `W`-cylinder over `(ι_v⁻¹ s_v)`. -/
theorem preimage_nonisotropicLastComplementGeneralSpinPoint_sourceCylinder
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hE : S ∪ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces =
      S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hint : ∀ v, v ∉ S ∪ W.cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ∀ y : W.HeightOnePadicCliffordGeneralSpinGroup v,
        (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
            (Rat.HeightOneSpectrum.primesEquiv v).1
            (W.nonisotropicLastComplementGeneralSpinPoint a ha _ y) ↔
          W.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v).1 y)
    (s : ∀ v : {v // v ∈ S ∪
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹'
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalSourceCylinder S s =
      W.cliffordGeneralSpinHorizontalSourceCylinder S
        (fun v ↦ W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
          s ⟨v.1, by rw [hE]; exact v.2⟩) := by
  ext x
  rw [Set.mem_preimage, mem_cliffordGeneralSpinHorizontalSourceCylinder_iff,
    mem_cliffordGeneralSpinHorizontalSourceCylinder_iff]
  unfold IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily
  simp only [finiteAdelicRestrictedFamilyMap_nonisotropicLastComplementGeneralSpinPoint,
    Set.mem_preimage]
  constructor
  · rintro ⟨hp, hl⟩
    exact ⟨fun v hv ↦ (hint v hv _).1 (hp v (by rw [hE]; exact hv)),
      fun v ↦ hl ⟨v.1, by rw [hE]; exact v.2⟩⟩
  · rintro ⟨hp, hl⟩
    refine ⟨fun v hv ↦ (hint v (by rw [← hE]; exact hv) _).2 (hp v (by rw [← hE]; exact hv)),
      fun v ↦ ?_⟩
    exact hl ⟨v.1, by rw [← hE]; exact v.2⟩

end RationalQuadraticSpaceMatrix

end
