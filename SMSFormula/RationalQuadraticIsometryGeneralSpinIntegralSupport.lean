import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteExceptionalOverlapMeasure
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaar

/-!
# Finite integral support for rational GSpin presentation transport

The horizontal finite-adelic measure is assembled from finite exceptional
coordinates and a normalized product of integral local factors.  This file
isolates the finite support needed to compare those integral tails across a
supplied rational quadratic presentation.

No new local chart is selected.  The support is obtained from compactness of
the already fixed integral tails and the cofinal family of existing genuine
horizontal principal blocks.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance presentationIntegralSupportDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance presentationIntegralSupportPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Every compact subset of finite-adelic intrinsic `GSpin` lies in one of
the existing genuine horizontal principal blocks. -/
theorem isCompact_subset_cliffordGeneralSpinHorizontalGenuinePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    {K : Set V.FiniteAdelicCliffordGeneralSpinGroup}
    (hK : IsCompact K) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      K ⊆ {g |
        V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap g)} := by
  let U := fun S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) =>
    {g : V.FiniteAdelicCliffordGeneralSpinGroup |
      V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap g)}
  have hUopen : ∀ S, IsOpen (U S) := fun S =>
    V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S
  have hcover : K ⊆ ⋃ S, U S := by
    intro g hg
    obtain ⟨S, hS⟩ :=
      V.exists_mem_cliffordGeneralSpinHorizontalGenuinePrincipalBlock g
    exact Set.mem_iUnion.2 ⟨S, hS⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hUopen hcover
  let S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) := T.biUnion id
  refine ⟨S, ?_⟩
  intro g hg
  have hgT := hT hg
  rw [Set.mem_iUnion] at hgT
  obtain ⟨R, hgT⟩ := hgT
  rw [Set.mem_iUnion] at hgT
  obtain ⟨hRT, hgR⟩ := hgT
  intro v hvS
  exact hgR v fun hvR => by
    have hvR' : v ∈ R ∨
        v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces :=
      Finset.mem_union.mp hvR
    apply hvS
    apply Finset.mem_union.mpr
    exact hvR'.elim
      (fun hvR => Or.inl (Finset.mem_biUnion.2 ⟨R, hRT, hvR⟩))
      Or.inr

/-- Embed the already fixed normalized integral tail into the intrinsic
finite-adelic group by putting the identity in every exceptional coordinate.
-/
def cliffordGeneralSpinHorizontalIntegralTailAmbientMap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalIntegralTail S →
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  fun g ↦
    ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
          S).symm
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S (1, g))).1

theorem continuous_cliffordGeneralSpinHorizontalIntegralTailAmbientMap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap S) := by
  exact continuous_subtype_val.comp
    ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
        S).symm.continuous.comp
      ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S).continuous.comp
        (continuous_const.prodMk continuous_id)))

/-- At every good place, the global integral-tail embedding has the original
local integral point as its exact component. -/
theorem cliffordGeneralSpinHorizontalIntegralTailAmbientMap_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1
        (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap S g) =
      (g v).1 := by
  let h := V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
    ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S (1, g)).1)
  have hv := congrFun h v.1
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
        ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S (1, g)).1)) v.1 = (g v).1
  rw [hv]
  exact
    V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
      S (1, g) v.1 v.2

/-- A continuous map out of a finite-adelic intrinsic `GSpin` group sends the
entire fixed compact integral tail into one target principal block. -/
theorem exists_integralTail_image_mem_cliffordGeneralSpinHorizontalPrincipalBlock
    {r s : ℕ}
    (U : RationalQuadraticSpaceMatrix r)
    (V : RationalQuadraticSpaceMatrix s)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : U.FiniteAdelicCliffordGeneralSpinGroup →
      V.FiniteAdelicCliffordGeneralSpinGroup)
    (hf : Continuous f) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      ∀ g : U.CliffordGeneralSpinHorizontalIntegralTail S,
        V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily T
          (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
            (f (U.cliffordGeneralSpinHorizontalIntegralTailAmbientMap S g))) := by
  letI (v : U.CliffordGeneralSpinHorizontalIntegralPlace S) :
      CompactSpace
        (U.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    isCompact_iff_compactSpace.mp
      (U.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
  letI : CompactSpace (U.CliffordGeneralSpinHorizontalIntegralTail S) := by
    infer_instance
  let F := f ∘ U.cliffordGeneralSpinHorizontalIntegralTailAmbientMap S
  have hF : Continuous F :=
    hf.comp (U.continuous_cliffordGeneralSpinHorizontalIntegralTailAmbientMap S)
  have hK : IsCompact (F '' Set.univ) := isCompact_univ.image hF
  obtain ⟨T, hT⟩ :=
    V.isCompact_subset_cliffordGeneralSpinHorizontalGenuinePrincipalBlock hK
  refine ⟨T, fun g => ?_⟩
  exact hT ⟨g, Set.mem_univ g, rfl⟩

namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Presentation transport over the finite adeles commutes with evaluation
at every height-one place. -/
theorem blockToAmbientFiniteAdelicGeneralSpin_heightOneComponent_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx z) =
      P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
        ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom
          v z) := by
  exact (P.blockToAmbientGeneralSpinIntrinsicPoint_naturality hx
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) z).symm

/-- The inverse finite-adelic presentation map also commutes with evaluation
at every height-one place. -/
theorem ambientToBlockFiniteAdelicGeneralSpin_heightOneComponent_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : V.FiniteAdelicCliffordGeneralSpinGroup) :
    (P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        ((P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm z) =
      P.ambientToBlockGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z) := by
  apply (P.blockToAmbientGeneralSpinMulEquiv
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx).injective
  change P.blockToAmbientGeneralSpinIntrinsicPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
        ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          ((P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm z)) =
    P.blockToAmbientGeneralSpinIntrinsicPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
        (P.ambientToBlockGeneralSpinIntrinsicPoint
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z))
  rw [P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock]
  rw [← P.blockToAmbientFiniteAdelicGeneralSpin_heightOneComponent_commutes]
  simp

/-- A finite set supports presentation transport of both fixed compact
integral tails when it also contains both spaces' fixed bad places and every
place where the rational presentation modulus has nontrivial norm. -/
def IsHorizontalIntegralTailPresentationSupport
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : Prop :=
  (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ S ∧
  V.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ S ∧
  rationalPadicNormSupportPlaces
      (P.blockToAmbientSkewAdjointDetScalar hx) ⊆ S ∧
  (∀ g : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail ∅,
    V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
          ((P.blockSpace hx)
            |>.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ g)))) ∧
  ∀ g : V.CliffordGeneralSpinHorizontalIntegralTail ∅,
    (P.blockSpace hx).IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
        ((P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm
          (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ g)))

/-- A finite support simultaneously controls the forward and reverse images
of the two fixed compact integral tails. -/
theorem exists_horizontalIntegralTailPresentationSupport
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      P.IsHorizontalIntegralTailPresentationSupport hx S := by
  obtain ⟨Sf, hSf⟩ :=
    exists_integralTail_image_mem_cliffordGeneralSpinHorizontalPrincipalBlock
      (P.blockSpace hx) V ∅
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).continuous
  obtain ⟨Sr, hSr⟩ :=
    exists_integralTail_image_mem_cliffordGeneralSpinHorizontalPrincipalBlock
      V (P.blockSpace hx) ∅
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm.continuous
  let S := Sf ∪ Sr ∪
    (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
      V.cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
        rationalPadicNormSupportPlaces
          (P.blockToAmbientSkewAdjointDetScalar hx)
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [S, Finset.mem_union] at hv ⊢
    tauto
  · intro v hv
    simp only [S, Finset.mem_union] at hv ⊢
    tauto
  · intro v hv
    simp only [S, Finset.mem_union] at hv ⊢
    tauto
  · intro g v hv
    exact hSf g v fun hvSf => by
      apply hv
      simp only [S, Finset.mem_union] at hvSf ⊢
      tauto
  · intro g v hv
    exact hSr g v fun hvSr => by
      apply hv
      simp only [S, Finset.mem_union] at hvSr ⊢
      tauto

/-- The fixed finite support obtained from the two existing compact integral
tails.  This selects a finite place set, not a local chart or a group point. -/
def horizontalIntegralTailPresentationSupport
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.choose (P.exists_horizontalIntegralTailPresentationSupport hx)

theorem horizontalIntegralTailPresentationSupport_spec
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.IsHorizontalIntegralTailPresentationSupport hx
      (P.horizontalIntegralTailPresentationSupport hx) :=
  Classical.choose_spec (P.exists_horizontalIntegralTailPresentationSupport hx)

/-- Outside any certified presentation support, the local presentation map
carries the fixed block integral subgroup into the fixed ambient integral
subgroup.  The proof inserts one local point into the already normalized
integral tail and reads back that component after global transport. -/
theorem IsHorizontalIntegralTailPresentationSupport.forward_integral
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace ∅)
    (hv : v.1 ∉ S)
    (g : (P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v.1)
    (hg : (P.blockSpace hx).PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx g) := by
  let z : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail ∅ :=
    Function.update (fun _ => 1) v ⟨g, hg⟩
  have himg := hS.2.2.2.1 z v.1 (by
    intro hvbad
    rcases Finset.mem_union.mp hvbad with hvS | hvbad
    · exact hv hvS
    · exact hv (hS.2.1 hvbad))
  change V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1
        (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
          ((P.blockSpace hx)
            |>.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ z))) at himg
  rw [P.blockToAmbientFiniteAdelicGeneralSpin_heightOneComponent_commutes,
    (P.blockSpace hx)
      |>.cliffordGeneralSpinHorizontalIntegralTailAmbientMap_component] at himg
  simpa [z] using himg

/-- Outside any certified presentation support, the inverse local
presentation map carries the fixed ambient integral subgroup into the fixed
block integral subgroup. -/
theorem IsHorizontalIntegralTailPresentationSupport.reverse_integral
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace ∅)
    (hv : v.1 ∉ S)
    (g : V.HeightOnePadicCliffordGeneralSpinGroup v.1)
    (hg : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g) :
    (P.blockSpace hx).PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (P.ambientToBlockGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx g) := by
  let z : V.CliffordGeneralSpinHorizontalIntegralTail ∅ :=
    Function.update (fun _ => 1) v ⟨g, hg⟩
  have himg := hS.2.2.2.2 z v.1 (by
    intro hvbad
    rcases Finset.mem_union.mp hvbad with hvS | hvbad
    · exact hv hvS
    · exact hv (hS.1 hvbad))
  change (P.blockSpace hx).PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom
        v.1
        ((P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx).symm
          (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ z))) at himg
  rw [P.ambientToBlockFiniteAdelicGeneralSpin_heightOneComponent_commutes,
    V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap_component] at himg
  simpa [z] using himg

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
