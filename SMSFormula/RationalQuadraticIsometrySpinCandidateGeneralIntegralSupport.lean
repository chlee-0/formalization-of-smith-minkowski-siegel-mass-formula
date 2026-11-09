import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralPadicMeasureTransport
import SMSFormula.RationalQuadraticIsometryGeneralSpinIntegralSupport
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteLocal

/-!
# Integral Spin tails under an arbitrary rational isometry

A finite support is chosen only at the level of places: it contains both
native horizontal bad sets, the support of the canonical rational tangent
modulus, and finite sets controlling the forward and reverse images of the
two already fixed compact integral tails.  Outside any such certified support,
the arbitrary-isometry `GSpin` and Spin equivalences identify the literal
integral loci.  Combining this with the exact local Spin Haar factor gives
the corresponding integral-volume formula, and the factor is one outside the
modulus support.

No complement lattice, vector representative, local chart, or global family
of complement presentations is selected.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance generalIntegralSupportDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance generalIntegralSupportPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Arbitrary-isometry finite-adelic `GSpin` transport commutes exactly with
evaluation at every height-one place. -/
theorem rationalIsometryFiniteAdelicGeneralSpin_heightOneComponent_commutes
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : U.FiniteAdelicCliffordGeneralSpinGroup) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele z) =
      rationalIsometryGeneralSpinIntrinsicPoint U V e
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (U.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z) := by
  exact (rationalIsometryGeneralSpinIntrinsicPoint_naturality U V e
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) z).symm

/-- The inverse finite-adelic arbitrary-isometry map also commutes with every
height-one evaluation. -/
theorem rationalIsometryFiniteAdelicGeneralSpin_heightOneComponent_commutes_symm
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : V.FiniteAdelicCliffordGeneralSpinGroup) :
    U.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        ((rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele).symm z) =
      (rationalIsometryGeneralSpinContinuousMulEquiv U V e
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).symm
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z) := by
  let EF := rationalIsometryGeneralSpinContinuousMulEquiv
    U V e RationalFiniteAdele
  let Ev := rationalIsometryGeneralSpinContinuousMulEquiv U V e
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  apply Ev.injective
  calc
    Ev (U.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (EF.symm z)) =
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (EF (EF.symm z)) :=
      (rationalIsometryFiniteAdelicGeneralSpin_heightOneComponent_commutes
        U V e v (EF.symm z)).symm
    _ = V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z := by
      rw [EF.apply_symm_apply]
    _ = Ev (Ev.symm
        (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z)) := by
      rw [Ev.apply_symm_apply]

/-- A finite support controls both native compact integral tails under an
arbitrary supplied rational isometry and contains the rational tangent-modulus
support. -/
def IsHorizontalIntegralTailRationalIsometrySupport
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : Prop :=
  U.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ S ∧
  V.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ S ∧
  rationalPadicNormSupportPlaces
      (rationalIsometrySkewAdjointDetScalar U V e) ⊆ S ∧
  (∀ g : U.CliffordGeneralSpinHorizontalIntegralTail ∅,
    V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
        (rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele
          (U.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ g)))) ∧
  ∀ g : V.CliffordGeneralSpinHorizontalIntegralTail ∅,
    U.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      (U.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap
        ((rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele).symm
          (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ g)))

/-- There is a finite place support simultaneously controlling the forward
and reverse images of both fixed compact integral tails. -/
theorem exists_horizontalIntegralTailRationalIsometrySupport :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      IsHorizontalIntegralTailRationalIsometrySupport U V e S := by
  obtain ⟨Sf, hSf⟩ :=
    exists_integralTail_image_mem_cliffordGeneralSpinHorizontalPrincipalBlock
      U V ∅
      (rationalIsometryGeneralSpinContinuousMulEquiv
        U V e RationalFiniteAdele)
      (rationalIsometryGeneralSpinContinuousMulEquiv
        U V e RationalFiniteAdele).continuous
  obtain ⟨Sr, hSr⟩ :=
    exists_integralTail_image_mem_cliffordGeneralSpinHorizontalPrincipalBlock
      V U ∅
      (rationalIsometryGeneralSpinContinuousMulEquiv
        U V e RationalFiniteAdele).symm
      (rationalIsometryGeneralSpinContinuousMulEquiv
        U V e RationalFiniteAdele).symm.continuous
  let S := Sf ∪ Sr ∪ U.cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
    V.cliffordGeneralSpinHorizontalIntegralBadPlaces ∪
      rationalPadicNormSupportPlaces
        (rationalIsometrySkewAdjointDetScalar U V e)
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
    exact hSf g v fun hvSf ↦ by
      apply hv
      simp only [S, Finset.mem_union] at hvSf ⊢
      tauto
  · intro g v hv
    exact hSr g v fun hvSr ↦ by
      apply hv
      simp only [S, Finset.mem_union] at hvSr ⊢
      tauto

/-- The fixed finite support supplied by compactness of the two existing
integral tails.  Only a finite set of places is selected. -/
def horizontalIntegralTailRationalIsometrySupport :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.choose (exists_horizontalIntegralTailRationalIsometrySupport U V e)

theorem horizontalIntegralTailRationalIsometrySupport_spec :
    IsHorizontalIntegralTailRationalIsometrySupport U V e
      (horizontalIntegralTailRationalIsometrySupport U V e) :=
  Classical.choose_spec
    (exists_horizontalIntegralTailRationalIsometrySupport U V e)

/-- Outside a certified support, arbitrary-isometry transport maps each
literal source `GSpin` integral point into the target integral locus. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.forward_integral
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport U V e S)
    (v : U.CliffordGeneralSpinHorizontalIntegralPlace ∅)
    (hv : v.1 ∉ S)
    (g : U.HeightOnePadicCliffordGeneralSpinGroup v.1)
    (hg : U.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g) :
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (rationalIsometryGeneralSpinIntrinsicPoint U V e
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] g) := by
  let z : U.CliffordGeneralSpinHorizontalIntegralTail ∅ :=
    Function.update (fun _ ↦ 1) v ⟨g, hg⟩
  have himg := hS.2.2.2.1 z v.1 (by
    intro hvbad
    rcases Finset.mem_union.mp hvbad with hvS | hvbad
    · exact hv hvS
    · exact hv (hS.2.1 hvbad))
  change V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1
        (rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele
          (U.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ z))) at himg
  rw [rationalIsometryFiniteAdelicGeneralSpin_heightOneComponent_commutes,
    U.cliffordGeneralSpinHorizontalIntegralTailAmbientMap_component] at himg
  simpa [z] using himg

/-- Outside a certified support, the inverse arbitrary-isometry map carries
every literal target `GSpin` integral point into the source integral locus. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.reverse_integral
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport U V e S)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace ∅)
    (hv : v.1 ∉ S)
    (g : V.HeightOnePadicCliffordGeneralSpinGroup v.1)
    (hg : V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g) :
    U.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      ((rationalIsometryGeneralSpinContinuousMulEquiv U V e
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).symm g) := by
  let z : V.CliffordGeneralSpinHorizontalIntegralTail ∅ :=
    Function.update (fun _ ↦ 1) v ⟨g, hg⟩
  have himg := hS.2.2.2.2 z v.1 (by
    intro hvbad
    rcases Finset.mem_union.mp hvbad with hvS | hvbad
    · exact hv hvS
    · exact hv (hS.1 hvbad))
  change U.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
      (U.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1
        ((rationalIsometryGeneralSpinContinuousMulEquiv
          U V e RationalFiniteAdele).symm
          (V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap ∅ z))) at himg
  rw [rationalIsometryFiniteAdelicGeneralSpin_heightOneComponent_commutes_symm,
    V.cliffordGeneralSpinHorizontalIntegralTailAmbientMap_component] at himg
  simpa [z] using himg

/-- The inverse Spin equivalence commutes with the inverse intrinsic `GSpin`
equivalence after the faithful embedding. -/
theorem cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateContinuousMulEquiv_symm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (z : V.CliffordSpinCandidateGroup A) :
    U.cliffordSpinCandidateToCliffordGeneralSpinHom A
        ((rationalIsometrySpinCandidateContinuousMulEquiv U V e A).symm z) =
      (rationalIsometryGeneralSpinContinuousMulEquiv U V e A).symm
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A z) := by
  let EG := rationalIsometryGeneralSpinContinuousMulEquiv U V e A
  let ES := rationalIsometrySpinCandidateContinuousMulEquiv U V e A
  apply EG.injective
  calc
    EG (U.cliffordSpinCandidateToCliffordGeneralSpinHom A (ES.symm z)) =
        V.cliffordSpinCandidateToCliffordGeneralSpinHom A
          (ES (ES.symm z)) :=
      (cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
        U V e A (ES.symm z)).symm
    _ = V.cliffordSpinCandidateToCliffordGeneralSpinHom A z := by
      rw [ES.apply_symm_apply]
    _ = EG (EG.symm
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A z)) := by
      rw [EG.apply_symm_apply]

/-- Outside a certified support, the arbitrary-isometry Spin equivalence
maps the literal integral-coordinate locus exactly onto the target locus. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.spinCandidate_integral_iff
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport U V e S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S)
    (z : U.HeightOnePadicCliffordSpinCandidateGroup v) :
    U.HeightOnePadicCliffordSpinCandidateIsIntegral v z ↔
      V.HeightOnePadicCliffordSpinCandidateIsIntegral v
        (rationalIsometrySpinCandidateMulEquiv
          U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z) := by
  let vU : U.CliffordGeneralSpinHorizontalIntegralPlace ∅ :=
    ⟨v, by
      simp only [Finset.empty_union]
      intro hvbad
      exact hv (hS.1 hvbad)⟩
  let vV : V.CliffordGeneralSpinHorizontalIntegralPlace ∅ :=
    ⟨v, by
      simp only [Finset.empty_union]
      intro hvbad
      exact hv (hS.2.1 hvbad)⟩
  constructor
  · intro hz
    have hzG : U.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v).1
        (U.cliffordSpinCandidateToCliffordGeneralSpinHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z) :=
      (U.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
        v z).2 hz
    have htG := hS.forward_integral U V e vU (by simpa [vU] using hv)
      (U.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z) hzG
    change V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v).1
        (rationalIsometryGeneralSpinMulEquiv U V e
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (U.cliffordSpinCandidateToCliffordGeneralSpinHom
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z)) at htG
    have hembed :=
      cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
        U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z
    rw [← hembed] at htG
    exact
      (V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
        v (rationalIsometrySpinCandidateMulEquiv
          U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z)).1 htG
  · intro hz
    let t := rationalIsometrySpinCandidateContinuousMulEquiv
      U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z
    have htG : V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v).1
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] t) :=
      (V.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
        v t).2 hz
    have hsG := hS.reverse_integral U V e vV (by simpa [vV] using hv)
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] t) htG
    have hembed :=
      cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateContinuousMulEquiv_symm
        U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] t
    rw [← hembed] at hsG
    have ht : (rationalIsometrySpinCandidateContinuousMulEquiv
        U V e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).symm t = z := by
      simp [t]
    rw [ht] at hsG
    exact
      (U.padicCliffordGeneralSpinIsIntegral_cliffordSpinCandidateToCliffordGeneralSpinHom_iff
        v z).1 hsG

section SamePositiveRank

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (f : W.quadraticForm.IsometryEquiv Z.quadraticForm)

/-- At a certified good place, arbitrary-isometry Spin transport restricts
to the two principal integral subgroups.  The carrier is indexed by the raw
place, so downstream restricted products do not normalize proof-carrying
good-place subtypes in their local equivalence types. -/
def rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z f S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvS : v ∉ S)
    (hvW : v ∉ W.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
    (hvZ : v ∉ Z.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    W.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v ≃ₜ*
      Z.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v := by
  let E := rationalIsometrySpinCandidateContinuousMulEquiv W Z f
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
  let restrictedEquiv :
      W.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v ≃
        Z.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v := {
    toFun := fun g ↦ ⟨E g.1, by
      intro _
      exact (hS.spinCandidate_integral_iff W Z f v hvS g.1).1 (g.2 hvW)⟩
    invFun := fun g ↦ ⟨E.symm g.1, by
      intro _
      let t := E.symm g.1
      have htarget :
          Z.HeightOnePadicCliffordSpinCandidateIsIntegral v (E t) := by
        rw [show E t = g.1 by exact E.apply_symm_apply g.1]
        exact g.2 hvZ
      exact (hS.spinCandidate_integral_iff W Z f v hvS t).2 htarget⟩
    left_inv := fun g ↦ Subtype.ext (E.symm_apply_apply g.1)
    right_inv := fun g ↦ Subtype.ext (E.apply_symm_apply g.1) }
  exact ContinuousMulEquiv.mk'
    { toEquiv := restrictedEquiv
      continuous_toFun := Continuous.subtype_mk
        (E.continuous.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (E.symm.continuous.comp continuous_subtype_val) _ }
    (fun g h ↦ Subtype.ext (E.map_mul g.1 h.1))

/-- The principal-subgroup equivalence at a certified good place preserves
the independently normalized local Haar probabilities. -/
theorem rationalIsometrySpinCandidateIntegralPrincipalLocal_measurePreserving
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z f S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvS : v ∉ S)
    (hvW : v ∉ W.cliffordSpinCandidateAdmissibleExceptionalPlaces S)
    (hvZ : v ∉ Z.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    let vW : W.CliffordSpinCandidateAdmissibleIntegralPlace S := ⟨v, hvW⟩
    let vZ : Z.CliffordSpinCandidateAdmissibleIntegralPlace S := ⟨v, hvZ⟩
    MeasurePreserving
      (rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
        W Z f hS v hvS hvW hvZ)
      (W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S vW)
      (Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S vZ) := by
  dsimp only
  let vW : W.CliffordSpinCandidateAdmissibleIntegralPlace S := ⟨v, hvW⟩
  let vZ : Z.CliffordSpinCandidateAdmissibleIntegralPlace S := ⟨v, hvZ⟩
  let E := rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
    W Z f hS v hvS hvW hvZ
  let μ :=
    W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S vW
  let ν :=
    Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S vZ
  letI : CompactSpace
      (W.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
    W.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
      S v hvW
  letI : CompactSpace
      (Z.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v) :=
    Z.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
      S v hvZ
  letI : Measure.IsMulLeftInvariant μ := by
    exact
      W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isMulLeftInvariant
        S vW
  letI : Measure.IsMulLeftInvariant ν := by
    exact
      Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isMulLeftInvariant
        S vZ
  letI : IsProbabilityMeasure μ := by
    exact
      W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
        S vW
  letI : IsProbabilityMeasure ν := by
    exact
      Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
        S vZ
  letI : Measure.IsHaarMeasure μ := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior μ Set.univ
    · exact isCompact_univ
    · simp
    · simp
    · simp
  letI : Measure.IsHaarMeasure ν := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior ν Set.univ
    · exact isCompact_univ
    · simp
    · simp
    · simp
  have hmap : Measure.IsHaarMeasure (Measure.map E μ) :=
    E.toMulEquiv.isHaarMeasure_map μ E.continuous E.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map E μ) := hmap
  letI : IsProbabilityMeasure (Measure.map E μ) :=
    Measure.isProbabilityMeasure_map E.measurable.aemeasurable
  refine ⟨E.measurable, ?_⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.map E μ) ν

/-- At every place outside a certified support, the source integral Spin
volume is the reciprocal local modulus times the target volume. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.integralVolume_eq_modulus_mul
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z f S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    W.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (rationalIsometrySkewAdjointDetScalar W Z f)‖₊⁻¹ : NNReal) *
        Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let E := rationalIsometrySpinCandidateContinuousMulEquiv W Z f ℚ_[p]
  let μW := W.padicCliffordSpinCandidateChartGluedMeasure p
  let μZ := Z.padicCliffordSpinCandidateChartGluedMeasure p
  let T : Set (Z.HeightOnePadicCliffordSpinCandidateGroup v) :=
    {g | Z.HeightOnePadicCliffordSpinCandidateIsIntegral v g}
  have hT : MeasurableSet T :=
    (Z.isOpen_heightOnePadicCliffordSpinCandidateIsIntegral v).measurableSet
  have hpre : E ⁻¹' T =
      {g | W.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
    ext g
    exact (hS.spinCandidate_integral_iff W Z f v hv g).symm
  have hmap :=
    map_rationalIsometryPadicCliffordSpinCandidateChartGluedMeasure W Z f p
  have hmass := congrArg
    (fun μ : Measure (Z.HeightOnePadicCliffordSpinCandidateGroup v) ↦ μ T) hmap
  change (Measure.map E μW) T =
      (‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar W Z f)‖₊⁻¹ : NNReal) •
        μZ T at hmass
  have happly := Measure.map_apply (μ := μW) E.measurable hT
  change (Measure.map E μW) T = μW (E ⁻¹' T) at happly
  rw [happly, hpre] at hmass
  change W.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      (‖algebraMap ℚ ℚ_[p]
          (rationalIsometrySkewAdjointDetScalar W Z f)‖₊⁻¹ : NNReal) *
        Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v
  exact hmass

/-- Since the certified support contains the rational tangent-modulus
support, the literal source and target Spin integral volumes agree outside
that support. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.integralVolume_eq
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z f S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    W.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v =
      Z.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v := by
  rw [hS.integralVolume_eq_modulus_mul W Z f v hv]
  let d := rationalIsometrySkewAdjointDetScalar W Z f
  have hp : Rat.HeightOneSpectrum.primesEquiv v ∉
      Rat.padicNormPrimeSupport d := by
    intro hp
    apply hv
    exact hS.2.2.1 (Finset.mem_map.mpr
      ⟨Rat.HeightOneSpectrum.primesEquiv v, hp,
        Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v⟩)
  have hnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
    (rationalIsometrySkewAdjointDetScalar_ne_zero W Z f)
    (Rat.HeightOneSpectrum.primesEquiv v) hp
  rw [hnorm, inv_one]
  simp only [ENNReal.coe_one, one_mul]

end SamePositiveRank

end RationalQuadraticSpaceMatrix

end
