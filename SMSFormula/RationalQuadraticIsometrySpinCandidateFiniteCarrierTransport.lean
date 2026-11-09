import SMSFormula.RationalQuadraticIsometryGeneralSpinTopology
import SMSFormula.RationalCliffordSpinCandidateAdelicGeneralSpinQuotientExactness
import SMSFormula.RationalQuadraticIsometryGeneralSpinRealHaarFactor
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicGroupHaarFactor
import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction
import SMSFormula.RationalQuadraticIsometryGeneralSpinIntegralSupport
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteLocal
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicHaar
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicHaarFactor

/-!
# Finite Spin carrier transport across a rational presentation

The exceptional-product/integral-tail source is assembled through the
existing mixed and genuine finite-adelic Spin carriers.  This module proves
that the assembly commutes with the intrinsic Spin presentation equivalence
and transports the coherent supported finite measure by the exact scalar
already forced on the source.

No new chart, complement lattice, global finite Haar normalization, quotient
measure, or scalar-one comparison is introduced.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

variable {n : ℕ}

local instance finiteSpinCarrierDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteSpinCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteSpinCarrierGroupMeasurableSpace
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteSpinCarrierGroupBorelSpace
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteSpinCarrierLocalFactorSecondCountable
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteSpinCarrierLocalFactorBorelSpace
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteSpinCarrierMixedSecondCountable
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteSpinCarrierMixedBorelSpace
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteSpinCarrierGenuineBorelSpace
    {k : ℕ} (V : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Canonical source assembly -/

/-- Assemble the explicit exceptional/tail source first into the mixed
principal block, then into the genuine block, and finally into the full
finite-adelic Spin carrier. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →
      V.FiniteAdelicCliffordSpinCandidateGroup :=
  fun g ↦
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
      ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S g))

theorem measurable_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
        S) := by
  exact
    (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S).measurable.comp
      ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm.measurable.comp
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S).measurable)

theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles_component_of_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S g) =
      g.1 ⟨v, hv⟩ := by
  change
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
      (((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S g)).1) = _
  rw [← V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom_apply_component]
  change
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
      S)
      ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S g)) v).1 = _
  rw [(V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
    S).apply_symm_apply]
  exact
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv_apply_mem
      S g v hv

theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles_component_of_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S g) =
      (g.2 ⟨v, hv⟩).1 := by
  change
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
      (((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S g)).1) = _
  rw [← V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom_apply_component]
  change
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
      S)
      ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
          S g)) v).1 = _
  rw [(V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
    S).apply_symm_apply]
  exact
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv_apply_notMem
      S g v hv

/-- Pushing the raw exceptional/tail source through the canonical assembly
recovers the supported ambient measure. -/
theorem map_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S) =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
        S := by
  let e :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph S
  let h :=
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S).symm
  let i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom S
  let μ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure S
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  change Measure.map (i ∘ (h ∘ e)) μ =
    Measure.map i (Measure.map h (Measure.map e μ))
  have hi : Measurable i :=
    V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S |>.measurable
  calc
    Measure.map (i ∘ (h ∘ e)) μ =
        Measure.map i (Measure.map (h ∘ e) μ) :=
      (Measure.map_map hi (h.measurable.comp e.measurable)).symm
    _ = Measure.map i (Measure.map h (Measure.map e μ)) := by
      rw [← Measure.map_map h.measurable e.measurable]

/-- The same assembly sends the coherently weighted source to the existing
coherent supported ambient measure. -/
theorem map_finiteAdelicCliffordSpinCandidateCoherentAdmissibleExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
            S) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S := by
  rw [Measure.map_smul,
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles S]
  exact
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_eq_weight_smul
      S).symm

namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- A certified horizontal presentation support remains certified after
enlarging its finite set of places. -/
theorem IsHorizontalIntegralTailPresentationSupport.mono
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (hST : S ⊆ T) :
    P.IsHorizontalIntegralTailPresentationSupport hx T := by
  rcases hS with ⟨hB, hA, hd, hf, hr⟩
  refine ⟨hB.trans hST, hA.trans hST, hd.trans hST, ?_, ?_⟩
  · intro g v hvT
    apply hf g v
    intro hvS
    apply hvT
    rcases Finset.mem_union.mp hvS with hv | hv
    · exact Finset.mem_union_left _ (hST hv)
    · exact Finset.mem_union_right _ hv
  · intro g v hvT
    apply hr g v
    intro hvS
    apply hvT
    rcases Finset.mem_union.mp hvS with hv | hv
    · exact Finset.mem_union_left _ (hST hv)
    · exact Finset.mem_union_right _ hv

/-! ## Placewise presentation formulas -/

/-! ## Exact source/carrier square -/

/-! ## Coherent supported finite measure transport -/

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix

end
