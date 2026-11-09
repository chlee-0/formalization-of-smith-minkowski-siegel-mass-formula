import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierTransport
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaarRegularity

/-!
# Regularity of the finite-adelic presentation overlap carrier

The genuine ambient overlap cylinder is open and contains the identity-source
cylinder point.  Hence the fixed finite-adelic Haar has a compact subset of
this carrier with positive finite mass.  This is the cancellation witness for
the subsequent coherent-weight comparison.
-/

noncomputable section

open MeasureTheory Topology

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierRegularityDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance overlapCarrierRegularityPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance overlapCarrierRegularityFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance overlapCarrierRegularityFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

theorem one_mem_transportedAmbientPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) ∈
      P.transportedAmbientPadicCentralFiberSourceOverlap p hx := by
  constructor
  · rw [P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff hx p]
    change (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).symm 1 ∈
      ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).source
    rw [map_one]
    exact (P.blockSpace hx)
      |>.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p
  · exact V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p

theorem isOpen_ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S) := by
  unfold ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier
  apply isOpen_set_pi Set.finite_univ
  intro v _
  exact P.isOpen_transportedAmbientPadicCentralFiberSourceOverlap
    (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

theorem isOpen_ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen (P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) := by
  unfold ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier
  exact
    (P.isOpen_ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S).prod
      isOpen_univ

theorem ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier_nonempty
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S).Nonempty := by
  let exceptional : V.CliffordGeneralSpinHorizontalExceptionalProduct S := fun _ ↦ 1
  let tail : V.CliffordGeneralSpinHorizontalIntegralTail S := fun _ ↦ 1
  refine ⟨(exceptional, tail), ?_, Set.mem_univ tail⟩
  intro v _
  exact P.one_mem_transportedAmbientPadicCentralFiberSourceOverlap hx
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

theorem isOpen_ambientFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen (P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S) := by
  let f := V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hf : IsOpenEmbedding f := by
    unfold f cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    exact
      (V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S
        |>.isOpenEmbedding_subtypeVal).comp
        ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm
          |>.isOpenEmbedding.comp
          (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
            |>.isOpenEmbedding))
  unfold ambientFiniteAdelicPresentationOverlapCylinderCarrier
  exact hf.isOpenMap _
    (P.isOpen_ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S)

theorem ambientFiniteAdelicPresentationOverlapCylinderCarrier_nonempty
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S).Nonempty := by
  obtain ⟨g, hg⟩ :=
    P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier_nonempty hx S
  exact ⟨V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S g, g, hg, rfl⟩

/-- A measurable subset of the ambient overlap carrier on which the fixed
Haar has nonzero finite mass. -/
theorem exists_subset_ambientPresentationOverlap_measure_ne_zero_ne_top
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ∃ K : Set V.FiniteAdelicCliffordGeneralSpinGroup,
      MeasurableSet K ∧
      K ⊆ P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S ∧
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure K ≠ 0 ∧
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure K ≠ ⊤ := by
  let A := P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S
  have hA : IsOpen A :=
    P.isOpen_ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S
  obtain ⟨y, hyA⟩ :=
    P.ambientFiniteAdelicPresentationOverlapCylinderCarrier_nonempty hx S
  let μ := V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  letI : IsLocallyFiniteMeasure μ :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isLocallyFinite
  letI : Measure.IsHaarMeasure μ :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  obtain ⟨U, hyU, hUopen, hUfinite⟩ := μ.exists_isOpen_measure_lt_top y
  let K := U ∩ A
  have hKopen : IsOpen K := hUopen.inter hA
  have hKsubA : K ⊆ A := Set.inter_subset_right
  have hKsubU : K ⊆ U := Set.inter_subset_left
  refine ⟨K, hKopen.measurableSet, hKsubA, ?_, ?_⟩
  · exact (hKopen.measure_pos μ ⟨y, hyU, hyA⟩).ne'
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hKsubU) hUfinite)

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
