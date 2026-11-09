import SMSFormula.MeasureMapCommutingSquare
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralFiniteCarrierTransport

/-!
# Finite Spin Haar transport under an arbitrary rational isometry

The exact raw source/carrier square transports the coherently
weighted finite-adelic Spin measures.  The dependent product reindexings are
kept opaque; they are used through their certified pointwise and pushforward
lemmas.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 200000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

local instance generalFiniteHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance generalFiniteHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance generalFiniteHaarGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance generalFiniteHaarGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

attribute [local irreducible]
  spinCandidateRawExceptionalTailToFiniteAdeles
  rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv

/-! ## Support stability -/

/-- A certified arbitrary-isometry support remains certified after enlarging
its finite set of places. -/
theorem IsHorizontalIntegralTailRationalIsometrySupport.mono
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hST : S ⊆ T) :
    IsHorizontalIntegralTailRationalIsometrySupport W Z e T := by
  rcases hS with ⟨hW, hZ, hd, hf, hr⟩
  refine ⟨hW.trans hST, hZ.trans hST, hd.trans hST, ?_, ?_⟩
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

/-- Once the support contains every nontrivial rational p-adic norm, the
finite exceptional tangent modulus is independent of the support. -/
theorem rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_of_supports
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hT : IsHorizontalIntegralTailRationalIsometrySupport W Z e T) :
    (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞) =
      (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e T : ℝ≥0∞) := by
  let d := rationalIsometrySkewAdjointDetScalar W Z e
  let f : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0 := fun v ↦
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] d‖₊⁻¹
  have hd : d ≠ 0 := rationalIsometrySkewAdjointDetScalar_ne_zero W Z e
  have hf_out (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (hv : v ∉ rationalPadicNormSupportPlaces d) : f v = 1 := by
    have hp : Rat.HeightOneSpectrum.primesEquiv v ∉
        Rat.padicNormPrimeSupport d := by
      intro hp
      apply hv
      exact Finset.mem_map.mpr
        ⟨Rat.HeightOneSpectrum.primesEquiv v, hp,
          Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v⟩
    have hnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
      hd (Rat.HeightOneSpectrum.primesEquiv v) hp
    simpa [f] using congrArg Inv.inv hnorm
  have hprodS :
      ∏ v ∈ rationalPadicNormSupportPlaces d, f v = ∏ v ∈ S, f v :=
    Finset.prod_subset hS.2.2.1 (fun v _ hv ↦ hf_out v hv)
  have hprodT :
      ∏ v ∈ rationalPadicNormSupportPlaces d, f v = ∏ v ∈ T, f v :=
    Finset.prod_subset hT.2.2.1 (fun v _ hv ↦ hf_out v hv)
  have hnn :
      rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S =
        rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e T := by
    unfold rationalIsometrySpinCandidateFiniteExceptionalModulus
    rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) f,
      ← Finset.prod_subtype T (fun _ ↦ Iff.rfl) f]
    exact hprodS.symm.trans hprodT
  exact congrArg (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) hnn

/-! ## Coherent supported finite carrier transport -/

/-- Same-matrix raw assembly rewrites the source carrier before arbitrary
isometry transport; no cross-matrix dependent product occurs here. -/
theorem rationalIsometrySpinCandidateCoherentCarrierMap_eq_sourceRawAssembly
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (W.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S) =
      Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (Measure.map (W.spinCandidateRawExceptionalTailToFiniteAdeles hW)
          (W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
            W.spinCandidateRawExceptionalTailSourceMeasure hW)) := by
  exact congrArg
    (fun μ : Measure W.FiniteAdelicCliffordSpinCandidateGroup ↦
      Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele) μ)
    (W.map_spinCandidateCoherentRawExceptionalTailToFiniteAdeles hW).symm

/-- Functoriality rewrites the source-side nested pushforward as one map. -/
theorem map_rationalIsometrySpinCandidate_map_rawAssembly
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (μ : Measure (W.SpinCandidateRawExceptionalProduct S ×
      W.SpinCandidateRawGoodTail S)) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (Measure.map (W.spinCandidateRawExceptionalTailToFiniteAdeles hW) μ) =
      Measure.map
        ((rationalIsometrySpinCandidateContinuousMulEquiv
            W Z e RationalFiniteAdele) ∘
          W.spinCandidateRawExceptionalTailToFiniteAdeles hW)
        μ :=
  Measure.map_map
    (rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e RationalFiniteAdele).measurable
    (W.measurable_spinCandidateRawExceptionalTailToFiniteAdeles hW)

/-- The coherent supported genuine finite-adelic Spin measure transports by
the exact raw correction times the supported p-adic tangent modulus. -/
theorem map_rationalIsometrySpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (W.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S) =
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
          (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S :
            ℝ≥0∞)) •
        Z.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S := by
  let μ := W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
    W.spinCandidateRawExceptionalTailSourceMeasure hW
  let c := e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
    (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞)
  let ν := c •
    (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
      Z.spinCandidateRawExceptionalTailSourceMeasure hZ)
  let T :=
    rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
      W Z e hS hW hZ
  let L :=
    (rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e RationalFiniteAdele) ∘
      W.spinCandidateRawExceptionalTailToFiniteAdeles hW
  let R := Z.spinCandidateRawExceptionalTailToFiniteAdeles hZ
  have hT : Measure.map T μ = ν := by
    exact map_rationalIsometrySpinCandidateCoherentRawExceptionalTailSourceMeasure
      W Z e hS hW hZ
  have hcommon : Measure.map L μ = Measure.map R ν :=
    Measure.map_eq_map_of_map_eq_of_forall T L R μ ν
      T.measurable (Z.measurable_spinCandidateRawExceptionalTailToFiniteAdeles hZ)
      hT
      (fun g =>
        (rationalIsometrySpinCandidateRawExceptionalTailToFiniteAdeles_commutes
          W Z e hS hW hZ g).symm)
  calc
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (W.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S) =
      Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        (Measure.map (W.spinCandidateRawExceptionalTailToFiniteAdeles hW) μ) :=
      rationalIsometrySpinCandidateCoherentCarrierMap_eq_sourceRawAssembly
        W Z e hW
    _ = Measure.map L μ :=
      map_rationalIsometrySpinCandidate_map_rawAssembly W Z e hW μ
    _ = Measure.map R ν := hcommon
    _ = c •
        Z.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          S := by
      change Measure.map (Z.spinCandidateRawExceptionalTailToFiniteAdeles hZ)
          (c • (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
            Z.spinCandidateRawExceptionalTailSourceMeasure hZ)) = _
      rw [Measure.map_smul,
        Z.map_spinCandidateCoherentRawExceptionalTailToFiniteAdeles hZ]
    _ = _ := rfl

/-- The directed finite-adelic Spin Haar measure transports by the same exact
positive finite scalar computed on any common certified support. -/
theorem map_rationalIsometrySpinCandidateCoherentGroupMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele)
        W.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure =
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
          (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S :
            ℝ≥0∞)) •
        Z.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  let E :=
    rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e RationalFiniteAdele
  let μW := fun T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) ↦
    W.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
      T
  let μZ := fun T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) ↦
    Z.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
      T
  let c : ℝ≥0∞ :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
      (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞)
  have hE : Measurable E := E.measurable
  apply Measure.ext
  intro A hA
  have hpre : MeasurableSet (E ⁻¹' A) := hA.preimage hE
  rw [Measure.map_apply hE hA, Measure.smul_apply]
  change W.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure (E ⁻¹' A) =
    c * Z.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure A
  unfold finiteAdelicCliffordSpinCandidateCoherentGroupMeasure
  rw [Measure.directedSup_apply _ _ hpre,
    Measure.directedSup_apply _ _ hA]
  change (⨆ T, μW T (E ⁻¹' A)) = c * ⨆ T, μZ T A
  apply le_antisymm
  · apply iSup_le
    intro U
    let T := U ∪ S
    have hUT : U ⊆ T := Finset.subset_union_left
    have hST : S ⊆ T := Finset.subset_union_right
    have hT : IsHorizontalIntegralTailRationalIsometrySupport W Z e T :=
      IsHorizontalIntegralTailRationalIsometrySupport.mono W Z e hS hST
    have hTW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ T :=
      hW.trans hST
    have hTZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ T :=
      hZ.trans hST
    let cT : ℝ≥0∞ :=
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection T *
        (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e T : ℝ≥0∞)
    have hcT : cT = c := by
      unfold cT c
      rw [e.spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_of_supports
        hT hS]
      rw [rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_of_supports
        W Z e hT hS]
    have hmapT : Measure.map E (μW T) = cT • μZ T := by
      exact
        map_rationalIsometrySpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          W Z e hT hTW hTZ
    calc
      μW U (E ⁻¹' A) ≤ μW T (E ⁻¹' A) :=
        W.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
          hUT (E ⁻¹' A)
      _ = Measure.map E (μW T) A := (Measure.map_apply hE hA).symm
      _ = (cT • μZ T) A := congrArg (fun ν : Measure _ ↦ ν A) hmapT
      _ = c * μZ T A := by
        rw [Measure.smul_apply, hcT]
        rfl
      _ ≤ c * (⨆ R, μZ R A) := by
        gcongr
        exact le_iSup (fun R ↦ μZ R A) T
  · rw [ENNReal.mul_iSup]
    apply iSup_le
    intro U
    let T := U ∪ S
    have hUT : U ⊆ T := Finset.subset_union_left
    have hST : S ⊆ T := Finset.subset_union_right
    have hT : IsHorizontalIntegralTailRationalIsometrySupport W Z e T :=
      IsHorizontalIntegralTailRationalIsometrySupport.mono W Z e hS hST
    have hTW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ T :=
      hW.trans hST
    have hTZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ T :=
      hZ.trans hST
    let cT : ℝ≥0∞ :=
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection T *
        (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e T : ℝ≥0∞)
    have hcT : cT = c := by
      unfold cT c
      rw [e.spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_of_supports
        hT hS]
      rw [rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_of_supports
        W Z e hT hS]
    have hmapT : Measure.map E (μW T) = cT • μZ T := by
      exact
        map_rationalIsometrySpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
          W Z e hT hTW hTZ
    calc
      c * μZ U A ≤ c * μZ T A := by
        have hmeasure : μZ U A ≤ μZ T A :=
          Z.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
            hUT A
        exact mul_le_mul le_rfl hmeasure bot_le bot_le
      _ = (cT • μZ T) A := by
        rw [Measure.smul_apply, hcT]
        rfl
      _ = Measure.map E (μW T) A :=
        congrArg (fun ν : Measure _ ↦ ν A) hmapT.symm
      _ = μW T (E ⁻¹' A) := Measure.map_apply hE hA
      _ ≤ ⨆ R, μW R (E ⁻¹' A) :=
        le_iSup (fun R ↦ μW R (E ⁻¹' A)) T

end RationalQuadraticSpaceMatrix

end
