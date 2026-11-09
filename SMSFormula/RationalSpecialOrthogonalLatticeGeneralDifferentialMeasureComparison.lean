import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialMeasure
import SMSFormula.SpecialOrthogonalAdelicAmbientDifferentialNormalization

/-!
# Lattice/general full-adelic differential measure comparison

The lattice construction and the carrier-independent construction use
the same rational invariant top differential but different finite
normalizations.  This module identifies the lattice normalization set with the
real full factor times the genuine finite empty principal block.  Its mass for
the general measure is therefore the real differential mass.

Haar uniqueness and cancellation on that positive finite real mass then show
that the lattice measure is the general measure scaled by the finite
stabilizer volume.  The scalar is not replaced by one.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000


variable {n : ℕ}

local instance comparisonRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductRealCarrierMeasurableSpace

local instance comparisonRealUnderlyingMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  V.fullAdelicDifferentialProductRealMeasurableSpace

local instance comparisonRealUnderlyingBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  V.fullAdelicDifferentialProductRealBorelSpace

local instance comparisonRealBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.RealSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductRealCarrierBorelSpace

local instance comparisonFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductFiniteMeasurableSpace

local instance comparisonFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  V.fullAdelicDifferentialProductFiniteBorelSpace

/-- The lattice normalization carrier described through the general
real/finite splitting and the genuine finite empty principal block. -/
def rationalQuadraticSpaceMatrixGeneralFullAdelicNormalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv ⁻¹'
    (Set.univ ×ˢ
      (L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
          Set L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalGroup))

private theorem finite_components_gl_eq
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g)).2.1.1 =
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2.1.1 := by
  apply Units.ext
  change
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g).1.1.1.map
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
      g.1.1.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
  exact congrArg
    (fun M : Matrix (Fin n) (Fin n) RationalAdele =>
      M.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele))
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_apply_matrix g)

private theorem finite_component_mem_stabilizer_iff_emptyBlock
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g)).2 ∈
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ↔
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 ∈
        (L.rationalQuadraticSpaceMatrix
          |>.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅) := by
  rw [L.mem_finiteSpecialOrthogonalLatticeStabilizerSubgroup_iff]
  rw [L.mem_finiteLocalLatticeStabilizerSubgroup_iff_placewise]
  rw [L.rationalQuadraticSpaceMatrix
    |>.mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_iff]
  rw [L.rationalQuadraticSpaceMatrix
    |>.isFiniteAdelicSpecialOrthogonalIntegralOutside_iff]
  have hgl := finite_components_gl_eq L g
  constructor
  · rintro ⟨hmat, hinv⟩ v _
    constructor
    · intro i j
      rw [← hgl]
      exact hmat i j v
    · intro i j
      rw [← hgl]
      exact hinv i j v
  · intro h
    constructor
    · intro i j v
      rw [hgl]
      exact (h v (by simp)).1 i j
    · intro i j v
      rw [hgl]
      exact (h v (by simp)).2 i j

private theorem mem_fullAdelicRealFiniteLatticeStabilizerIdentityCoset_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    g ∈ L.fullAdelicRealFiniteLatticeStabilizerIdentityCoset ↔
      g ∈ L.fullAdelicRealFiniteLatticeStabilizerSubgroup := by
  rw [fullAdelicRealFiniteLatticeStabilizerIdentityCoset]
  rw [L.mem_fullAdelicRealFiniteLatticeStabilizerCoset_iff]
  change
    g ∈ {x : L.ConcreteFullAdelicSpecialOrthogonalGroup |
      (x : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) =
        ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
          L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)} ↔
      g ∈ L.fullAdelicRealFiniteLatticeStabilizerSubgroup
  rw [QuotientGroup.eq_class_eq_leftCoset
    L.fullAdelicRealFiniteLatticeStabilizerSubgroup 1]
  simp

/-- The lattice normalization set equals the general real-full/finite-empty
principal block. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet_eq_general
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
      L.rationalQuadraticSpaceMatrixGeneralFullAdelicNormalizationSet := by
  ext g
  rw [rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet]
  rw [rationalQuadraticSpaceMatrixGeneralFullAdelicNormalizationSet]
  rw [Set.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    apply (finite_component_mem_stabilizer_iff_emptyBlock L _).mp
    rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.apply_symm_apply]
    rw [mem_fullAdelicRealFiniteLatticeStabilizerIdentityCoset_iff] at hh
    change
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1 ∈
          (⊤ : OpenSubgroup L.ConcreteRealSpecialOrthogonalGroup) ∧
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2 ∈
          L.finiteSpecialOrthogonalLatticeOpenSubgroup at hh
    exact hh.2
  · intro hg
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and] at hg
    refine ⟨L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g, ?_, ?_⟩
    · rw [mem_fullAdelicRealFiniteLatticeStabilizerIdentityCoset_iff]
      change
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g)).1 ∈
            (⊤ : OpenSubgroup L.ConcreteRealSpecialOrthogonalGroup) ∧
          (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv g)).2 ∈
            L.finiteSpecialOrthogonalLatticeOpenSubgroup
      exact ⟨by simp,
        (finite_component_mem_stabilizer_iff_emptyBlock L g).mpr hg⟩
    · exact
        L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.symm_apply_apply g

/-- The carrier-independent and lattice real differential measures have the
same total mass. -/
theorem rationalQuadraticSpaceMatrix_realInvariantDifferentialGroupMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.realInvariantDifferentialGroupMeasure Set.univ =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ := by
  rw [L.concreteRealSpecialOrthogonalDifferentialMeasure_univ]
  rfl

/-- The general full-adelic differential measure gives the lattice
normalization set exactly the real differential total mass. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_normalizationSet
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.fullAdelicInvariantDifferentialGroupMeasure
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ := by
  let V := L.rationalQuadraticSpaceMatrix
  let Kf : Set V.FiniteAdelicSpecialOrthogonalGroup :=
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
      Set V.FiniteAdelicSpecialOrthogonalGroup)
  have hKf : MeasurableSet Kf :=
    (V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅).measurableSet
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    V.finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite
  letI : SFinite V.finiteAdelicInvariantDifferentialGroupMeasure := by
    infer_instance
  rw [L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet_eq_general]
  change
    V.fullAdelicInvariantDifferentialGroupMeasure
        (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph ⁻¹'
          (Set.univ ×ˢ Kf)) = _
  calc
    _ = Measure.map
          V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
          V.fullAdelicInvariantDifferentialGroupMeasure
          (Set.univ ×ˢ Kf) :=
      (Measure.map_apply
        V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.measurable
        (MeasurableSet.univ.prod hKf)).symm
    _ = V.realInvariantDifferentialGroupMeasure Set.univ := by
      rw [V.map_fullAdelicInvariantDifferentialGroupMeasure_realFinite]
      calc
        _ = V.realInvariantDifferentialGroupMeasure Set.univ *
              V.finiteAdelicInvariantDifferentialGroupMeasure Kf :=
          @Measure.prod_prod _ _
            V.fullAdelicDifferentialProductRealCarrierMeasurableSpace
            V.fullAdelicDifferentialProductFiniteMeasurableSpace
            V.realInvariantDifferentialGroupMeasure
            V.finiteAdelicInvariantDifferentialGroupMeasure
            (by infer_instance) Set.univ Kf
        _ = _ := by
          rw [V.finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock, mul_one]
    _ = _ :=
      L.rationalQuadraticSpaceMatrix_realInvariantDifferentialGroupMeasure_univ

/-- The lattice full-adelic differential measure differs from the
carrier-independent measure by exactly the finite stabilizer volume. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_eq_stabilizerVolume_smul_general
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        L.rationalQuadraticSpaceMatrix.fullAdelicInvariantDifferentialGroupMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  letI : LocallyCompactSpace V.RealSpecialOrthogonalGroup :=
    specialFormPreservingRealGroup_locallyCompact
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SecondCountableTopology V.RealSpecialOrthogonalGroup :=
    specialFormPreservingRealGroup_secondCountable V.pairingMatrix
  letI : LocallyCompactSpace V.FullAdelicSpecialOrthogonalGroup :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
      |>.locallyCompactSpace_iff.mpr inferInstance
  letI : SecondCountableTopology V.FullAdelicSpecialOrthogonalGroup :=
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.isEmbedding
      |>.secondCountableTopology
  letI : Measure.IsHaarMeasure
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isHaarMeasure hP
  letI : Measure.IsHaarMeasure
      V.fullAdelicInvariantDifferentialGroupMeasure :=
    V.fullAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
  let c := Measure.haarScalarFactor
    (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P)
    V.fullAdelicInvariantDifferentialGroupMeasure
  have hscale :
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P =
        c • V.fullAdelicInvariantDifferentialGroupMeasure := by
    exact Measure.isMulLeftInvariant_eq_smul _ _
  have hmass := congrArg
    (fun μ : Measure V.FullAdelicSpecialOrthogonalGroup =>
      μ L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet)
    hscale
  change
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet =
      (c • V.fullAdelicInvariantDifferentialGroupMeasure)
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    at hmass
  rw [L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_normalizationSet hP]
    at hmass
  change
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P =
      (c : ℝ≥0∞) *
        V.fullAdelicInvariantDifferentialGroupMeasure
          L.rationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationSet
    at hmass
  rw [L.fullAdelicInvariantDifferentialGroupMeasure_normalizationSet] at hmass
  let r := L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ
  let a := L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  have hr0 : r ≠ 0 :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  have hrtop : r ≠ ⊤ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  have hc : (c : ℝ≥0∞) = a := by
    change r * a = (c : ℝ≥0∞) * r at hmass
    calc
      (c : ℝ≥0∞) = c * (r * r⁻¹) := by
        rw [ENNReal.mul_inv_cancel hr0 hrtop, mul_one]
      _ = ((c : ℝ≥0∞) * r) * r⁻¹ := by ac_rfl
      _ = (r * a) * r⁻¹ := by rw [← hmass]
      _ = a * (r * r⁻¹) := by ac_rfl
      _ = a := by rw [ENNReal.mul_inv_cancel hr0 hrtop, mul_one]
  change
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P =
      (c : ℝ≥0∞) • V.fullAdelicInvariantDifferentialGroupMeasure
    at hscale
  rw [hc] at hscale
  exact hscale

end PositiveDefiniteIntegralLattice
