import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteFactor
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDifferentialScale

/-!
# Retained finite Spin orbital block coefficient

The retained finite-orbit conditions are evaluated inside the genuine
admissible Spin block.  At the normalized exceptional coordinates, the
chart-glued local Haar mass of the identity source is its fixed source
measure.  The integral tail has probability mass one.  Pulling the raw finite
Spin measure through the genuine-block and exceptional/tail homeomorphisms
therefore gives exactly
`finiteScale * finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S`.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedFiniteBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedFiniteBlockFiniteGroupMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup := borel _

local instance retainedFiniteBlockFiniteGroupBorelSpace :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup := ⟨rfl⟩

local instance retainedFiniteBlockGenuineBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The exact product of existing p-adic Spin identity sources inside the
normalized exceptional factor of the admissible block. -/
def retainedSpinExceptionalIdentityCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Set.pi Set.univ fun v =>
    (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional chart-glued product evaluates on the identity carrier as
the total mass of the already fixed product of identity-source measures. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_identityCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S
        (V.retainedSpinExceptionalIdentityCarrier S) =
      (Measure.pi fun v : {v // v ∈
          V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
        V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ := by
  letI (v : {v // v ∈
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}) :
      SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  rw [retainedSpinExceptionalIdentityCarrier,
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_pi]
  rw [Measure.pi_univ]
  apply Finset.prod_congr rfl
  intro v _hv
  exact V.padicCliffordSpinCandidateChartGluedMeasure_identitySource
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

theorem measurableSet_retainedSpinExceptionalIdentityCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (V.retainedSpinExceptionalIdentityCarrier S) := by
  apply MeasurableSet.univ_pi
  intro v
  exact (V.padicCliffordSpinCandidateIdentityChart
    (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_source.measurableSet

/-- The retained normalized block source: exact exceptional Spin identity
sources and the entire integral tail. -/
def retainedSpinExceptionalTailIdentityCylinder
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  V.retainedSpinExceptionalIdentityCarrier S ×ˢ Set.univ

/-- The normalized tail contributes one, leaving precisely the existing
exceptional identity-source product mass. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_identityCylinder
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure S
        (V.retainedSpinExceptionalTailIdentityCylinder S) =
      (Measure.pi fun v : {v // v ∈
          V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
        V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ := by
  rw [retainedSpinExceptionalTailIdentityCylinder,
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure]
  rw [Measure.prod_prod]
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_identityCarrier]
  simp

/-- Pulling the raw finite Spin measure back through the existing genuine
block and exceptional/tail homeomorphisms exposes exactly the raw scale times
the coherent block weight. -/
theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_block_source
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
          S).symm
        (Measure.map
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
          ((V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
            finiteScale).comap
            (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
              S))) =
      ((finiteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S := by
  unfold finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  rw [Measure.comap_smul, Measure.map_smul, Measure.map_smul]
  rw [V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_block_source S]
  rw [smul_smul]
  rfl

/-- On the retained identity cylinder, the recovered raw block has coefficient
exactly `finiteScale * spinBlockWeight(S)`; the remaining factor is the
fixed product of p-adic Spin identity-source measures. -/
theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_block_source_identityCylinder
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
          S).symm
        (Measure.map
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
          ((V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
            finiteScale).comap
            (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
              S)))
        (V.retainedSpinExceptionalTailIdentityCylinder S) =
      ((finiteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S) *
        (Measure.pi fun v : {v // v ∈
            V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
          V.padicCliffordSpinCandidateIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ := by
  rw [V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_block_source]
  rw [Measure.smul_apply]
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_identityCylinder]
  rw [smul_eq_mul]

end RationalQuadraticSpaceMatrix

end
