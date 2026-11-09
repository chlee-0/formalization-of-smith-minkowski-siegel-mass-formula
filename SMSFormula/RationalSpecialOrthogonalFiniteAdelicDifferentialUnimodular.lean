import SMSFormula.HaarMeasureUnimodularInversion
import SMSFormula.MeasureInversionTransport
import SMSFormula.PadicCayleySpecialOrthogonalDifferentialUnimodular
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasure

/-!
# Unimodularity of the finite-adelic special-orthogonal differential measure

The corrected p-adic differential measure is inversion invariant at every
place.  This module propagates that exact scale through the integral subgroup
comaps, normalized infinite tail, exceptional finite product, mixed and
genuine block equivalences, ambient subgroup inclusions, and finally the
directed supremum defining the full finite-adelic measure.

Supported ambient block measures are only asserted to be inversion invariant;
they are not right invariant under arbitrary ambient translations.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

local instance finiteAdelicUnimodularPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicUnimodularDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteAdelicUnimodularPadicGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance finiteAdelicUnimodularPadicGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

local instance finiteAdelicUnimodularGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance finiteAdelicUnimodularGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicUnimodularGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance finiteAdelicUnimodularIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicUnimodularIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Subtype.borelSpace _

local instance finiteAdelicUnimodularExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicUnimodularExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteAdelicUnimodularTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicUnimodularTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

local instance finiteAdelicUnimodularLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicUnimodularLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicUnimodularMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicUnimodularMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicUnimodularFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance finiteAdelicUnimodularFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance finiteAdelicUnimodularGenuineMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  borel _

local instance finiteAdelicUnimodularGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S) :=
  ⟨rfl⟩

/-! ## Local and integral factors -/

/-- The placewise p-adic invariant-differential measure exposes the completed
local inversion theorem. -/
theorem padicInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant (V.padicInvariantDifferentialGroupMeasure p) := by
  exact
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_isInvInvariant
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- The height-one local differential measure is inversion invariant. -/
instance heightOnePadicInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsInvInvariant
      (V.heightOnePadicInvariantDifferentialGroupMeasure v) := by
  exact V.padicInvariantDifferentialGroupMeasure_isInvInvariant
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Comapping the local differential measure to the integral subgroup
preserves inversion invariance. -/
instance heightOnePadicSpecialOrthogonalIntegralMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsInvInvariant
      (V.heightOnePadicSpecialOrthogonalIntegralMeasure v) := by
  letI : Measure.IsInvInvariant
      (V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    V.padicInvariantDifferentialGroupMeasure_isInvInvariant
      (Rat.HeightOneSpectrum.primesEquiv v).1
  unfold heightOnePadicSpecialOrthogonalIntegralMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v)
    (V.heightOnePadicSpecialOrthogonalIntegralMeasurableSpace_eq v)
    (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v).measurableSet

/-- Normalizing the integral subgroup measure preserves inversion
invariance. -/
instance
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsInvInvariant
      (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v) := by
  unfold heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
  exact Measure.isInvInvariant_smul _ _

/-! ## Tail and exceptional products -/

/-- The normalized infinite integral tail is inversion invariant. -/
instance
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
      V v.1
  letI (v : {v // v ∉ S}) :
      Measure.IsInvInvariant
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isInvInvariant
      V v.1
  constructor
  unfold finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ (x v)⁻¹)
        (Measure.infinitePi fun v : {v // v ∉ S} ↦
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) =
      Measure.infinitePi fun v : {v // v ∉ S} ↦
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1
  rw [Measure.infinitePi_map_pi
    (μ := fun v : {v // v ∉ S} ↦
      V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
    (f := fun _ x ↦ x⁻¹)
    (fun _ ↦ measurable_inv)]
  congr 1
  funext v
  exact Measure.map_inv_eq_self
    (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)

/-- The exceptional finite product is inversion invariant. -/
instance finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalExceptionalProductMeasure
  exact Measure.pi.isInvInvariant _

/-- The exceptional/tail source product is inversion invariant. -/
instance
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure S) := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) :=
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite V S
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability V S
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
    infer_instance
  unfold finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
  exact Measure.isInvInvariant_prod _ _

/-! ## Mixed, genuine, and ambient blocks -/

/-- The mixed principal-block cylinder is inversion invariant. -/
instance
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
      |>.continuous.measurable)
    (fun x ↦
      (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv S
        |>.map_inv x))

/-- Coherent scalar normalization preserves mixed-block inversion
invariance. -/
instance
    finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalCoherentMixedPrincipalBlockCylinderMeasure
  exact Measure.isInvInvariant_smul _ _

/-- The coherent genuine principal-block measure is inversion invariant. -/
instance
    finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalCoherentGenuinePrincipalBlockMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S
      |>.symm.continuous.measurable)
    (fun x ↦
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockContinuousMulEquiv S
        |>.symm.map_inv x))

/-- Mapping a genuine block into the ambient finite-adelic group preserves
inversion invariance. -/
instance
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    continuous_subtype_val.measurable
    (fun x ↦
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S
        |>.subtype.map_inv x))

/-! ## Directed global finite-adelic measure -/

/-- The actual finite-adelic invariant-differential measure is invariant
under inversion. -/
instance finiteAdelicInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant V.finiteAdelicInvariantDifferentialGroupMeasure := by
  unfold finiteAdelicInvariantDifferentialGroupMeasure
  exact Measure.directedSup_isInvInvariant
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure
    (fun _ _ hST ↦
      V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_mono hST)
    (fun S ↦
      finiteAdelicSpecialOrthogonalGenuinePrincipalBlockAmbientMeasure_isInvInvariant
        V S)

/-- Consequently the finite-adelic differential measure is globally right
invariant. -/
theorem finiteAdelicInvariantDifferentialGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.finiteAdelicInvariantDifferentialGroupMeasure := by
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.finiteAdelicInvariantDifferentialGroupMeasure

end RationalQuadraticSpaceMatrix
