import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Direct cylinder measures on mixed finite-adelic principal blocks

For a finite exceptional set `S`, this module puts the unnormalized
invariant-differential Haar measure on every full local factor in `S`, takes
their finite dependent product, and multiplies it by the normalized integral
tail measure.

The resulting source product is mapped through the direct exceptional/tail
homeomorphism to the mixed principal-block carrier.  All topology and
measurability come from the displayed product factors.  Nothing is
transported through the algebraic equivalence with the restricted-family
block subtype.

No compatibility between different exceptional sets, global finite-adelic
measure, quotient measure, or Tamagawa theorem is introduced.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance mixedPrincipalBlockCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockCylinderGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockCylinderGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance mixedPrincipalBlockCylinderGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance mixedPrincipalBlockCylinderIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockCylinderIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockCylinderLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockCylinderLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockCylinderExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockCylinderMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockCylinderMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Exceptional local and finite-product measures -/

/-- The unnormalized invariant-differential Haar measure at a height-one
place, named on the exact local carrier used by the exceptional product. -/
def heightOnePadicInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicInvariantDifferentialGroupMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- The height-one local differential measure is Haar. -/
theorem heightOnePadicInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure
      (V.heightOnePadicInvariantDifferentialGroupMeasure v) := by
  exact
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Every exceptional local differential Haar measure is sigma-finite. -/
instance heightOnePadicInvariantDifferentialGroupMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SigmaFinite (V.heightOnePadicInvariantDifferentialGroupMeasure v) := by
  exact
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      (Rat.HeightOneSpectrum.primesEquiv v).1 n
      V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- Every exceptional local differential Haar measure is left invariant. -/
instance heightOnePadicInvariantDifferentialGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (V.heightOnePadicInvariantDifferentialGroupMeasure v) :=
  (V.heightOnePadicInvariantDifferentialGroupMeasure_isHaarMeasure v)
    |>.toIsMulLeftInvariant

/-- The finite dependent product of the unnormalized local differential Haar
measures at the exceptional places. -/
def finiteAdelicSpecialOrthogonalExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    V.heightOnePadicInvariantDifferentialGroupMeasure v.1

/-- The exceptional finite product has the literal rectangle formula. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalProductMeasure_pi
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S},
      Set (V.HeightOnePadicSpecialOrthogonalGroup v.1)) :
    V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S
        (Set.pi Set.univ s) =
      ∏ v : {v // v ∈ S},
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1 (s v) := by
  unfold finiteAdelicSpecialOrthogonalExceptionalProductMeasure
  exact Measure.pi_pi _ s

/-- The exceptional finite product has the literal product of local total
masses. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalProductMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S Set.univ =
      ∏ v : {v // v ∈ S},
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1 Set.univ := by
  unfold finiteAdelicSpecialOrthogonalExceptionalProductMeasure
  exact Measure.pi_univ _

/-- The exceptional finite product is sigma-finite. -/
instance finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalExceptionalProductMeasure
  infer_instance

/-- The exceptional finite product is left invariant under componentwise
multiplication. -/
instance
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
  unfold finiteAdelicSpecialOrthogonalExceptionalProductMeasure
  exact Measure.pi.isMulLeftInvariant _

/-! ## Direct source product and mixed-block cylinder -/

/-- The direct cylinder source measure: unnormalized exceptional product
times normalized integral tail. -/
def finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
    (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S)

/-- The direct exceptional/tail source product is left invariant. -/
instance
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
        S) := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) :=
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite V S
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
      V S
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
  exact Measure.prod.instIsMulLeftInvariant

/-- The direct mixed principal-block cylinder measure obtained by mapping the
exceptional/tail product through the direct product homeomorphism. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :=
  Measure.map
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S)
    (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure S)

/-- Mapping the mixed-block cylinder back through the direct splitting
recovers the literal exceptional/tail product measure. -/
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_map_symm
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S).symm
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S) =
      V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure S := by
  unfold finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
  exact
    MeasurableEquiv.map_symm_map
      (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
        |>.toMeasurableEquiv)

/-- The direct mixed-block cylinder has the literal product of exceptional
local total masses; the normalized tail contributes one. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S
        Set.univ =
      ∏ v : {v // v ∈ S},
        V.heightOnePadicInvariantDifferentialGroupMeasure v.1 Set.univ := by
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) :=
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_isSigmaFinite V S
  letI : SFinite
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
      V S
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure,
    Measure.map_apply
      (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S
        |>.continuous.measurable)
      MeasurableSet.univ]
  change
    V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure S
        Set.univ =
      _
  rw [
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure,
    ← Set.univ_prod_univ,
    Measure.prod_prod,
    finiteAdelicSpecialOrthogonalExceptionalProductMeasure_univ,
    measure_univ,
    mul_one]

/-- With no exceptional coordinates, the normalized direct mixed cylinder
has total mass one. -/
@[simp]
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_empty_univ
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
        ∅ Set.univ = 1 := by
  rw [V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_univ]
  simp

/-- The direct mixed-block cylinder measure is left invariant. -/
instance
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure S) := by
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure
        S) :=
    finiteAdelicSpecialOrthogonalExceptionalTailCylinderSourceMeasure_isMulLeftInvariant
      V S
  unfold finiteAdelicSpecialOrthogonalMixedPrincipalBlockCylinderMeasure
  exact isMulLeftInvariant_map
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv S
      |>.toMulHom)
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv S
      |>.continuous.measurable)
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv S
      |>.surjective)

end RationalQuadraticSpaceMatrix
