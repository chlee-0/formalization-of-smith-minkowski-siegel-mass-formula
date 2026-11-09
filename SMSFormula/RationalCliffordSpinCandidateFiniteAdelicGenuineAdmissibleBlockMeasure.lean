import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderMeasure

/-!
# Measures on genuine admissible Clifford--Spin finite-adelic blocks

For a finite set `S`, the preceding layer constructed a left-invariant
cylinder measure on the explicit admissible mixed local block.  This file
transports that measure through the completed genuine/mixed continuous
multiplicative equivalence.  The resulting measure lives on the genuine open
finite-adelic Spin-candidate block, maps back to the literal mixed cylinder,
and has the same exceptional-product total mass.

The genuine block inclusion into the full finite-adelic Spin-candidate group
is also packaged as a measurable embedding.  Mapping the block measure along
that inclusion gives an ambient supported measure whose comap and values on
images recover the block measure exactly.  This ambient pushforward is not
claimed to be invariant under translations by elements outside the block.

No compatibility between exceptional sets, no global finite-adelic measure,
and no analytic identification with the rational Spin top form or the
full-adelic reference Haar scale is asserted.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1000000

local instance finiteAdelicSpinGenuineMeasurePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinGenuineMeasureGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinGenuineMeasureGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicSpinGenuineMeasureGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance finiteAdelicSpinGenuineMeasureLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinGenuineMeasureLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinGenuineMeasureMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinGenuineMeasureMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicSpinGenuineMeasureFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteAdelicSpinGenuineMeasureFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteAdelicSpinGenuineMeasureGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Transport to the genuine block -/

/-- The mixed-block cylinder transported to the genuine open finite-adelic
Spin-candidate block. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Measure.map
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S).symm
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
      S)

/-- Simultaneous local evaluation maps the genuine-block measure back to the
literal mixed-block cylinder. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure_map
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
          S) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S := by
  unfold
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
  exact MeasurableEquiv.map_map_symm
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
      |>.toMeasurableEquiv)

/-- Equivalently, the genuine-block measure is the comap of the mixed cylinder
along simultaneous local evaluation. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure_eq_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure S =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S).comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
          S) := by
  let e :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
  let μ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
      S
  change Measure.map e.symm μ = μ.comap e
  calc
    Measure.map e.symm μ =
        (Measure.map e (Measure.map e.symm μ)).comap e := by
          rw [e.measurableEmbedding.comap_map]
    _ = μ.comap e := by
      exact congrArg (fun ν : Measure _ => ν.comap e)
        (MeasurableEquiv.map_map_symm e.toMeasurableEquiv)

/-- The genuine-block measure has the literal product of the normalized
exceptional local Haar masses. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S Set.univ =
      ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
          Set.univ := by
  rw [finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure]
  rw [Measure.map_apply
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
      S).symm.measurable MeasurableSet.univ]
  simp

/-- The transported measure is left invariant on the genuine admissible
block. -/
instance
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S) := by
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
      S
  unfold
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
  exact isMulLeftInvariant_map
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
      S).symm.toMulHom
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
      S).symm.measurable
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
      S).symm.surjective

/-! ## Inclusion into the full finite-adelic carrier -/

/-- The genuine admissible block inclusion into the full finite-adelic
Spin-candidate group. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateGroup :=
  (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
    S).subtype

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        S a = a.1 :=
  rfl

/-- The genuine admissible block inclusion is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        S) :=
  continuous_subtype_val

/-- The inclusion of the genuine open block is a measurable embedding. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        S) := by
  change MeasurableEmbedding (fun
    a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S =>
      a.1)
  exact
    (V.isOpen_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
      S).isOpenEmbedding_subtypeVal.measurableEmbedding

/-- The supported ambient cylinder obtained by pushing the genuine-block
measure into the full finite-adelic Spin-candidate carrier. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure V.FiniteAdelicCliffordSpinCandidateGroup :=
  Measure.map
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S)
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
      S)

/-- Comapping the ambient supported cylinder to its genuine block recovers
the transported block measure exactly. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
      S).comap
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S) =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S := by
  unfold
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
  exact
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S).comap_map
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
          S)

/-- The ambient supported cylinder evaluates on the image of an arbitrary
block set as the original genuine-block measure. -/
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure_apply_image
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Set
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S)) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
        S
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
          S '' s) =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S s := by
  unfold
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
  rw [
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
      S).map_apply,
    Set.preimage_image_eq _
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
        S).injective]

/-- The ambient supported cylinder has the same exceptional-product total
mass as the genuine and mixed block measures. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
        S Set.univ =
      ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
          Set.univ := by
  rw [
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure,
    Measure.map_apply
      (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
        S).measurable
      MeasurableSet.univ]
  simp

end RationalQuadraticSpaceMatrix
