import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteBlock
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRealFactor
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicUnimodular

/-!
# Evaluation of the retained finite Spin orbit

The finite preimage at the retained central-orbit origin is exhibited as a
right translate of the normalized genuine Spin block source.  Right
invariance of raw finite Spin Haar then evaluates it with coefficient exactly
`finiteScale * spinBlockWeight(B)`.  Combining this with the real
factor gives the full identity-carrier orbital mass at the retained origin.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedTranslationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedTranslationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance retainedTranslationIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedTranslationIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedTranslationExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedTranslationExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedTranslationTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedTranslationTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

local instance retainedTranslationLocalFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedTranslationLocalFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedTranslationMixedSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedTranslationMixedBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock B) :=
  Pi.borelSpace

local instance retainedTranslationFiniteGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedTranslationFiniteGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedTranslationGenuineBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock B) :=
  Subtype.borelSpace _

def retainedSpinBlockSourceToAmbient
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) ×
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) →
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  fun u =>
    L.rationalQuadraticSpaceMatrix
      |>.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom B
        ((L.rationalQuadraticSpaceMatrix
          |>.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm
          ((L.rationalQuadraticSpaceMatrix
            |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B) u))

theorem measurableEmbedding_retainedSpinBlockSourceToAmbient
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (L.retainedSpinBlockSourceToAmbient B) := by
  exact
    (L.rationalQuadraticSpaceMatrix
      |>.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
        B).comp
      (((L.rationalQuadraticSpaceMatrix
        |>.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm
          |>.measurableEmbedding).comp
        ((L.rationalQuadraticSpaceMatrix
          |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B)
            |>.measurableEmbedding))

theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_retainedBlockSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0) :
    (L.rationalQuadraticSpaceMatrix
      |>.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale).comap
        (L.retainedSpinBlockSourceToAmbient B) =
      ((finiteScale : ℝ≥0∞) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
  let i := V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom B
  let e := V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B
  have hi : MeasurableEmbedding i :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding B
  have he : MeasurableEmbedding e.symm := e.symm.measurableEmbedding
  have hm : MeasurableEmbedding m := m.measurableEmbedding
  have heq : (μ.comap i).comap e.symm = Measure.map e (μ.comap i) := by
    symm
    calc
      Measure.map e (μ.comap i) =
          (Measure.map e.symm (Measure.map e (μ.comap i))).comap e.symm := by
            rw [he.comap_map]
      _ = (μ.comap i).comap e.symm :=
        congrArg (fun ν : Measure _ => ν.comap e.symm)
          (MeasurableEquiv.map_symm_map e.toMeasurableEquiv)
  have hmq : (Measure.map e (μ.comap i)).comap m =
      Measure.map m.symm (Measure.map e (μ.comap i)) := by
    symm
    calc
      Measure.map m.symm (Measure.map e (μ.comap i)) =
          (Measure.map m (Measure.map m.symm (Measure.map e (μ.comap i)))).comap m := by
            rw [hm.comap_map]
      _ = (Measure.map e (μ.comap i)).comap m :=
        congrArg (fun ν : Measure _ => ν.comap m)
          (MeasurableEquiv.map_map_symm m.toMeasurableEquiv)
  change μ.comap ((i ∘ e.symm) ∘ m) = _
  calc
    μ.comap ((i ∘ e.symm) ∘ m) = (μ.comap (i ∘ e.symm)).comap m := by
      rw [Measure.comap_comap hm.measurableSet_image'
        (hi.comp he).injective (hi.comp he).measurableSet_image']
    _ = ((μ.comap i).comap e.symm).comap m := by
      rw [Measure.comap_comap he.measurableSet_image' hi.injective hi.measurableSet_image']
    _ = (Measure.map e (μ.comap i)).comap m := by rw [heq]
    _ = Measure.map m.symm (Measure.map e (μ.comap i)) := hmq
    _ = _ := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_block_source
      B finiteScale

theorem retainedSpinBlockSourceToAmbient_component_mem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) ×
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces B) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (L.retainedSpinBlockSourceToAmbient B u) =
      u.1 ⟨v, hv⟩ := by
  let V := L.rationalQuadraticSpaceMatrix
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B u
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m)
    v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show L.retainedSpinBlockSourceToAmbient B u = z.1 by rfl, hz]
  exact V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
    B u v hv

theorem retainedSpinBlockSourceToAmbient_component_notMem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) ×
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces B) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (L.retainedSpinBlockSourceToAmbient B u) =
      (u.2 ⟨v, hv⟩).1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B u
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m)
    v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show L.retainedSpinBlockSourceToAmbient B u = z.1 by rfl, hz]
  exact V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
    B u v hv

def retainedSpinIdentityBlockCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  L.retainedSpinBlockSourceToAmbient B ''
    L.rationalQuadraticSpaceMatrix.retainedSpinExceptionalTailIdentityCylinder B

theorem measurableSet_retainedSpinIdentityBlockCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (L.retainedSpinIdentityBlockCarrier B) := by
  unfold retainedSpinIdentityBlockCarrier
  exact (L.measurableEmbedding_retainedSpinBlockSourceToAmbient B).measurableSet_image.mpr
    ((L.rationalQuadraticSpaceMatrix.measurableSet_retainedSpinExceptionalIdentityCarrier B).prod
      MeasurableSet.univ)

theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_retainedSpinIdentityBlockCarrier
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        finiteScale (L.retainedSpinIdentityBlockCarrier B) =
      ((finiteScale : ℝ≥0∞) *
          L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) *
        (Measure.pi fun v : {v // v ∈
            L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
          L.rationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartSourceMeasure
              (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ := by
  let V := L.rationalQuadraticSpaceMatrix
  let C := V.retainedSpinExceptionalTailIdentityCylinder B
  have h := congrArg (fun ν : Measure _ => ν C)
    (L.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_retainedBlockSource
      B finiteScale)
  change (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale).comap
      (L.retainedSpinBlockSourceToAmbient B) C = _ at h
  rw [(L.measurableEmbedding_retainedSpinBlockSourceToAmbient B).comap_apply] at h
  change V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
      (L.retainedSpinIdentityBlockCarrier B) =
        (((finiteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B) C
      at h
  rw [Measure.smul_apply,
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_identityCylinder]
    at h
  simpa only [smul_eq_mul] using h

def retainedFiniteSpinTranslationSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact
    (fun v => (x.2.1 ⟨v.1, by
      simpa only [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        using v.2⟩).1,
      1)

def retainedFiniteSpinTranslation
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let t := L.retainedFiniteSpinTranslationSource S x
  exact V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom B
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B t))

theorem retainedFiniteSpinTranslation_component_mem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (L.retainedFiniteSpinTranslation S x) =
      x.2.1 ⟨v, hv⟩ := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let t := L.retainedFiniteSpinTranslationSource S x
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B t
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m)
    v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show L.retainedFiniteSpinTranslation S x = z.1 by rfl, hz]
  change (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
    B t v).1 = _
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem]
  · dsimp [t, retainedFiniteSpinTranslationSource]
  · rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
    exact hv

theorem retainedFiniteSpinTranslation_component_notMem
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (L.retainedFiniteSpinTranslation S x) = 1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let t := L.retainedFiniteSpinTranslationSource S x
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B t
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m)
    v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show L.retainedFiniteSpinTranslation S x = z.1 by rfl, hz]
  change (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
    B t v).1 = _
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem]
  · dsimp [t, retainedFiniteSpinTranslationSource]
  · rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
    exact hv

/-- Normalized block coordinates, translated into the finite Spin-orbit
preimage at the retained origin. -/
def retainedSpinBlockSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B →
      V.FiniteAdelicCliffordSpinCandidateGroup := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun u => L.retainedSpinBlockSourceToAmbient B u *
    (L.retainedFiniteSpinTranslation S x)⁻¹

theorem measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    MeasurableEmbedding (L.retainedSpinBlockSourceToOrbitPreimage S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact (Homeomorph.mulRight (L.retainedFiniteSpinTranslation S x)⁻¹
    |>.measurableEmbedding).comp
      (L.measurableEmbedding_retainedSpinBlockSourceToAmbient B)

/-- Raw finite Spin Haar pulled back to the translated orbit-preimage source
has exactly the normalized genuine-block coefficient. -/
theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_retainedOrbitPreimageSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0)
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale).comap
        (L.retainedSpinBlockSourceToOrbitPreimage S x) =
      ((finiteScale : ℝ≥0∞) *
        V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μ := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
  let t := L.retainedFiniteSpinTranslation S x
  let f := Homeomorph.mulRight t
  let j := L.retainedSpinBlockSourceToOrbitPreimage S x
  let i := L.retainedSpinBlockSourceToAmbient B
  have hf : MeasurableEmbedding f := f.measurableEmbedding
  have hj : MeasurableEmbedding j :=
    L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x
  letI : Measure.IsMulRightInvariant
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulRightInvariant
  letI : Measure.IsMulRightInvariant μ := by
    unfold μ RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    infer_instance
  have hmap : Measure.map f μ = μ := by
    exact MeasureTheory.map_mul_right_eq_self μ t
  have hcomap : μ.comap f = μ := by
    calc
      μ.comap f = (Measure.map f μ).comap f :=
        congrArg (fun ν : Measure _ => ν.comap f) hmap.symm
      _ = μ := hf.comap_map μ
  have hfji : f ∘ j = i := by
    funext u
    change (L.retainedSpinBlockSourceToAmbient B u * t⁻¹) * t =
      L.retainedSpinBlockSourceToAmbient B u
    simp
  change μ.comap j = _
  calc
    μ.comap j = (μ.comap f).comap j :=
      congrArg (fun ν : Measure _ => ν.comap j) hcomap.symm
    _ = μ.comap (f ∘ j) := by
      rw [Measure.comap_comap hj.measurableSet_image' hf.injective hf.measurableSet_image']
    _ = μ.comap i := by rw [hfji]
    _ = _ :=
      L.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_retainedBlockSource
        B finiteScale

theorem cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_translation_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x =
      (fun y : V.FiniteAdelicCliffordSpinCandidateGroup =>
        y * L.retainedFiniteSpinTranslation S x) ⁻¹'
          L.retainedSpinIdentityBlockCarrier B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let t := L.retainedFiniteSpinTranslation S x
  have hB : V.cliffordSpinCandidateAdmissibleExceptionalPlaces B = B := by
    simpa only [B, E] using
      L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S
  have mem_B_of_mem_admissible (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B) : v ∈ B := by
    simpa only [hB] using hv
  have notMem_B_of_notMem_admissible (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B) : v ∉ B := by
    simpa only [hB] using hv
  ext y
  have hmem := L.mem_cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_iff S x y
  dsimp only at hmem
  rw [hmem]
  change _ ↔ y * t ∈ L.retainedSpinBlockSourceToAmbient B ''
    V.retainedSpinExceptionalTailIdentityCylinder B
  constructor
  · rintro ⟨hExceptional, hTail⟩
    let uExceptional : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B :=
      fun v => V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y *
        (x.2.1 ⟨v.1, mem_B_of_mem_admissible v.1 v.2⟩).1
    let uTail : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B :=
      fun v => ⟨V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 y, by
        intro _hv
        exact hTail ⟨v.1, notMem_B_of_notMem_admissible v.1 v.2⟩⟩
    let u := (uExceptional, uTail)
    refine ⟨u, ?_, ?_⟩
    · refine ⟨?_, Set.mem_univ _⟩
      intro v _hv
      simpa only [uExceptional] using
        hExceptional ⟨v.1, mem_B_of_mem_admissible v.1 v.2⟩
    · apply V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective
      funext v
      change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
          (L.retainedSpinBlockSourceToAmbient B u) =
        V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v (y * t)
      rw [map_mul]
      by_cases hv : v ∈ B
      · have hvA : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
          rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
          exact hv
        rw [L.retainedSpinBlockSourceToAmbient_component_mem B u v hvA,
          L.retainedFiniteSpinTranslation_component_mem S x v hv]
      · have hvA : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
          rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
          exact hv
        rw [L.retainedSpinBlockSourceToAmbient_component_notMem B u v hvA,
          L.retainedFiniteSpinTranslation_component_notMem S x v hv, mul_one]
  · rintro ⟨u, hu, hEq⟩
    refine ⟨?_, ?_⟩
    · intro v
      have hvA : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
        rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        exact v.2
      have hcomp := congrArg
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1) hEq
      rw [L.retainedSpinBlockSourceToAmbient_component_mem B u v.1 hvA,
        map_mul, L.retainedFiniteSpinTranslation_component_mem S x v.1 v.2] at hcomp
      rw [← hcomp]
      exact hu.1 ⟨v.1, hvA⟩ (Set.mem_univ _)
    · intro v
      have hvB : v.1 ∉ B := v.2
      have hvA : v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B := by
        rw [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        exact hvB
      have hcomp := congrArg
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1) hEq
      rw [L.retainedSpinBlockSourceToAmbient_component_notMem B u v.1 hvA,
        map_mul, L.retainedFiniteSpinTranslation_component_notMem S x v.1 hvB,
        mul_one] at hcomp
      exact hcomp ▸ (u.2 ⟨v.1, hvA⟩).2 hvA

/-- The translated normalized block source has image exactly the retained
finite Spin-orbit preimage. -/
theorem cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_image_orbitPreimageSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x =
      L.retainedSpinBlockSourceToOrbitPreimage S x ''
        V.retainedSpinExceptionalTailIdentityCylinder B := by
  dsimp only
  rw [L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_translation_preimage
    S x]
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let t := L.retainedFiniteSpinTranslation S x
  let i := L.retainedSpinBlockSourceToAmbient B
  let j := L.retainedSpinBlockSourceToOrbitPreimage S x
  ext y
  constructor
  · rintro ⟨u, hu, hut⟩
    refine ⟨u, hu, ?_⟩
    change i u = y * t at hut
    change i u * t⁻¹ = y
    rw [hut]
    simp
  · rintro ⟨u, hu, huy⟩
    refine ⟨u, hu, ?_⟩
    change i u = y * t
    change i u * t⁻¹ = y at huy
    rw [← huy]
    simp

theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_retainedFiniteSpinOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (finiteScale : ℝ≥0)
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
        (L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) =
      ((finiteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) *
        (Measure.pi fun v : {v // v ∈
            V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
          V.padicCliffordSpinCandidateIdentityChartSourceMeasure
              (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ := by
  dsimp only
  rw [L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_translation_preimage
    S x]
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μ := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale
  let t := L.retainedFiniteSpinTranslation S x
  let rightMul := fun y : V.FiniteAdelicCliffordSpinCandidateGroup => y * t
  have hright : Measurable rightMul :=
    (continuous_id.mul continuous_const).measurable
  letI : Measure.IsMulRightInvariant
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulRightInvariant
  letI : Measure.IsMulRightInvariant μ := by
    unfold μ RationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    infer_instance
  have hmap : Measure.map rightMul μ = μ := by
    exact MeasureTheory.map_mul_right_eq_self μ t
  have hsource := congrArg
    (fun ν : Measure V.FiniteAdelicCliffordSpinCandidateGroup =>
      ν (L.retainedSpinIdentityBlockCarrier B)) hmap
  change (Measure.map rightMul μ) (L.retainedSpinIdentityBlockCarrier B) =
    μ (L.retainedSpinIdentityBlockCarrier B) at hsource
  rw [Measure.map_apply hright (L.measurableSet_retainedSpinIdentityBlockCarrier B)]
    at hsource
  rw [L.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_retainedSpinIdentityBlockCarrier
    B finiteScale] at hsource
  exact hsource

/-- The complete retained-origin identity-carrier orbital mass: the only raw
finite coefficient is `spinFiniteScale * spinBlockWeight(B)`, while the real
and exceptional source masses are the chart-source masses. -/
theorem positiveSpinOrbitalKernel_fullSOChartGSpinOrigin_identityChart_eq_blockCoefficient
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      V.realCliffordSpinCandidateChartGluedMeasure
          V.realCliffordSpinCandidateIdentityChart.source *
        (((D.spinFiniteScale : ℝ≥0∞) *
            V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) *
          (Measure.pi fun v : {v // v ∈
              V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
            V.padicCliffordSpinCandidateIdentityChartSourceMeasure
                (Rat.HeightOneSpectrum.primesEquiv v.1).1) Set.univ) := by
  dsimp only
  rw [L.positiveSpinOrbitalKernel_fullSOChartGSpinOrigin_identityChart_eq_realSpin_mul_finite
    hr D S x]
  rw [L.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_retainedFiniteSpinOrbitPreimage
    S D.spinFiniteScale x]

end PositiveDefiniteIntegralLattice

end
