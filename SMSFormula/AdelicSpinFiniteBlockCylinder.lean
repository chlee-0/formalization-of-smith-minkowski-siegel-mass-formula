import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedFiniteBlock

/-!
# Raw finite-adelic Spin mass of block cylinders

For any finite set `B` of places, the genuine admissible block of the finite-adelic Spin
candidate group is parametrized by the exceptional local factors and the integral tail.  The
image of a rectangle `∏_{v ∈ exc B} E_v × (integral tail)` is the cylinder of finite-adelic
points whose `v`-components lie in `E_v` for `v ∈ exc B` and are integral otherwise; its raw
mass is `finiteScale · blockWeight(B) · ∏_{v ∈ exc B} μ_v(E_v)`.  This is the block-source
identity evaluated on rectangles; nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance finiteBlockCylinderDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteBlockCylinderPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteBlockCylinderIntegralFactorSecondCountable
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (v : V.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteBlockCylinderIntegralFactorBorelSpace
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (v : V.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance finiteBlockCylinderExceptionalSecondCountable (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteBlockCylinderExceptionalBorelSpace (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance finiteBlockCylinderTailSecondCountable (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteBlockCylinderTailBorelSpace (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

local instance finiteBlockCylinderLocalFactorSecondCountable (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteBlockCylinderLocalFactorBorelSpace (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor B v) :=
  Subtype.borelSpace _

local instance finiteBlockCylinderMixedSecondCountable (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteBlockCylinderMixedBorelSpace (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock B) :=
  Pi.borelSpace

local instance finiteBlockCylinderFiniteGroupMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup := borel _

local instance finiteBlockCylinderFiniteGroupBorelSpace :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup := ⟨rfl⟩

local instance finiteBlockCylinderGenuineBorelSpace (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock B) :=
  Subtype.borelSpace _

/-- The genuine-block source parametrization by exceptional local factors and the integral tail. -/
def finiteBlockSourceToAmbient (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B →
      V.FiniteAdelicCliffordSpinCandidateGroup :=
  fun u ↦ V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom B
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B) u))

theorem measurableEmbedding_finiteBlockSourceToAmbient (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding (V.finiteBlockSourceToAmbient B) :=
  (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding B).comp
    (((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm.measurableEmbedding).comp
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B).measurableEmbedding))

theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_finiteBlockSource
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (finiteScale : ℝ≥0) :
    (V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale).comap
        (V.finiteBlockSourceToAmbient B) =
      ((finiteScale : ℝ≥0∞) * V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B := by
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
      Measure.map e (μ.comap i) = (Measure.map e.symm (Measure.map e (μ.comap i))).comap e.symm := by
        rw [he.comap_map]
      _ = (μ.comap i).comap e.symm :=
        congrArg (fun ν : Measure _ => ν.comap e.symm) (MeasurableEquiv.map_symm_map e.toMeasurableEquiv)
  have hmq : (Measure.map e (μ.comap i)).comap m = Measure.map m.symm (Measure.map e (μ.comap i)) := by
    symm
    calc
      Measure.map m.symm (Measure.map e (μ.comap i)) =
          (Measure.map m (Measure.map m.symm (Measure.map e (μ.comap i)))).comap m := by
        rw [hm.comap_map]
      _ = (Measure.map e (μ.comap i)).comap m :=
        congrArg (fun ν : Measure _ => ν.comap m) (MeasurableEquiv.map_map_symm m.toMeasurableEquiv)
  change μ.comap ((i ∘ e.symm) ∘ m) = _
  calc
    μ.comap ((i ∘ e.symm) ∘ m) = (μ.comap (i ∘ e.symm)).comap m := by
      rw [Measure.comap_comap hm.measurableSet_image' (hi.comp he).injective (hi.comp he).measurableSet_image']
    _ = ((μ.comap i).comap e.symm).comap m := by
      rw [Measure.comap_comap he.measurableSet_image' hi.injective hi.measurableSet_image']
    _ = (Measure.map e (μ.comap i)).comap m := by rw [heq]
    _ = Measure.map m.symm (Measure.map e (μ.comap i)) := hmq
    _ = _ := V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_block_source B finiteScale

theorem finiteBlockSourceToAmbient_component_mem (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v (V.finiteBlockSourceToAmbient B u) =
      u.1 ⟨v, hv⟩ := by
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B u
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m) v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show V.finiteBlockSourceToAmbient B u = z.1 by rfl, hz]
  exact V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem B u v hv

theorem finiteBlockSourceToAmbient_component_notMem (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (u : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v (V.finiteBlockSourceToAmbient B u) =
      (u.2 ⟨v, hv⟩).1 := by
  let m := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B u
  let z := (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm m
  have hz := congrArg Subtype.val (congrFun
    ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).apply_symm_apply m) v)
  change V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z.1 = (m v).1 at hz
  rw [show V.finiteBlockSourceToAmbient B u = z.1 by rfl, hz]
  exact V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem B u v hv

/-- The block cylinder of local conditions `E_v` at the exceptional places, integral elsewhere. -/
def finiteBlockCylinder (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (E : ∀ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
      Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1)) :
    Set V.FiniteAdelicCliffordSpinCandidateGroup :=
  V.finiteBlockSourceToAmbient B '' (Set.univ.pi E ×ˢ Set.univ)

theorem measurableSet_finiteBlockCylinder (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {E : ∀ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
      Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1)} (hE : ∀ v, MeasurableSet (E v)) :
    MeasurableSet (V.finiteBlockCylinder B E) :=
  (V.measurableEmbedding_finiteBlockSourceToAmbient B).measurableSet_image.mpr
    ((MeasurableSet.univ_pi hE).prod MeasurableSet.univ)

/-- The raw mass of a block cylinder. -/
theorem finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_finiteBlockCylinder
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (finiteScale : ℝ≥0)
    {E : ∀ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
      Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1)} (hE : ∀ v, MeasurableSet (E v)) :
    V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure finiteScale (V.finiteBlockCylinder B E) =
      (finiteScale : ℝ≥0∞) * V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B *
        ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
          V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1 (E v) := by
  rw [finiteBlockCylinder, ← (V.measurableEmbedding_finiteBlockSourceToAmbient B).comap_apply,
    V.finiteAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_comap_finiteBlockSource B finiteScale,
    Measure.smul_apply, smul_eq_mul]
  congr 1
  unfold finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_pi B E

theorem mem_genuineBlock_of_isIntegral (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.FiniteAdelicCliffordSpinCandidateGroup)
    (hx : ∀ v, v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B →
      V.HeightOnePadicCliffordSpinCandidateIsIntegral v (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x)) :
    x ∈ V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup B := by
  rw [V.mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup_iff,
    V.isFiniteAdelicCliffordSpinCandidateIntegralOutside_iff]
  exact fun v hv ↦ (V.finiteAdelicCliffordSpinCandidateHeightOneComponent_isIntegral_iff x v).1 (hx v hv)

/-- Membership in a block cylinder is a condition on the local components. -/
theorem mem_finiteBlockCylinder_iff (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (E : ∀ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
      Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1))
    (x : V.FiniteAdelicCliffordSpinCandidateGroup) :
    x ∈ V.finiteBlockCylinder B E ↔
      (∀ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B},
        V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v.1 x ∈ E v) ∧
      ∀ v, v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B →
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v x) := by
  constructor
  · rintro ⟨u, ⟨hu, -⟩, rfl⟩
    refine ⟨fun v ↦ ?_, fun v hv ↦ ?_⟩
    · rw [V.finiteBlockSourceToAmbient_component_mem B u v.1 v.2]
      exact hu v (Set.mem_univ _)
    · rw [V.finiteBlockSourceToAmbient_component_notMem B u v hv]
      exact (u.2 ⟨v, hv⟩).2 hv
  · rintro ⟨hE, hI⟩
    let z : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock B :=
      ⟨x, V.mem_genuineBlock_of_isIntegral B x hI⟩
    let u := (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B).symm
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B z)
    have hux : V.finiteBlockSourceToAmbient B u = x := by
      change V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom B
        ((V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B).symm
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B)
            ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph B).symm
              (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph B z)))) = x
      rw [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
      rfl
    refine ⟨u, ⟨fun v _ ↦ ?_, Set.mem_univ _⟩, hux⟩
    have := V.finiteBlockSourceToAmbient_component_mem B u v.1 v.2
    rw [hux] at this
    rw [← this]
    exact hE v

end RationalQuadraticSpaceMatrix
