import SMSFormula.RationalIdeleDifferentialFiniteIdeleMeasure

/-!
# Global invariance of the differential finite-idele measure

The transported exceptional/tail group law on every genuine principal block
is the literal ambient finite-idele multiplication.  Every finite idele lies
in one such block.  Exact block coherence therefore promotes the directed
finite-exceptional measure to a globally left-invariant ambient measure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance rationalIdeleFiniteHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleFiniteHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleFiniteHaarAmbientMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleFiniteHaarAmbientBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleFiniteHaarBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance rationalIdeleFiniteHaarLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleFiniteHaarLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleFiniteHaarLocalSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := by
  letI : SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ×
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ) :=
    inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance rationalIdeleFiniteHaarIntegralBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Subtype.borelSpace _

local instance rationalIdeleFiniteHaarIntegralSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleFiniteHaarExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

local instance rationalIdeleFiniteHaarTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

/-- A genuine block carries the group law transported from its direct
exceptional/tail coordinates. -/
noncomputable instance rationalIdeleDifferentialGenuinePrincipalBlockGroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Group (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Equiv.group
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S).symm

/-- Direct exceptional/tail coordinates are multiplicative for the
transported genuine-block law. -/
def rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialIntegralTail S) ≃*
      RationalIdeleDifferentialGenuinePrincipalBlock S :=
  { toEquiv :=
      rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S
    map_mul' := by
      intro x y
      change
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S)
            (x * y) =
          (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S)
            ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S).symm
                ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S) x) *
              (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S).symm
                ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S) y))
      rw [(rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S)
          |>.symm_apply_apply,
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockEquiv S)
          |>.symm_apply_apply] }

/-- The fixed-block homeomorphism is simultaneously multiplicative. -/
def rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialIntegralTail S) ≃ₜ*
      RationalIdeleDifferentialGenuinePrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph S)
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockMulEquiv S).map_mul

noncomputable instance rationalIdeleDifferentialGenuinePrincipalBlockContinuousMul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ContinuousMul (RationalIdeleDifferentialGenuinePrincipalBlock S) := by
  let e :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv S
  constructor
  change Continuous (fun p :
      RationalIdeleDifferentialGenuinePrincipalBlock S ×
        RationalIdeleDifferentialGenuinePrincipalBlock S ↦
    e (e.symm p.1 * e.symm p.2))
  exact e.continuous.comp
    ((e.symm.continuous.comp continuous_fst).mul
      (e.symm.continuous.comp continuous_snd))

/-- The genuine block measure is left invariant for its transported group
law. -/
instance rationalIdeleDifferentialGenuinePrincipalBlockMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S) := by
  let e :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv S
  unfold rationalIdeleDifferentialGenuinePrincipalBlockMeasure
  exact isMulLeftInvariant_map e.toMulHom e.continuous.measurable e.surjective

private theorem rationalIdeleDifferentialExceptionalTailLocalUnit_mul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x y : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalIdeleDifferentialExceptionalTailLocalUnit S (x * y) v =
      rationalIdeleDifferentialExceptionalTailLocalUnit S x v *
        rationalIdeleDifferentialExceptionalTailLocalUnit S y v := by
  by_cases hv : v ∈ S
  · simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv]
  · simp [rationalIdeleDifferentialExceptionalTailLocalUnit, hv]

/-- The transported genuine-block multiplication is literal ambient
finite-idele multiplication on underlying points. -/
@[simp]
theorem rationalIdeleDifferentialGenuinePrincipalBlock_mul_val
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x y : RationalIdeleDifferentialGenuinePrincipalBlock S) :
    (x * y).1 = x.1 * y.1 := by
  let e :=
    rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv S
  have hxy : x * y = e (e.symm x * e.symm y) := by
    simpa using (e.map_mul (e.symm x) (e.symm y)).symm
  rw [hxy]
  apply Units.ext
  ext v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
  change
    ((finiteAdelicUnitHeightOneComponentHom v
        (e (e.symm x * e.symm y)).1 :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
      ((finiteAdelicUnitHeightOneComponentHom v (x.1 * y.1) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  rw [show finiteAdelicUnitHeightOneComponentHom v
      (e (e.symm x * e.symm y)).1 =
        rationalIdeleDifferentialExceptionalTailLocalUnit S
          (e.symm x * e.symm y) v by
      exact exceptionalTailToGenuinePrincipalBlock_component S _ v]
  rw [rationalIdeleDifferentialExceptionalTailLocalUnit_mul]
  rw [← exceptionalTailToGenuinePrincipalBlock_component S (e.symm x) v,
    ← exceptionalTailToGenuinePrincipalBlock_component S (e.symm y) v]
  rw [show rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S
        (e.symm x) = x by exact e.apply_symm_apply x,
    show rationalIdeleDifferentialExceptionalTailToGenuinePrincipalBlock S
        (e.symm y) = y by exact e.apply_symm_apply y]
  exact congrArg Units.val
    ((finiteAdelicUnitHeightOneComponentHom v).map_mul x.1 y.1).symm

/-- Every rational finite idele belongs to its literal finite-support
principal block. -/
theorem exists_mem_rationalIdeleDifferentialGenuinePrincipalBlock
    (a : RationalFiniteAdeleˣ) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      IsRationalIdeleDifferentialGenuinePrincipalBlock S a := by
  refine ⟨finiteIdeleNormSupport a, ?_⟩
  intro v hv
  rw [mem_padicIntegralUnitsSubgroup_iff]
  have h := (not_mem_finiteIdeleNormSupport_iff a v).1 hv
  exact ⟨(mem_adicCompletionIntegers_iff_padic v _).1 h.1,
    (mem_adicCompletionIntegers_iff_padic v _).1 h.2⟩

/-- Left translation of an ambient block cylinder is dominated by the block
cylinder whose exceptional set also contains the translator. -/
private theorem
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_map_mul_left_le
    (g : RationalFiniteAdeleˣ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hg : IsRationalIdeleDifferentialGenuinePrincipalBlock S g)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map (fun a ↦ g * a)
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T) ≤
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure (S ∪ T) := by
  let U := S ∪ T
  let i := rationalIdeleDifferentialGenuinePrincipalBlockTransition
    T U Finset.subset_union_right
  let gS : RationalIdeleDifferentialGenuinePrincipalBlock S := ⟨g, hg⟩
  let gU : RationalIdeleDifferentialGenuinePrincipalBlock U :=
    rationalIdeleDifferentialGenuinePrincipalBlockInclusion
      S U Finset.subset_union_left gS
  let muT := rationalIdeleDifferentialGenuinePrincipalBlockMeasure T
  let muU := rationalIdeleDifferentialGenuinePrincipalBlockMeasure U
  let valT := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion T
  let valU := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion U
  let leftG : RationalFiniteAdeleˣ → RationalFiniteAdeleˣ := fun a ↦ g * a
  let leftGU : RationalIdeleDifferentialGenuinePrincipalBlock U →
      RationalIdeleDifferentialGenuinePrincipalBlock U := fun a ↦ gU * a
  have hi : MeasurableEmbedding i :=
    rationalIdeleDifferentialGenuinePrincipalBlockTransition_measurableEmbedding
      T U Finset.subset_union_right
  have hmapi : Measure.map i muT ≤ muU := by
    rw [map_rationalIdeleDifferentialGenuinePrincipalBlockMeasure_transition
      T U Finset.subset_union_right]
    exact Measure.restrict_le_self
  have hleftG : Measurable leftG := measurable_const_mul g
  have hleftGU : Measurable leftGU := measurable_const_mul gU
  unfold rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
  change Measure.map leftG (Measure.map valT muT) ≤ Measure.map valU muU
  calc
    Measure.map leftG (Measure.map valT muT) =
        Measure.map valU (Measure.map leftGU (Measure.map i muT)) := by
      rw [Measure.map_map hleftG
          (continuous_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
            T).measurable,
        Measure.map_map hleftGU hi.measurable,
        Measure.map_map
          (continuous_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
            U).measurable
          (hleftGU.comp hi.measurable)]
      apply congrArg (fun f ↦ Measure.map f muT)
      funext a
      change g * a.1 = (gU * i a).1
      rw [rationalIdeleDifferentialGenuinePrincipalBlock_mul_val]
      change g * a.1 = g * (i a).1
      rw [rationalIdeleDifferentialGenuinePrincipalBlockTransition_val]
    _ ≤ Measure.map valU (Measure.map leftGU muU) := by
      exact Measure.map_mono
        (Measure.map_mono hmapi hleftGU)
        (continuous_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion
          U).measurable
    _ = Measure.map valU muU := by
      rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self gU]

/-- Every ambient left translation sends the directed differential measure
below itself. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_map_mul_left_le
    (g : RationalFiniteAdeleˣ) :
    Measure.map (fun a ↦ g * a) rationalFiniteIdeleDifferentialDirectedMeasure ≤
      rationalFiniteIdeleDifferentialDirectedMeasure := by
  obtain ⟨S, hg⟩ :=
    exists_mem_rationalIdeleDifferentialGenuinePrincipalBlock g
  apply Measure.le_iff.2
  intro A hA
  have hleft : Measurable (fun a : RationalFiniteAdeleˣ ↦ g * a) :=
    measurable_const_mul g
  rw [Measure.map_apply hleft hA]
  unfold rationalFiniteIdeleDifferentialDirectedMeasure
  rw [Measure.directedSup_apply _ _ (hleft hA),
    Measure.directedSup_apply _ _ hA]
  apply iSup_le
  intro T
  calc
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T
        ((fun a ↦ g * a) ⁻¹' A) =
      Measure.map (fun a ↦ g * a)
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure T) A := by
      rw [Measure.map_apply hleft hA]
    _ ≤ rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure
        (S ∪ T) A :=
      rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure_map_mul_left_le
        g S hg T A
    _ ≤ ⨆ U, rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure U A :=
      le_iSup
        (fun U ↦ rationalIdeleDifferentialGenuinePrincipalBlockAmbientMeasure U A)
        (S ∪ T)

/-- The directed differential finite-idele measure is globally left
invariant. -/
instance rationalFiniteIdeleDifferentialDirectedMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant rationalFiniteIdeleDifferentialDirectedMeasure := by
  constructor
  intro g
  apply le_antisymm
  · exact rationalFiniteIdeleDifferentialDirectedMeasure_map_mul_left_le g
  · let leftG : RationalFiniteAdeleˣ → RationalFiniteAdeleˣ := fun a ↦ g * a
    let leftGInv : RationalFiniteAdeleˣ → RationalFiniteAdeleˣ :=
      fun a ↦ g⁻¹ * a
    have hleftG : Measurable leftG := measurable_const_mul g
    have hleftGInv : Measurable leftGInv := measurable_const_mul g⁻¹
    calc
      rationalFiniteIdeleDifferentialDirectedMeasure =
          Measure.map leftG
            (Measure.map leftGInv rationalFiniteIdeleDifferentialDirectedMeasure) := by
        rw [Measure.map_map hleftG hleftGInv]
        have hfun : leftG ∘ leftGInv = id := by
          funext a
          simp [leftG, leftGInv]
        rw [hfun, Measure.map_id]
      _ ≤ Measure.map leftG rationalFiniteIdeleDifferentialDirectedMeasure := by
        exact Measure.map_mono
          (rationalFiniteIdeleDifferentialDirectedMeasure_map_mul_left_le g⁻¹)
          hleftG

end RationalQuadraticSpaceMatrix
