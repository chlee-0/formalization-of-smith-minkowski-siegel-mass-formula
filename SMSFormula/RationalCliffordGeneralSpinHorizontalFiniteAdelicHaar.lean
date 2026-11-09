import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicMeasure

/-!
# Horizontal Haar structure on finite-adelic GSpin

The directed horizontal measure has already been recovered exactly on every
open genuine principal block.  This file transports the block group law and
its left-invariant coherent measure to those genuine blocks and uses the
directed open cover to prove global left invariance.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalFiniteAdelicHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalFiniteAdelicHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalFiniteAdelicHaarFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFiniteAdelicHaarFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalFiniteAdelicHaarBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The genuine block carries the group law transported by simultaneous local
evaluation from the already normalized restricted-family block. -/
noncomputable instance cliffordGeneralSpinHorizontalGenuinePrincipalBlockGroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Group (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Equiv.group
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockEquiv S)

/-- Simultaneous local evaluation is multiplicative for the transported
genuine block law. -/
def cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ≃*
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  Equiv.mulEquiv
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockEquiv S)

/-- The fixed-block homeomorphism is simultaneously multiplicative. -/
def cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ≃ₜ*
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S)
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockMulEquiv S).map_mul

noncomputable instance
    cliffordGeneralSpinHorizontalGenuinePrincipalBlockContinuousMul
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ContinuousMul (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) := by
  let e :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv S
  constructor
  change Continuous (fun p :
      V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ×
        V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S ↦
    e.symm (e p.1 * e p.2))
  exact e.symm.continuous.comp
    ((e.continuous.comp continuous_fst).mul
      (e.continuous.comp continuous_snd))

instance cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S) := by
  unfold cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
  infer_instance

/-- The coherent measure on a genuine block is left invariant for its exact
transported group law. -/
instance cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) := by
  let e :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv S
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
  exact isMulLeftInvariant_map e.symm.toMulHom e.symm.continuous.measurable
    e.symm.surjective

private theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlock_mul_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g h : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (g * h).1.1 v = g.1.1 v * h.1.1 v := by
  let e :=
    V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv S
  have hmul' : e (e.symm g * e.symm h) = g * h := by
    simpa using e.map_mul (e.symm g) (e.symm h)
  calc
    (g * h).1.1 v = (e (e.symm g * e.symm h)).1.1 v :=
      congrArg (fun z ↦ z.1.1 v) hmul'.symm
    _ = (e (e.symm g)).1.1 v * (e (e.symm h)).1.1 v := by
      change
        (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
          S (e.symm g * e.symm h)).1.1 v =
        (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
          S (e.symm g)).1.1 v *
        (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
          S (e.symm h)).1.1 v
      by_cases hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      · rw [V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
            S _ v hv,
          V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
            S _ v hv,
          V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
            S _ v hv]
        rfl
      · rw [V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
            S _ v hv,
          V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
            S _ v hv,
          V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
            S _ v hv]
        rfl
    _ = g.1.1 v * h.1.1 v := by
      rw [e.apply_symm_apply, e.apply_symm_apply]

/-- The transported genuine block multiplication is the literal ambient
intrinsic `GSpin` multiplication on underlying points. -/
@[simp]
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlock_mul_val
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x y : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    (x * y).1 = x.1 * y.1 := by
  apply V.finiteAdelicCliffordGeneralSpinRestrictedFamilyEquiv.injective
  let e :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv S
  calc
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap (x * y).1 =
        (e (x * y)).1 := rfl
    _ = (e x * e y).1 := congrArg Subtype.val (e.map_mul x y)
    _ = V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap (x.1 * y.1) := by
      apply Subtype.ext
      funext v
      rw [V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlock_mul_apply]
      exact
        ((V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul x.1 y.1).symm

/-- Every intrinsic finite-adelic `GSpin` point lies in some genuine
horizontal principal block. -/
theorem exists_mem_cliffordGeneralSpinHorizontalGenuinePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicCliffordGeneralSpinGroup) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
        (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap g) := by
  let bad : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
    {v | ¬ V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v g)}
  have hbad : bad.Finite := by
    simpa only [bad, Filter.eventually_cofinite] using
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap g).2
  let S := hbad.toFinset
  refine ⟨S, ?_⟩
  intro v hv
  by_contra hnot
  have hvS : v ∈ S := by
    simpa [S, bad] using hnot
  exact hv (Finset.mem_union_left _ hvS)

/-- Left translation of one ambient block cylinder is dominated by a block
cylinder whose exceptional set also contains the translator. -/
private theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicCliffordGeneralSpinGroup)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hg : V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyMap g))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map (fun a ↦ g * a)
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T) ≤
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
        (S ∪ T) := by
  let U := S ∪ T
  let i := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition
    T U Finset.subset_union_right
  let gS : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S := ⟨g, hg⟩
  let gU : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock U :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion
      S U Finset.subset_union_left gS
  let μT := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure T
  let μU := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure U
  let valT := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion T
  let valU := V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion U
  let leftG : V.FiniteAdelicCliffordGeneralSpinGroup →
      V.FiniteAdelicCliffordGeneralSpinGroup := fun a ↦ g * a
  let leftGU : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock U →
      V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock U := fun a ↦ gU * a
  have hi : MeasurableEmbedding i :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_measurableEmbedding
      T U Finset.subset_union_right
  have hmapi : Measure.map i μT ≤ μU := by
    rw [V.map_cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_transition
      T U Finset.subset_union_right]
    exact Measure.restrict_le_self
  have hleftG : Measurable leftG := measurable_const_mul g
  have hleftGU : Measurable leftGU := measurable_const_mul gU
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
  change Measure.map leftG (Measure.map valT μT) ≤ Measure.map valU μU
  calc
    Measure.map leftG (Measure.map valT μT) =
        Measure.map valU (Measure.map leftGU (Measure.map i μT)) := by
      rw [Measure.map_map hleftG
          (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
            T).measurable,
        Measure.map_map hleftGU hi.measurable,
        Measure.map_map
          (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
            U).measurable
          (hleftGU.comp hi.measurable)]
      apply congrArg (fun f ↦ Measure.map f μT)
      funext a
      change g * a.1 = (gU * i a).1
      rw [V.cliffordGeneralSpinHorizontalGenuinePrincipalBlock_mul_val]
      change g * a.1 = g * (i a).1
      rw [V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_val]
    _ ≤ Measure.map valU (Measure.map leftGU μU) := by
      exact Measure.map_mono
        (Measure.map_mono hmapi hleftGU)
        (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
          U).measurable
    _ = Measure.map valU μU := by
      rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self gU]

/-- Every ambient left translation sends the directed horizontal measure
below itself. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_map_mul_left_le
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FiniteAdelicCliffordGeneralSpinGroup) :
    Measure.map (fun a ↦ g * a)
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure ≤
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  obtain ⟨S, hg⟩ :=
    V.exists_mem_cliffordGeneralSpinHorizontalGenuinePrincipalBlock g
  apply Measure.le_iff.2
  intro A hA
  have hleft : Measurable
      (fun a : V.FiniteAdelicCliffordGeneralSpinGroup ↦ g * a) :=
    measurable_const_mul g
  rw [Measure.map_apply hleft hA]
  unfold finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  rw [Measure.directedSup_apply _ _ (hleft hA),
    Measure.directedSup_apply _ _ hA]
  apply iSup_le
  intro T
  calc
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T
        ((fun a ↦ g * a) ⁻¹' A) =
      Measure.map (fun a ↦ g * a)
        (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure T) A := by
      rw [Measure.map_apply hleft hA]
    _ ≤ V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
        (S ∪ T) A :=
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_map_mul_left_le
        g S hg T A
    _ ≤ ⨆ U,
        V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure U A :=
      le_iSup
        (fun U ↦
          V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure U A)
        (S ∪ T)

/-- The directed horizontal finite-adelic `GSpin` measure is globally left
invariant. -/
instance finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  constructor
  intro g
  apply le_antisymm
  · exact V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_map_mul_left_le g
  · let leftG : V.FiniteAdelicCliffordGeneralSpinGroup →
        V.FiniteAdelicCliffordGeneralSpinGroup := fun a ↦ g * a
    let leftGInv : V.FiniteAdelicCliffordGeneralSpinGroup →
        V.FiniteAdelicCliffordGeneralSpinGroup := fun a ↦ g⁻¹ * a
    have hleftG : Measurable leftG := measurable_const_mul g
    have hleftGInv : Measurable leftGInv := measurable_const_mul g⁻¹
    calc
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure =
          Measure.map leftG
            (Measure.map leftGInv
              V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
        rw [Measure.map_map hleftG hleftGInv]
        have hfun : leftG ∘ leftGInv = id := by
          funext a
          simp [leftG, leftGInv]
        rw [hfun, Measure.map_id]
      _ ≤ Measure.map leftG
          V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
        exact Measure.map_mono
          (V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_map_mul_left_le
            g⁻¹)
          hleftG

end RationalQuadraticSpaceMatrix
