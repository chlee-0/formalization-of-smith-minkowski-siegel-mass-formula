import SMSFormula.RationalIdeleDifferentialExceptionalTailMeasure

/-!
# Coherent transitions for differential idele exceptional/tail sources

For finite sets `S ⊆ T`, split the larger exceptional product into the old
and newly exceptional coordinates, and split the smaller integral tail into
the newly exceptional integral coordinates and the common tail.  The
transition includes only the new integral coordinates into their unrestricted
local groups.  Because every local integral subgroup has literal Haar mass
one, the direct source measures comap exactly, with no transition scalar.

No transport to the finite-idele restricted product, ambient finite-idele
Haar equality, square-map modulus, Euler product, or idele-class quotient
comparison is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2400000

local instance rationalIdeleTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleTransitionLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleTransitionLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleTransitionLocalSecondCountable
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

local instance rationalIdeleTransitionIntegralSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleTransitionIntegralBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Subtype.borelSpace _

/-! ## New coordinates -/

/-- The unrestricted coordinates newly added when `S` is enlarged to `T`. -/
abbrev RationalIdeleDifferentialNewExceptionalProduct
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ T \ S}) →
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ

/-- The same new coordinates constrained to their integral-unit subgroups. -/
abbrev RationalIdeleDifferentialNewIntegralProduct
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ T \ S}) →
    padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-! ## Exceptional-coordinate splitting -/

def rationalIdeleDifferentialExceptionalTransitionSplit
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialExceptionalProduct T →
      RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialNewExceptionalProduct S T :=
  fun z ↦
    (fun v ↦ z ⟨v.1, hST v.2⟩,
    fun v ↦ z ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)

def rationalIdeleDifferentialExceptionalTransitionAssemble
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialNewExceptionalProduct S T) →
      RationalIdeleDifferentialExceptionalProduct T :=
  fun z v ↦
    if hv : v.1 ∈ S then z.1 ⟨v.1, hv⟩
    else z.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩

def rationalIdeleDifferentialExceptionalTransitionHomeomorph
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialExceptionalProduct T ≃ₜ
      RationalIdeleDifferentialExceptionalProduct S ×
        RationalIdeleDifferentialNewExceptionalProduct S T where
  toFun := rationalIdeleDifferentialExceptionalTransitionSplit S T hST
  invFun := rationalIdeleDifferentialExceptionalTransitionAssemble S T hST
  left_inv := by
    intro z
    funext v
    by_cases hv : v.1 ∈ S
    · simp [rationalIdeleDifferentialExceptionalTransitionSplit,
        rationalIdeleDifferentialExceptionalTransitionAssemble, hv]
    · simp [rationalIdeleDifferentialExceptionalTransitionSplit,
        rationalIdeleDifferentialExceptionalTransitionAssemble, hv]
  right_inv := by
    intro z
    apply Prod.ext
    · funext v
      simp [rationalIdeleDifferentialExceptionalTransitionSplit,
        rationalIdeleDifferentialExceptionalTransitionAssemble]
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).2
      unfold rationalIdeleDifferentialExceptionalTransitionSplit
      simp [rationalIdeleDifferentialExceptionalTransitionAssemble, hv]
  continuous_toFun := by
    unfold rationalIdeleDifferentialExceptionalTransitionSplit
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.1 ∈ S
    · simpa [rationalIdeleDifferentialExceptionalTransitionAssemble, hv]
        using (continuous_apply (⟨v.1, hv⟩ : {v // v ∈ S}))
          |>.comp continuous_fst
    · simpa [rationalIdeleDifferentialExceptionalTransitionAssemble, hv]
        using (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ : {v // v ∈ T \ S}))
          |>.comp continuous_snd

/-! ## Integral-tail splitting -/

private def rationalIdeleDifferentialTailCommonPlace
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (v : {v // v ∉ T}) : {v // v ∉ S} :=
  ⟨v.1, fun hv ↦ v.2 (hST hv)⟩

def rationalIdeleDifferentialIntegralTailTransitionSplit
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialIntegralTail S →
      RationalIdeleDifferentialNewIntegralProduct S T ×
        RationalIdeleDifferentialIntegralTail T :=
  fun z ↦
    (fun v ↦ z ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
    fun v ↦ z (rationalIdeleDifferentialTailCommonPlace S T hST v))

def rationalIdeleDifferentialIntegralTailTransitionAssemble
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (RationalIdeleDifferentialNewIntegralProduct S T ×
      RationalIdeleDifferentialIntegralTail T) →
      RationalIdeleDifferentialIntegralTail S :=
  fun z v ↦
    if hv : v.1 ∈ T then
      z.1 ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
    else z.2 ⟨v.1, hv⟩

def rationalIdeleDifferentialIntegralTailTransitionHomeomorph
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialIntegralTail S ≃ₜ
      RationalIdeleDifferentialNewIntegralProduct S T ×
        RationalIdeleDifferentialIntegralTail T where
  toFun := rationalIdeleDifferentialIntegralTailTransitionSplit S T hST
  invFun := rationalIdeleDifferentialIntegralTailTransitionAssemble S T hST
  left_inv := by
    intro z
    funext v
    by_cases hv : v.1 ∈ T
    · simp [rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialIntegralTailTransitionAssemble, hv]
    · simp [rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialIntegralTailTransitionAssemble, hv,
        rationalIdeleDifferentialTailCommonPlace]
  right_inv := by
    intro z
    apply Prod.ext
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).1
      simp [rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialIntegralTailTransitionAssemble, hv]
    · funext v
      simp [rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialIntegralTailTransitionAssemble, v.2,
        rationalIdeleDifferentialTailCommonPlace]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun v ↦ continuous_apply
        (⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ : {v // v ∉ S})
    · exact continuous_pi fun v ↦ continuous_apply
        (rationalIdeleDifferentialTailCommonPlace S T hST v)
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.1 ∈ T
    · simpa [rationalIdeleDifferentialIntegralTailTransitionAssemble, hv]
        using (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩ : {v // v ∈ T \ S}))
          |>.comp continuous_fst
    · simpa [rationalIdeleDifferentialIntegralTailTransitionAssemble, hv]
        using (continuous_apply (⟨v.1, hv⟩ : {v // v ∉ T}))
          |>.comp continuous_snd

/-! ## New-coordinate measures and inclusion -/

noncomputable def rationalIdeleDifferentialNewExceptionalProductMeasure
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialNewExceptionalProduct S T) :=
  Measure.pi fun v : {v // v ∈ T \ S} ↦
    rationalPadicIdeleDifferentialHaarMeasure v.1

noncomputable instance
    rationalIdeleDifferentialNewExceptionalProductMeasure_isSigmaFinite
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (rationalIdeleDifferentialNewExceptionalProductMeasure S T) := by
  unfold rationalIdeleDifferentialNewExceptionalProductMeasure
  infer_instance

noncomputable def rationalIdeleDifferentialNewIntegralProductMeasure
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialNewIntegralProduct S T) :=
  Measure.pi fun v : {v // v ∈ T \ S} ↦
    rationalPadicIdeleIntegralFactorMeasure v.1

noncomputable instance
    rationalIdeleDifferentialNewIntegralProductMeasure_isProbability
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (rationalIdeleDifferentialNewIntegralProductMeasure S T) := by
  letI (v : {v // v ∈ T \ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  unfold rationalIdeleDifferentialNewIntegralProductMeasure
  infer_instance

/-- Componentwise inclusion of the newly exceptional integral coordinates. -/
def rationalIdeleDifferentialNewIntegralExceptionalInclusion
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialNewIntegralProduct S T →
      RationalIdeleDifferentialNewExceptionalProduct S T :=
  fun z v ↦ (z v).1

theorem rationalIdeleDifferentialNewIntegralExceptionalInclusion_measurableEmbedding
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (rationalIdeleDifferentialNewIntegralExceptionalInclusion S T) := by
  have hlocal :
      ∀ v : {v // v ∈ T \ S},
        Topology.IsOpenEmbedding
          (fun z : padicIntegralUnitsSubgroup
              (Rat.HeightOneSpectrum.primesEquiv v.1).1 ↦
            (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)) := by
    intro v
    exact (isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).isOpenEmbedding_subtypeVal
  exact (Topology.IsOpenEmbedding.piMap hlocal).measurableEmbedding

theorem rationalIdeleDifferentialNewExceptionalProductMeasure_comap_inclusion
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (rationalIdeleDifferentialNewExceptionalProductMeasure S T).comap
        (rationalIdeleDifferentialNewIntegralExceptionalInclusion S T) =
      rationalIdeleDifferentialNewIntegralProductMeasure S T := by
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [rationalIdeleDifferentialNewIntegralProductMeasure]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(rationalIdeleDifferentialNewIntegralExceptionalInclusion_measurableEmbedding
    S T).comap_apply]
  change
    rationalIdeleDifferentialNewExceptionalProductMeasure S T
        (Pi.map (fun v
          (z : padicIntegralUnitsSubgroup
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) ↦
              (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)) ''
          Set.pi Set.univ s) = _
  rw [Set.piMap_image_univ_pi]
  unfold rationalIdeleDifferentialNewExceptionalProductMeasure
  rw [Measure.pi_pi]
  congr 1
  funext v
  unfold rationalPadicIdeleIntegralFactorMeasure
  exact
    (((isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).isOpenEmbedding_subtypeVal
        |>.measurableEmbedding).comap_apply
      (rationalPadicIdeleDifferentialHaarMeasure v.1) (s v)).symm

/-! ## Exact product splittings -/

private theorem measurePreserving_rationalIdeleInfinitePiEquivPiSubtypeProd
    {iota : Type*} {X : iota → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (p : iota → Prop) [DecidablePred p] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd X p)
      (Measure.infinitePi mu)
      ((Measure.infinitePi fun i : Subtype p ↦ mu i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} ↦ mu i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [e.map_apply]
  have hpre :
      e ⁻¹' Set.pi (s : Set iota) t =
        Set.pi (s.subtype p : Set (Subtype p)) (fun i ↦ t i) ×ˢ
          Set.pi (s.subtype (fun i ↦ ¬ p i) : Set {i // ¬ p i})
            (fun i ↦ t i) := by
    ext ⟨f, g⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_subtype, e]
    constructor
    · intro h
      constructor
      · intro i hi
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2] using h i hi
      · intro i hi
        simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2] using h i hi
    · rintro ⟨hf, hg⟩ i hi
      by_cases hpi : p i
      · simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, hpi] using
          hf ⟨i, hpi⟩ hi
      · simpa [e, Equiv.piEquivPiSubtypeProd_symm_apply, hpi] using
          hg ⟨i, hpi⟩ hi
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · have hp :
        (∏ i ∈ s.subtype p, mu i (t i)) =
          ∏ i ∈ (s.filter p).attach, mu i.1 (t i.1) := by
      unfold Finset.subtype
      rw [Finset.prod_map]
      rfl
    have hnp :
        (∏ i ∈ s.subtype (fun i ↦ ¬ p i), mu i (t i)) =
          ∏ i ∈ (s.filter (fun i ↦ ¬ p i)).attach,
            mu i.1 (t i.1) := by
      unfold Finset.subtype
      rw [Finset.prod_map]
      rfl
    rw [hp, hnp,
      Finset.prod_attach (s.filter p) (fun i ↦ mu i (t i)),
      Finset.prod_attach (s.filter (fun i ↦ ¬ p i))
        (fun i ↦ mu i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i ↦ mu i (t i))
  · intro i hi
    exact ht i
  · intro i hi
    exact ht i

private def rationalIdeleExceptionalOldIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∈ S} ≃ {v : {v // v ∈ T} // v.1 ∈ S} where
  toFun v := ⟨⟨v.1, hST v.2⟩, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rationalIdeleExceptionalNewIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ T \ S} ≃ {v : {v // v ∈ T} // v.1 ∉ S} where
  toFun v := ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
    (Finset.mem_sdiff.mp v.2).2⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.1.2, v.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rationalIdeleTailNewIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ T \ S} ≃ {v : {v // v ∉ S} // v.1 ∈ T} where
  toFun v := ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
    (Finset.mem_sdiff.mp v.2).1⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.2, v.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rationalIdeleTailCommonIndexEquiv
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∉ T} ≃ {v : {v // v ∉ S} // v.1 ∉ T} where
  toFun v := ⟨rationalIdeleDifferentialTailCommonPlace S T hST v, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rationalIdeleDifferentialExceptionalProductMeasure_map_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (rationalIdeleDifferentialExceptionalTransitionHomeomorph S T hST)
        (rationalIdeleDifferentialExceptionalProductMeasure T) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).prod
        (rationalIdeleDifferentialNewExceptionalProductMeasure S T) := by
  let p : {v // v ∈ T} → Prop := fun v ↦ v.1 ∈ S
  let oldReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ S} ↦
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (rationalIdeleExceptionalOldIndexEquiv S T hST).symm
  let newReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ T \ S} ↦
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (rationalIdeleExceptionalNewIndexEquiv S T).symm
  have hPart := measurePreserving_piEquivPiSubtypeProd
    (fun v : {v // v ∈ T} ↦
      rationalPadicIdeleDifferentialHaarMeasure v.1) p
  have hOld := measurePreserving_piCongrLeft
    (fun v : {v // v ∈ S} ↦
      rationalPadicIdeleDifferentialHaarMeasure v.1)
    (rationalIdeleExceptionalOldIndexEquiv S T hST).symm
  have hNew := measurePreserving_piCongrLeft
    (fun v : {v // v ∈ T \ S} ↦
      rationalPadicIdeleDifferentialHaarMeasure v.1)
    (rationalIdeleExceptionalNewIndexEquiv S T).symm
  have hCombined := (hOld.prod hNew).comp hPart
  have hfun :
      (Prod.map oldReindex newReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∈ T} ↦
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) p) =
        rationalIdeleDifferentialExceptionalTransitionHomeomorph S T hST := by
    funext z
    apply Prod.ext <;> funext v <;> rfl
  simpa only [rationalIdeleDifferentialExceptionalProductMeasure,
    rationalIdeleDifferentialNewExceptionalProductMeasure, hfun] using
      hCombined.map_eq

theorem rationalIdeleDifferentialNormalizedIntegralTailMeasure_map_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (rationalIdeleDifferentialIntegralTailTransitionHomeomorph S T hST)
        (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) =
      (rationalIdeleDifferentialNewIntegralProductMeasure S T).prod
        (rationalIdeleDifferentialNormalizedIntegralTailMeasure T) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  letI (v : {v // v ∉ T}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  let p : {v // v ∉ S} → Prop := fun v ↦ v.1 ∈ T
  let newReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ T \ S} ↦
      padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    (rationalIdeleTailNewIndexEquiv S T).symm
  let commonReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∉ T} ↦
      padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    (rationalIdeleTailCommonIndexEquiv S T hST).symm
  have hPart := measurePreserving_rationalIdeleInfinitePiEquivPiSubtypeProd
    (fun v : {v // v ∉ S} ↦
      rationalPadicIdeleIntegralFactorMeasure v.1) p
  have hNew :
      MeasurePreserving newReindex
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1)
        (rationalIdeleDifferentialNewIntegralProductMeasure S T) := by
    refine ⟨newReindex.measurable, ?_⟩
    simpa only [rationalIdeleDifferentialNewIntegralProductMeasure,
      Measure.infinitePi_eq_pi] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∈ T \ S} ↦
            rationalPadicIdeleIntegralFactorMeasure v.1)
          (rationalIdeleTailNewIndexEquiv S T).symm)
  have hCommon :
      MeasurePreserving commonReindex
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1)
        (rationalIdeleDifferentialNormalizedIntegralTailMeasure T) := by
    refine ⟨commonReindex.measurable, ?_⟩
    simpa only [rationalIdeleDifferentialNormalizedIntegralTailMeasure,
      commonReindex] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∉ T} ↦
            rationalPadicIdeleIntegralFactorMeasure v.1)
          (rationalIdeleTailCommonIndexEquiv S T hST).symm)
  letI : SFinite
      (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) := inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  letI : SFinite
      (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) := inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hCombined := (MeasurePreserving.prod
    (μa := Measure.infinitePi fun v : {v : {v // v ∉ S} // p v} ↦
      rationalPadicIdeleIntegralFactorMeasure v.1.1)
    (μc := Measure.infinitePi fun v : {v : {v // v ∉ S} // ¬ p v} ↦
      rationalPadicIdeleIntegralFactorMeasure v.1.1)
    hNew hCommon).comp hPart
  have hfun :
      (Prod.map newReindex commonReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∉ S} ↦
              padicIntegralUnitsSubgroup
                (Rat.HeightOneSpectrum.primesEquiv v.1).1) p) =
        rationalIdeleDifferentialIntegralTailTransitionHomeomorph S T hST := by
    funext z
    apply Prod.ext <;> funext v <;> rfl
  simpa only [rationalIdeleDifferentialNormalizedIntegralTailMeasure, hfun]
    using hCombined.map_eq

/-! ## Direct source transition and exact coherence -/

private theorem rationalIdeleComapProdMap
    {alpha beta gamma delta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSpace gamma] [MeasurableSpace delta]
    {f : alpha → beta} {g : gamma → delta}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (mu : Measure beta) (nu : Measure delta)
    [SigmaFinite mu] [SigmaFinite nu]
    [SigmaFinite (mu.comap f)] [SigmaFinite (nu.comap g)] :
    (mu.prod nu).comap (Prod.map f g) =
      (mu.comap f).prod (nu.comap g) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [(hf.prodMap hg).comap_apply, Set.prodMap_image_prod,
    Measure.prod_prod, hf.comap_apply, hg.comap_apply]

private theorem rationalIdeleComapIdProdMapId
    {gamma delta epsilon zeta : Type*}
    [MeasurableSpace gamma] [MeasurableSpace delta]
    [MeasurableSpace epsilon] [MeasurableSpace zeta]
    {f : gamma → delta} (hf : MeasurableEmbedding f)
    (mu : Measure epsilon) (nu : Measure delta) (kappa : Measure zeta)
    [SigmaFinite mu] [SigmaFinite nu] [SigmaFinite kappa]
    [SigmaFinite (nu.comap f)] :
    (mu.prod (nu.prod kappa)).comap
        (Prod.map (fun x ↦ x) (Prod.map f (fun x ↦ x))) =
      mu.prod ((nu.comap f).prod kappa) := by
  have hmu : MeasurableEmbedding (fun x : epsilon ↦ x) :=
    MeasurableEmbedding.id
  have hkappa : MeasurableEmbedding (fun x : zeta ↦ x) :=
    MeasurableEmbedding.id
  letI : SigmaFinite (kappa.comap (fun x ↦ x)) := by
    rw [Measure.comap_id]
    infer_instance
  letI : SigmaFinite (mu.comap (fun x ↦ x)) := by
    rw [Measure.comap_id]
    infer_instance
  letI : SigmaFinite ((nu.prod kappa).comap
      (Prod.map f (fun x ↦ x))) := by
    rw [rationalIdeleComapProdMap hf hkappa, Measure.comap_id]
    infer_instance
  rw [rationalIdeleComapProdMap hmu (hf.prodMap hkappa), Measure.comap_id,
    rationalIdeleComapProdMap hf hkappa, Measure.comap_id]

def rationalIdeleDifferentialLargerTransitionSourceHomeomorph
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (RationalIdeleDifferentialExceptionalProduct T ×
      RationalIdeleDifferentialIntegralTail T) ≃ₜ
    (RationalIdeleDifferentialExceptionalProduct S ×
      (RationalIdeleDifferentialNewExceptionalProduct S T ×
        RationalIdeleDifferentialIntegralTail T)) :=
  (Homeomorph.prodCongr
    (rationalIdeleDifferentialExceptionalTransitionHomeomorph S T hST)
    (Homeomorph.refl _)).trans (Homeomorph.prodAssoc _ _ _)

def rationalIdeleDifferentialSmallerTransitionSourceHomeomorph
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) ≃ₜ
    (RationalIdeleDifferentialExceptionalProduct S ×
      (RationalIdeleDifferentialNewIntegralProduct S T ×
        RationalIdeleDifferentialIntegralTail T)) :=
  Homeomorph.prodCongr (Homeomorph.refl _)
    (rationalIdeleDifferentialIntegralTailTransitionHomeomorph S T hST)

def rationalIdeleDifferentialTransitionSourceInclusion
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (RationalIdeleDifferentialExceptionalProduct S ×
      (RationalIdeleDifferentialNewIntegralProduct S T ×
        RationalIdeleDifferentialIntegralTail T)) →
    (RationalIdeleDifferentialExceptionalProduct S ×
      (RationalIdeleDifferentialNewExceptionalProduct S T ×
        RationalIdeleDifferentialIntegralTail T)) :=
  Prod.map (fun z ↦ z)
    (Prod.map
      (rationalIdeleDifferentialNewIntegralExceptionalInclusion S T)
      (fun z ↦ z))

theorem rationalIdeleDifferentialTransitionSourceInclusion_measurableEmbedding
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (rationalIdeleDifferentialTransitionSourceInclusion S T) := by
  exact MeasurableEmbedding.id.prodMap
    ((rationalIdeleDifferentialNewIntegralExceptionalInclusion_measurableEmbedding
      S T).prodMap MeasurableEmbedding.id)

/-- The direct source transition obtained by splitting, including the new
integral coordinates, and reassembling. -/
def rationalIdeleDifferentialExceptionalTailTransition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) →
    (RationalIdeleDifferentialExceptionalProduct T ×
      RationalIdeleDifferentialIntegralTail T) :=
  (rationalIdeleDifferentialLargerTransitionSourceHomeomorph S T hST).symm ∘
    rationalIdeleDifferentialTransitionSourceInclusion S T ∘
      rationalIdeleDifferentialSmallerTransitionSourceHomeomorph S T hST

theorem rationalIdeleDifferentialExceptionalTailTransition_measurableEmbedding
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (rationalIdeleDifferentialExceptionalTailTransition S T hST) :=
  (rationalIdeleDifferentialLargerTransitionSourceHomeomorph S T hST).symm
    |>.measurableEmbedding.comp
      ((rationalIdeleDifferentialTransitionSourceInclusion_measurableEmbedding S T).comp
        (rationalIdeleDifferentialSmallerTransitionSourceHomeomorph S T hST
          |>.measurableEmbedding))

theorem rationalIdeleDifferentialExceptionalTailSourceMeasure_map_largerTransition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (rationalIdeleDifferentialLargerTransitionSourceHomeomorph S T hST)
        (rationalIdeleDifferentialExceptionalTailSourceMeasure T) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).prod
        ((rationalIdeleDifferentialNewExceptionalProductMeasure S T).prod
          (rationalIdeleDifferentialNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure T) := inferInstance
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  have hidTail :
      Measure.map (fun z ↦ z)
          (rationalIdeleDifferentialNormalizedIntegralTailMeasure T) =
        rationalIdeleDifferentialNormalizedIntegralTailMeasure T :=
    Measure.map_id
  have hAssoc :
      Measure.map (Homeomorph.prodAssoc
          (RationalIdeleDifferentialExceptionalProduct S)
          (RationalIdeleDifferentialNewExceptionalProduct S T)
          (RationalIdeleDifferentialIntegralTail T))
        (((rationalIdeleDifferentialExceptionalProductMeasure S).prod
          (rationalIdeleDifferentialNewExceptionalProductMeasure S T)).prod
            (rationalIdeleDifferentialNormalizedIntegralTailMeasure T)) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).prod
        ((rationalIdeleDifferentialNewExceptionalProductMeasure S T).prod
          (rationalIdeleDifferentialNormalizedIntegralTailMeasure T)) := by
    exact Measure.prodAssoc_prod
  unfold rationalIdeleDifferentialLargerTransitionSourceHomeomorph
    rationalIdeleDifferentialExceptionalTailSourceMeasure
  change Measure.map
    ((Homeomorph.prodAssoc _ _ _) ∘
      Prod.map
        (rationalIdeleDifferentialExceptionalTransitionHomeomorph S T hST)
        (fun z ↦ z)) _ = _
  rw [← Measure.map_map, ← Measure.map_prod_map,
    rationalIdeleDifferentialExceptionalProductMeasure_map_transition S T hST,
    hidTail, hAssoc]
  all_goals fun_prop

theorem rationalIdeleDifferentialExceptionalTailSourceMeasure_map_smallerTransition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (rationalIdeleDifferentialSmallerTransitionSourceHomeomorph S T hST)
        (rationalIdeleDifferentialExceptionalTailSourceMeasure S) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).prod
        ((rationalIdeleDifferentialNewIntegralProductMeasure S T).prod
          (rationalIdeleDifferentialNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  have hid :
      Measure.map (Homeomorph.refl
          (RationalIdeleDifferentialExceptionalProduct S))
          (rationalIdeleDifferentialExceptionalProductMeasure S) =
        rationalIdeleDifferentialExceptionalProductMeasure S :=
    Measure.map_id
  unfold rationalIdeleDifferentialSmallerTransitionSourceHomeomorph
    rationalIdeleDifferentialExceptionalTailSourceMeasure
  rw [Homeomorph.coe_prodCongr, ← Measure.map_prod_map, hid,
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_map_transition S T hST]
  all_goals fun_prop

theorem rationalIdeleDifferentialTransitionSourceProduct_comap
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ((rationalIdeleDifferentialExceptionalProductMeasure S).prod
      ((rationalIdeleDifferentialNewExceptionalProductMeasure S T).prod
        (rationalIdeleDifferentialNormalizedIntegralTailMeasure T))).comap
        (rationalIdeleDifferentialTransitionSourceInclusion S T) =
      (rationalIdeleDifferentialExceptionalProductMeasure S).prod
        ((rationalIdeleDifferentialNewIntegralProductMeasure S T).prod
          (rationalIdeleDifferentialNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (rationalIdeleDifferentialNewExceptionalProductMeasure S T) := inferInstance
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (rationalIdeleDifferentialNewIntegralProductMeasure S T) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      ((rationalIdeleDifferentialNewExceptionalProductMeasure S T).comap
        (rationalIdeleDifferentialNewIntegralExceptionalInclusion S T)) := by
    rw [rationalIdeleDifferentialNewExceptionalProductMeasure_comap_inclusion S T]
    infer_instance
  unfold rationalIdeleDifferentialTransitionSourceInclusion
  rw [rationalIdeleComapIdProdMapId
      (rationalIdeleDifferentialNewIntegralExceptionalInclusion_measurableEmbedding S T)
      (rationalIdeleDifferentialExceptionalProductMeasure S)
      (rationalIdeleDifferentialNewExceptionalProductMeasure S T)
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure T),
    rationalIdeleDifferentialNewExceptionalProductMeasure_comap_inclusion S T]

/-- Enlarging the exceptional set preserves the direct source measure
literally.  The absence of a scalar is exactly the local integral-unit volume
one normalization. -/
theorem rationalIdeleDifferentialExceptionalTailSourceMeasure_comap_transition
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (rationalIdeleDifferentialExceptionalTailSourceMeasure T).comap
        (rationalIdeleDifferentialExceptionalTailTransition S T hST) =
      rationalIdeleDifferentialExceptionalTailSourceMeasure S := by
  let larger := rationalIdeleDifferentialLargerTransitionSourceHomeomorph
    S T hST
  let smaller := rationalIdeleDifferentialSmallerTransitionSourceHomeomorph
    S T hST
  let coordinate := rationalIdeleDifferentialExceptionalTailTransition S T hST
  let inclusion := rationalIdeleDifferentialTransitionSourceInclusion S T
  have hCoordinate : MeasurableEmbedding coordinate :=
    rationalIdeleDifferentialExceptionalTailTransition_measurableEmbedding S T hST
  have hInclusion : MeasurableEmbedding inclusion :=
    rationalIdeleDifferentialTransitionSourceInclusion_measurableEmbedding S T
  have hfun : larger ∘ coordinate = inclusion ∘ smaller := by
    funext z
    simp only [larger, coordinate,
      rationalIdeleDifferentialExceptionalTailTransition, Function.comp_apply]
    exact larger.apply_symm_apply _
  calc
    (rationalIdeleDifferentialExceptionalTailSourceMeasure T).comap coordinate =
        ((Measure.map larger
          (rationalIdeleDifferentialExceptionalTailSourceMeasure T)).comap
            larger).comap coordinate := by
      rw [larger.measurableEmbedding.comap_map]
    _ = (Measure.map larger
          (rationalIdeleDifferentialExceptionalTailSourceMeasure T)).comap
            (larger ∘ coordinate) := by
      rw [Measure.comap_comap hCoordinate.measurableSet_image' larger.injective
        larger.measurableEmbedding.measurableSet_image']
    _ = (Measure.map larger
          (rationalIdeleDifferentialExceptionalTailSourceMeasure T)).comap
            (inclusion ∘ smaller) := by rw [hfun]
    _ = ((Measure.map larger
          (rationalIdeleDifferentialExceptionalTailSourceMeasure T)).comap
            inclusion).comap smaller := by
      rw [Measure.comap_comap smaller.measurableEmbedding.measurableSet_image'
        hInclusion.injective hInclusion.measurableSet_image']
    _ = (((rationalIdeleDifferentialExceptionalProductMeasure S).prod
          ((rationalIdeleDifferentialNewExceptionalProductMeasure S T).prod
            (rationalIdeleDifferentialNormalizedIntegralTailMeasure T))).comap
              inclusion).comap smaller := by
      rw [rationalIdeleDifferentialExceptionalTailSourceMeasure_map_largerTransition
        S T hST]
    _ = ((rationalIdeleDifferentialExceptionalProductMeasure S).prod
          ((rationalIdeleDifferentialNewIntegralProductMeasure S T).prod
            (rationalIdeleDifferentialNormalizedIntegralTailMeasure T))).comap
              smaller := by
      rw [rationalIdeleDifferentialTransitionSourceProduct_comap S T]
    _ = rationalIdeleDifferentialExceptionalTailSourceMeasure S := by
      rw [← rationalIdeleDifferentialExceptionalTailSourceMeasure_map_smallerTransition
        S T hST, smaller.measurableEmbedding.comap_map]

end RationalQuadraticSpaceMatrix
