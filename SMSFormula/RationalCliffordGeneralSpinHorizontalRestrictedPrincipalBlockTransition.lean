import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlock

/-!
# Coherent transitions for horizontal GSpin restricted-family blocks

For `S ⊆ T`, the effective exceptional sets are `S ∪ badPlaces` and
`T ∪ badPlaces`.  This file splits the larger exceptional product and the
smaller normalized integral tail along their literal finite difference.  The
new unrestricted coordinates comap to the new integral coordinates with the
product of their fixed horizontal integral volumes.

Conjugating this source calculation through the exact restricted-family block
homeomorphisms gives the transition law for the actual principal-block
cylinders.  Reciprocal finite-volume weights then make those cylinders
strictly coherent.  No genuine finite-adelic transport, quotient measure,
Euler product, or global Haar scalar is introduced.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2400000

local instance horizontalRestrictedTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalRestrictedTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalRestrictedTransitionGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalRestrictedTransitionGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance horizontalRestrictedTransitionIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalRestrictedTransitionIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalRestrictedTransitionExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedTransitionExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalRestrictedTransitionTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedTransitionTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

/-! ## Effective exceptional sets and transition factors -/

/-- The literal exceptional set used by the horizontal source at `S`. -/
abbrev cliffordGeneralSpinHorizontalExceptionalPlaces
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces

theorem cliffordGeneralSpinHorizontalExceptionalPlaces_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.cliffordGeneralSpinHorizontalExceptionalPlaces S ⊆
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T := by
  intro v hv
  exact Finset.mem_union.mpr <| (Finset.mem_union.mp hv).elim
    (fun h ↦ Or.inl (hST h)) Or.inr

/-- New unrestricted coordinates introduced by enlarging `S` to `T`. -/
abbrev CliffordGeneralSpinHorizontalNewExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S}) →
    V.HeightOnePadicCliffordGeneralSpinGroup v.1

/-- The same new coordinates, restricted to the fixed integral subgroup. -/
abbrev CliffordGeneralSpinHorizontalNewIntegralProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S}) →
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- The literal finite product of new-coordinate integral volumes. -/
def cliffordGeneralSpinHorizontalTransitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S},
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1

theorem cliffordGeneralSpinHorizontalTransitionVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalTransitionVolume S T ≠ 0 := by
  unfold cliffordGeneralSpinHorizontalTransitionVolume
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

theorem cliffordGeneralSpinHorizontalTransitionVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalTransitionVolume S T ≠ ⊤ := by
  unfold cliffordGeneralSpinHorizontalTransitionVolume
  exact ENNReal.prod_ne_top fun v _ ↦
    V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v.1

/-! ## Exceptional-coordinate splitting -/

def cliffordGeneralSpinHorizontalExceptionalTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalExceptionalProduct T →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T :=
  fun g ↦
    (fun v ↦ g ⟨v.1,
      V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST v.2⟩,
    fun v ↦ g ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)

def cliffordGeneralSpinHorizontalExceptionalTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) →
      V.CliffordGeneralSpinHorizontalExceptionalProduct T :=
  fun g v ↦
    if hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S then
      g.1 ⟨v.1, hv⟩
    else
      g.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩

def cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalExceptionalProduct T ≃ₜ
      V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T where
  toFun := V.cliffordGeneralSpinHorizontalExceptionalTransitionSplit S T hST
  invFun :=
    V.cliffordGeneralSpinHorizontalExceptionalTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    by_cases hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S
    · simp [cliffordGeneralSpinHorizontalExceptionalTransitionSplit,
        cliffordGeneralSpinHorizontalExceptionalTransitionAssemble, hv]
    · simp [cliffordGeneralSpinHorizontalExceptionalTransitionSplit,
        cliffordGeneralSpinHorizontalExceptionalTransitionAssemble, hv]
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      simp [cliffordGeneralSpinHorizontalExceptionalTransitionSplit,
        cliffordGeneralSpinHorizontalExceptionalTransitionAssemble]
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).2
      unfold cliffordGeneralSpinHorizontalExceptionalTransitionSplit
      simp [cliffordGeneralSpinHorizontalExceptionalTransitionAssemble, hv]
  continuous_toFun := by
    unfold cliffordGeneralSpinHorizontalExceptionalTransitionSplit
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S
    · simpa [cliffordGeneralSpinHorizontalExceptionalTransitionAssemble, hv]
        using (continuous_apply (⟨v.1, hv⟩ :
          {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S}))
          |>.comp continuous_fst
    · simpa [cliffordGeneralSpinHorizontalExceptionalTransitionAssemble, hv]
        using (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ :
            {v // v ∈
              V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
                V.cliffordGeneralSpinHorizontalExceptionalPlaces S}))
          |>.comp continuous_snd

/-! ## Integral-tail splitting -/

private def horizontalTailCommonPlace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace T) :
    V.CliffordGeneralSpinHorizontalIntegralPlace S :=
  ⟨v.1, fun hv ↦
    v.2 (V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST hv)⟩

def cliffordGeneralSpinHorizontalIntegralTailTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalIntegralTail S →
      V.CliffordGeneralSpinHorizontalNewIntegralProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T :=
  fun g ↦
    (fun v ↦ g ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
    fun v ↦
      let w := horizontalTailCommonPlace V S T hST v
      ⟨(g w).1, (g w).2⟩)

def cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T ×
      V.CliffordGeneralSpinHorizontalIntegralTail T) →
      V.CliffordGeneralSpinHorizontalIntegralTail S :=
  fun g v ↦
    if hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T then
      let w : {v // v ∈
          V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
            V.cliffordGeneralSpinHorizontalExceptionalPlaces S} :=
        ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
      ⟨(g.1 w).1, (g.1 w).2⟩
    else
      let w : V.CliffordGeneralSpinHorizontalIntegralPlace T := ⟨v.1, hv⟩
      ⟨(g.2 w).1, (g.2 w).2⟩

def cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalIntegralTail S ≃ₜ
      V.CliffordGeneralSpinHorizontalNewIntegralProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T where
  toFun := V.cliffordGeneralSpinHorizontalIntegralTailTransitionSplit S T hST
  invFun :=
    V.cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    apply Subtype.ext
    unfold cliffordGeneralSpinHorizontalIntegralTailTransitionSplit
    by_cases hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T
    · change
        ((if h : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T then
          _ else _ :
          V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).1) = g v
      rw [dif_pos hv]
    · change
        ((if h : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T then
          _ else _ :
          V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).1) = g v
      rw [dif_neg hv]
      rfl
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).1
      apply Subtype.ext
      change
        ((if h : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T then
          _ else _ :
          V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
            ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩).1) = (g.1 v).1
      rw [dif_pos hv]
    · funext v
      apply Subtype.ext
      change
        ((if h : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T then
          _ else _ :
          V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
            (horizontalTailCommonPlace V S T hST v)).1) = (g.2 v).1
      rw [dif_neg v.2]
      rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun v ↦ continuous_apply
        (⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ :
          V.CliffordGeneralSpinHorizontalIntegralPlace S)
    · apply continuous_pi
      intro v
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp
          (continuous_apply (horizontalTailCommonPlace V S T hST v))) _
  continuous_invFun := by
    apply continuous_pi
    intro v
    by_cases hv : v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T
    ·
      let w : {v // v ∈
          V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
            V.cliffordGeneralSpinHorizontalExceptionalPlaces S} :=
        ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
      have hfun :
          (fun g ↦
            V.cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble
              S T hST g v) =
            (fun g ↦ ⟨(g.1 w).1, (g.1 w).2⟩) := by
        funext g
        apply Subtype.ext
        simp [cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble,
          hv, w]
      rw [hfun]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp
          ((continuous_apply w).comp continuous_fst)) _
    ·
      let w : V.CliffordGeneralSpinHorizontalIntegralPlace T := ⟨v.1, hv⟩
      have hfun :
          (fun g ↦
            V.cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble
              S T hST g v) =
            (fun g ↦ ⟨(g.2 w).1, (g.2 w).2⟩) := by
        funext g
        apply Subtype.ext
        simp [cliffordGeneralSpinHorizontalIntegralTailTransitionAssemble,
          hv, w]
      rw [hfun]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp
          ((continuous_apply w).comp continuous_snd)) _

/-! ## The exact new-coordinate measure factor -/

local instance horizontalRestrictedTransitionNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedTransitionNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance horizontalRestrictedTransitionNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedTransitionNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T) :=
  Pi.borelSpace

/-- The unrestricted horizontal Haar product on the finitely many new
exceptional coordinates. -/
def cliffordGeneralSpinHorizontalNewExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T) :=
  Measure.pi fun v ↦
    V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1

instance cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T) := by
  unfold cliffordGeneralSpinHorizontalNewExceptionalProductMeasure
  infer_instance

/-- The product of the unnormalized integral-factor measures on the new
coordinates. -/
def cliffordGeneralSpinHorizontalNewIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T) :=
  Measure.pi fun v ↦
    V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- The product of normalized integral-factor probabilities on the new
coordinates. -/
def cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T) :=
  Measure.pi fun v ↦
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

private theorem
    padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_eq_volume_smul_normalized
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v =
      V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 •
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v := by
  rw [padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure,
    ← smul_assoc]
  simp only [smul_eq_mul]
  rw [ENNReal.mul_inv_cancel
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v.1), one_smul]

theorem cliffordGeneralSpinHorizontalNewIntegralProductMeasure_eq_transitionVolume_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalNewIntegralProductMeasure S T =
      V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T := by
  unfold cliffordGeneralSpinHorizontalNewIntegralProductMeasure
    cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure
    cliffordGeneralSpinHorizontalTransitionVolume
  letI (v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S}) :
      SigmaFinite
        (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S
          ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  letI (v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S}) :
      SigmaFinite
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
          ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi _ s]
  simp only [smul_eq_mul]
  simp_rw [padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_eq_volume_smul_normalized,
    Measure.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib.symm

/-- Componentwise inclusion of the new integral coordinates into the new
unrestricted coordinates. -/
def cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalNewIntegralProduct S T →
      V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T :=
  fun g v ↦ (g v).1

theorem cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion S T) := by
  have hlocal :
      ∀ v : {v // v ∈
          V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
            V.cliffordGeneralSpinHorizontalExceptionalPlaces S},
        Topology.IsOpenEmbedding
          (fun g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
              ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ ↦
            (g : V.HeightOnePadicCliffordGeneralSpinGroup v.1)) := by
    intro v
    exact
      (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S
        ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩).isOpenEmbedding_subtypeVal
  exact (Topology.IsOpenEmbedding.piMap hlocal).measurableEmbedding

theorem cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_comap_inclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).comap
        (V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion S T) =
      V.cliffordGeneralSpinHorizontalNewIntegralProductMeasure S T := by
  letI (v : {v // v ∈
      V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
        V.cliffordGeneralSpinHorizontalExceptionalPlaces S}) :
      SigmaFinite
        (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S
          ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [cliffordGeneralSpinHorizontalNewIntegralProductMeasure]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion_measurableEmbedding
    S T).comap_apply]
  change
    V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T
        (Pi.map (fun v
          (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
            ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) ↦
              (g : V.HeightOnePadicCliffordGeneralSpinGroup v.1)) ''
          Set.pi Set.univ s) = _
  rw [Set.piMap_image_univ_pi]
  unfold cliffordGeneralSpinHorizontalNewExceptionalProductMeasure
  rw [Measure.pi_pi]
  congr 1
  funext v
  unfold heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
    padicCliffordGeneralSpinHorizontalIntegralFactorMeasure
  exact
    (((V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩).isOpenEmbedding_subtypeVal
        |>.measurableEmbedding).comap_apply
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) (s v)).symm

/-! ## Exact product splittings -/

private theorem measurePreserving_horizontalInfinitePiEquivPiSubtypeProd
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd X p)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : Subtype p ↦ μ i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} ↦ μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [e.map_apply]
  have hpre :
      e ⁻¹' Set.pi (s : Set ι) t =
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
        (∏ i ∈ s.subtype p, μ i (t i)) =
          ∏ i ∈ (s.filter p).attach, μ i.1 (t i.1) := by
        unfold Finset.subtype
        rw [Finset.prod_map]
        rfl
    have hnp :
        (∏ i ∈ s.subtype (fun i ↦ ¬ p i), μ i (t i)) =
          ∏ i ∈ (s.filter (fun i ↦ ¬ p i)).attach,
            μ i.1 (t i.1) := by
        unfold Finset.subtype
        rw [Finset.prod_map]
        rfl
    rw [hp, hnp,
      Finset.prod_attach (s.filter p) (fun i ↦ μ i (t i)),
      Finset.prod_attach (s.filter (fun i ↦ ¬ p i))
        (fun i ↦ μ i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i ↦ μ i (t i))
  · intro i hi
    exact ht i
  · intro i hi
    exact ht i

private def horizontalExceptionalOldIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ≃
      {v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} //
        v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} where
  toFun v := ⟨⟨v.1,
    V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST v.2⟩, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def horizontalExceptionalNewIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ≃
      {v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} //
        v.1 ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} where
  toFun v := ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
    (Finset.mem_sdiff.mp v.2).2⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.1.2, v.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def horizontalTailNewIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ≃
      {v : V.CliffordGeneralSpinHorizontalIntegralPlace S //
        v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} where
  toFun v := ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
    (Finset.mem_sdiff.mp v.2).1⟩
  invFun v := ⟨v.1.1, Finset.mem_sdiff.mpr ⟨v.2, v.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def horizontalTailCommonIndexEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalIntegralPlace T ≃
      {v : V.CliffordGeneralSpinHorizontalIntegralPlace S //
        v.1 ∉ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} where
  toFun v := ⟨horizontalTailCommonPlace V S T hST v, v.2⟩
  invFun v := ⟨v.1.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def horizontalTailCommonLocalHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace T) :
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
        (horizontalTailCommonPlace V S T hST v) ≃ₜ
      V.padicCliffordGeneralSpinHorizontalIntegralSubgroup T v where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

private theorem horizontalTailCommonLocalHomeomorph_measurePreserving
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace T) :
    MeasurePreserving
      (horizontalTailCommonLocalHomeomorph V S T hST v)
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
        (horizontalTailCommonPlace V S T hST v))
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure T v) := by
  let e := horizontalTailCommonLocalHomeomorph V S T hST v
  let jT := (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup T v).subtype
  have hjT : MeasurableEmbedding jT :=
    (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup T v)
      |>.isOpenEmbedding_subtypeVal.measurableEmbedding
  refine ⟨e.measurable, ?_⟩
  apply hjT.map_injective
  rw [Measure.map_map hjT.measurable e.measurable]
  change
    Measure.map
        (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
          (horizontalTailCommonPlace V S T hST v)).subtype
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
          (horizontalTailCommonPlace V S T hST v)) =
      Measure.map jT
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure T v)
  rw [V.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
      (horizontalTailCommonPlace V S T hST v),
    V.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure T v]
  rfl

theorem cliffordGeneralSpinHorizontalExceptionalProductMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure T) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
        (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T) := by
  let p : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} → Prop :=
    fun v ↦ v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S
  let oldReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
      V.HeightOnePadicCliffordGeneralSpinGroup v.1)
    (horizontalExceptionalOldIndexEquiv V S T hST).symm
  let newReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
        V.HeightOnePadicCliffordGeneralSpinGroup v.1)
    (horizontalExceptionalNewIndexEquiv V S T).symm
  have hPart := measurePreserving_piEquivPiSubtypeProd
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} ↦
      V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1) p
  have hOld := measurePreserving_piCongrLeft
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
      V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1)
    (horizontalExceptionalOldIndexEquiv V S T hST).symm
  have hNew := measurePreserving_piCongrLeft
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1)
    (horizontalExceptionalNewIndexEquiv V S T).symm
  have hCombined := (hOld.prod hNew).comp hPart
  have hfun :
      (Prod.map oldReindex newReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T} ↦
              V.HeightOnePadicCliffordGeneralSpinGroup v.1) p) =
        V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST := by
    funext g
    apply Prod.ext <;> funext v <;> rfl
  simpa only [cliffordGeneralSpinHorizontalExceptionalProductMeasure,
    cliffordGeneralSpinHorizontalNewExceptionalProductMeasure, hfun] using
      hCombined.map_eq

theorem cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_map_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) =
      (V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability S v
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace T) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure T v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability T v
  let p : V.CliffordGeneralSpinHorizontalIntegralPlace S → Prop :=
    fun v ↦ v.1 ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T
  let newReindex := MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
        V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
          ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩)
    (horizontalTailNewIndexEquiv V S T).symm
  let commonIndexReindex := MeasurableEquiv.piCongrLeft
    (fun v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
      V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
        (horizontalTailCommonPlace V S T hST v))
    (horizontalTailCommonIndexEquiv V S T hST).symm
  let commonFiberReindex := MeasurableEquiv.piCongrRight fun
    v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
      (horizontalTailCommonLocalHomeomorph V S T hST v).toMeasurableEquiv
  let commonReindex := commonIndexReindex.trans commonFiberReindex
  have hPart := measurePreserving_horizontalInfinitePiEquivPiSubtypeProd
    (fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) p
  have hNew :
      MeasurePreserving newReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
              S v.1)
        (V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T) := by
    refine ⟨newReindex.measurable, ?_⟩
    simpa only [cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure,
      Measure.infinitePi_eq_pi] using
        (Measure.infinitePi_map_piCongrLeft
          (fun v : {v // v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T \
            V.cliffordGeneralSpinHorizontalExceptionalPlaces S} ↦
              V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
                ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩)
          (horizontalTailNewIndexEquiv V S T).symm)
  have hCommonIndex :
      MeasurePreserving commonIndexReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1)
        (Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
              (horizontalTailCommonPlace V S T hST v)) := by
    refine ⟨commonIndexReindex.measurable, ?_⟩
    simpa only [commonIndexReindex] using
      (Measure.infinitePi_map_piCongrLeft
        (fun v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
            (horizontalTailCommonPlace V S T hST v))
        (horizontalTailCommonIndexEquiv V S T hST).symm)
  have hCommonFiber :
      MeasurePreserving commonFiberReindex
        (Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
              (horizontalTailCommonPlace V S T hST v))
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) := by
    refine ⟨commonFiberReindex.measurable, ?_⟩
    unfold cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
    change
      Measure.map
          (fun g v ↦ horizontalTailCommonLocalHomeomorph V S T hST v (g v))
          (Measure.infinitePi fun
            v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
              V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
                (horizontalTailCommonPlace V S T hST v)) =
        Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure T v
    rw [Measure.infinitePi_map_pi
      (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace T ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
          (horizontalTailCommonPlace V S T hST v))
      (f := fun v g ↦ horizontalTailCommonLocalHomeomorph V S T hST v g)
      (fun v ↦ (horizontalTailCommonLocalHomeomorph V S T hST v).measurable)]
    congr 1
    funext v
    exact (horizontalTailCommonLocalHomeomorph_measurePreserving V S T hST v).map_eq
  have hCommon :
      MeasurePreserving commonReindex
        (Measure.infinitePi fun
          v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
            V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1)
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) :=
    hCommonFiber.comp hCommonIndex
  letI : SFinite
      (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  letI : SFinite
      (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) := by
    letI : IsProbabilityMeasure
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      inferInstance
    letI : IsFiniteMeasure
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    letI : SigmaFinite
        (Measure.infinitePi fun v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1) :=
      IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hCombined := (MeasurePreserving.prod
    (μa := Measure.infinitePi fun
      v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // p v} ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1)
    (μc := Measure.infinitePi fun
      v : {v : V.CliffordGeneralSpinHorizontalIntegralPlace S // ¬ p v} ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v.1)
    hNew hCommon).comp hPart
  have hfun :
      (Prod.map newReindex commonReindex) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd
            (fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
              V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) p) =
        V.cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph S T hST := by
    funext g
    apply Prod.ext <;> funext v <;> rfl
  simpa only [cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure, hfun]
    using hCombined.map_eq

/-! ## Nested source comparison -/

private theorem horizontalComapProdMap
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    {f : α → β} {g : γ → δ}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure β) (ν : Measure δ)
    [SigmaFinite μ] [SigmaFinite ν]
    [SigmaFinite (μ.comap f)] [SigmaFinite (ν.comap g)] :
    (μ.prod ν).comap (Prod.map f g) =
      (μ.comap f).prod (ν.comap g) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [(hf.prodMap hg).comap_apply, Set.prodMap_image_prod,
    Measure.prod_prod, hf.comap_apply, hg.comap_apply]

private theorem horizontalComapIdProdMapId
    {γ δ ε ζ : Type*}
    [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSpace ε] [MeasurableSpace ζ]
    {f : γ → δ} (hf : MeasurableEmbedding f)
    (μ : Measure ε) (ν : Measure δ) (κ : Measure ζ)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    [SigmaFinite (ν.comap f)] :
    (μ.prod (ν.prod κ)).comap
        (Prod.map (fun x ↦ x) (Prod.map f (fun x ↦ x))) =
      μ.prod ((ν.comap f).prod κ) := by
  have hμ : MeasurableEmbedding (fun x : ε ↦ x) := MeasurableEmbedding.id
  have hκ : MeasurableEmbedding (fun x : ζ ↦ x) := MeasurableEmbedding.id
  letI : SigmaFinite (κ.comap (fun x ↦ x)) := by rw [Measure.comap_id]; infer_instance
  letI : SigmaFinite (μ.comap (fun x ↦ x)) := by rw [Measure.comap_id]; infer_instance
  letI : SigmaFinite ((ν.prod κ).comap (Prod.map f (fun x ↦ x))) := by
    rw [horizontalComapProdMap hf hκ, Measure.comap_id]
    infer_instance
  rw [horizontalComapProdMap hμ (hf.prodMap hκ), Measure.comap_id,
    horizontalComapProdMap hf hκ, Measure.comap_id]

/-- Split the larger source into old exceptional, new unrestricted, and
common-tail coordinates. -/
def cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct T ×
      V.CliffordGeneralSpinHorizontalIntegralTail T) ≃ₜ
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T)) :=
  (Homeomorph.prodCongr
    (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST)
    (Homeomorph.refl _)).trans (Homeomorph.prodAssoc _ _ _)

/-- Split the smaller source into old exceptional, new integral, and
common-tail coordinates. -/
def cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) ≃ₜ
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T)) :=
  Homeomorph.prodCongr (Homeomorph.refl _)
    (V.cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph S T hST)

/-- The literal nested inclusion fixes the old exceptional coordinates and
common tail, and includes only the new integral coordinates. -/
def cliffordGeneralSpinHorizontalTransitionSourceInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (V.CliffordGeneralSpinHorizontalNewIntegralProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T)) →
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T ×
        V.CliffordGeneralSpinHorizontalIntegralTail T)) :=
  Prod.map (fun g ↦ g)
    (Prod.map
      (V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion S T)
      (fun g ↦ g))

theorem cliffordGeneralSpinHorizontalTransitionSourceInclusion_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalTransitionSourceInclusion S T) := by
  exact MeasurableEmbedding.id.prodMap
    ((V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion_measurableEmbedding
      S T).prodMap MeasurableEmbedding.id)

/-- The transition map on the direct source coordinates, obtained only by
splitting, including the new integral coordinates, and reassembling. -/
def cliffordGeneralSpinHorizontalTransitionSource
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) →
    (V.CliffordGeneralSpinHorizontalExceptionalProduct T ×
      V.CliffordGeneralSpinHorizontalIntegralTail T) :=
  (V.cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph S T hST).symm ∘
    V.cliffordGeneralSpinHorizontalTransitionSourceInclusion S T ∘
      V.cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph S T hST

theorem cliffordGeneralSpinHorizontalTransitionSource_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding (V.cliffordGeneralSpinHorizontalTransitionSource S T hST) :=
  (V.cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph S T hST).symm
    |>.measurableEmbedding.comp
      ((V.cliffordGeneralSpinHorizontalTransitionSourceInclusion_measurableEmbedding S T).comp
        (V.cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph S T hST
          |>.measurableEmbedding))

theorem cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_map_largerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
        ((V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure T) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  have hidTail :
      Measure.map (fun g ↦ g)
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) =
        V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T := Measure.map_id
  have hAssoc :
      Measure.map (Homeomorph.prodAssoc
          (V.CliffordGeneralSpinHorizontalExceptionalProduct S)
          (V.CliffordGeneralSpinHorizontalNewExceptionalProduct S T)
          (V.CliffordGeneralSpinHorizontalIntegralTail T))
        (((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
          (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T)).prod
            (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
        ((V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) := by
    exact Measure.prodAssoc_prod
  unfold cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph
    cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
  change Measure.map
    ((Homeomorph.prodAssoc _ _ _) ∘
      Prod.map
        (V.cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph S T hST)
        (fun g ↦ g)) _ = _
  rw [← Measure.map_map, ← Measure.map_prod_map,
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_map_transition S T hST,
    hidTail, hAssoc]
  all_goals fun_prop

theorem cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_map_smallerTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph S T hST)
        (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
        ((V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T).prod
          (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  have hid :
      Measure.map (Homeomorph.refl
          (V.CliffordGeneralSpinHorizontalExceptionalProduct S))
          (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) =
        V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S := Measure.map_id
  unfold cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph
    cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
  rw [Homeomorph.coe_prodCongr, ← Measure.map_prod_map, hid,
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_map_transition S T hST]
  all_goals fun_prop

theorem cliffordGeneralSpinHorizontalTransitionSourceProduct_comap
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
      ((V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T))).comap
        (V.cliffordGeneralSpinHorizontalTransitionSourceInclusion S T) =
      V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        ((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
          ((V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T).prod
            (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T))) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T) := inferInstance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewIntegralProductMeasure S T) := by
    unfold cliffordGeneralSpinHorizontalNewIntegralProductMeasure
    infer_instance
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T) := by
    unfold cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure
    infer_instance
  letI : SigmaFinite
      ((V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).comap
        (V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion S T)) := by
    rw [V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_comap_inclusion S T]
    infer_instance
  unfold cliffordGeneralSpinHorizontalTransitionSourceInclusion
  rw [horizontalComapIdProdMapId
      (V.cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion_measurableEmbedding
        S T)
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S)
      (V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T)
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T),
    V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure_comap_inclusion S T,
    V.cliffordGeneralSpinHorizontalNewIntegralProductMeasure_eq_transitionVolume_smul S T,
    Measure.prod_smul_left, Measure.prod_smul_right]

theorem cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T).comap
        (V.cliffordGeneralSpinHorizontalTransitionSource S T hST) =
      V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S := by
  let larger := V.cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph
    S T hST
  let smaller := V.cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph
    S T hST
  let coordinate := V.cliffordGeneralSpinHorizontalTransitionSource S T hST
  let inclusion := V.cliffordGeneralSpinHorizontalTransitionSourceInclusion S T
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.cliffordGeneralSpinHorizontalTransitionSource_measurableEmbedding S T hST
  have hInclusion : MeasurableEmbedding inclusion :=
    V.cliffordGeneralSpinHorizontalTransitionSourceInclusion_measurableEmbedding S T
  have hfun : larger ∘ coordinate = inclusion ∘ smaller := by
    funext g
    simp only [larger, coordinate,
      cliffordGeneralSpinHorizontalTransitionSource, Function.comp_apply]
    exact larger.apply_symm_apply _
  calc
    (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T).comap coordinate =
        ((Measure.map larger
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            larger).comap coordinate := by
      rw [larger.measurableEmbedding.comap_map]
    _ = (Measure.map larger
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            (larger ∘ coordinate) := by
      rw [Measure.comap_comap hCoordinate.measurableSet_image' larger.injective
        larger.measurableEmbedding.measurableSet_image']
    _ = (Measure.map larger
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            (inclusion ∘ smaller) := by rw [hfun]
    _ = ((Measure.map larger
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            inclusion).comap smaller := by
      rw [Measure.comap_comap smaller.measurableEmbedding.measurableSet_image'
        hInclusion.injective hInclusion.measurableSet_image']
    _ = (((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
          ((V.cliffordGeneralSpinHorizontalNewExceptionalProductMeasure S T).prod
            (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T))).comap
              inclusion).comap smaller := by
      rw [V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_map_largerTransition
        S T hST]
    _ = (V.cliffordGeneralSpinHorizontalTransitionVolume S T •
          ((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
            ((V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T).prod
              (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T)))).comap
                smaller := by
      rw [V.cliffordGeneralSpinHorizontalTransitionSourceProduct_comap S T]
    _ = V.cliffordGeneralSpinHorizontalTransitionVolume S T •
          (((V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
            ((V.cliffordGeneralSpinHorizontalNewNormalizedIntegralProductMeasure S T).prod
              (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure T))).comap
                smaller) := by rw [Measure.comap_smul]
    _ = V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S := by
      rw [← V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_map_smallerTransition
        S T hST, smaller.measurableEmbedding.comap_map]

/-! ## Actual restricted-family block cylinders -/

/-- Transition between the actual restricted-family principal blocks,
conjugated from the literal exceptional/tail coordinate inclusion. -/
def cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S →
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock T :=
  V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph T ∘
    V.cliffordGeneralSpinHorizontalTransitionSource S T hST ∘
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).symm

theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_measurableEmbedding
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST) :=
  (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph T
    |>.measurableEmbedding).comp
    ((V.cliffordGeneralSpinHorizontalTransitionSource_measurableEmbedding S T hST).comp
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
        |>.symm.measurableEmbedding))

/-- Exact unnormalized cylinder transition on the actual restricted-family
principal blocks. -/
theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure T).comap
        (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST) =
      V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S := by
  let sourceToBlockS :=
    V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
  let sourceToBlockT :=
    V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph T
  let embedding :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST
  let coordinate := V.cliffordGeneralSpinHorizontalTransitionSource S T hST
  have hEmbedding : MeasurableEmbedding embedding :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_measurableEmbedding
      S T hST
  have hCoordinate : MeasurableEmbedding coordinate :=
    V.cliffordGeneralSpinHorizontalTransitionSource_measurableEmbedding S T hST
  have hfun : embedding ∘ sourceToBlockS = sourceToBlockT ∘ coordinate := by
    funext g
    change sourceToBlockT (coordinate (sourceToBlockS.symm (sourceToBlockS g))) =
      sourceToBlockT (coordinate g)
    rw [sourceToBlockS.symm_apply_apply]
  unfold cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
  calc
    (Measure.map sourceToBlockT
        (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
          embedding =
      Measure.map sourceToBlockS
        (((Measure.map sourceToBlockT
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            embedding).comap sourceToBlockS) := by
      rw [sourceToBlockS.measurableEmbedding.map_comap,
        sourceToBlockS.surjective.range_eq, Measure.restrict_univ]
    _ = Measure.map sourceToBlockS
        ((Measure.map sourceToBlockT
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            (embedding ∘ sourceToBlockS)) := by
      rw [Measure.comap_comap sourceToBlockS.measurableEmbedding.measurableSet_image'
        hEmbedding.injective hEmbedding.measurableSet_image']
    _ = Measure.map sourceToBlockS
        ((Measure.map sourceToBlockT
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            (sourceToBlockT ∘ coordinate)) := by rw [hfun]
    _ = Measure.map sourceToBlockS
        (((Measure.map sourceToBlockT
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T)).comap
            sourceToBlockT).comap coordinate) := by
      rw [Measure.comap_comap hCoordinate.measurableSet_image'
        sourceToBlockT.injective sourceToBlockT.measurableEmbedding.measurableSet_image']
    _ = Measure.map sourceToBlockS
        ((V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure T).comap
          coordinate) := by
      rw [sourceToBlockT.measurableEmbedding.comap_map]
    _ = Measure.map sourceToBlockS
        (V.cliffordGeneralSpinHorizontalTransitionVolume S T •
          V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
      rw [V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_comap_transition
        S T hST]
    _ = V.cliffordGeneralSpinHorizontalTransitionVolume S T •
        Measure.map sourceToBlockS
          (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
      rw [Measure.map_smul]

/-- Reciprocal-volume normalization makes the actual block-cylinder
transition strictly coherent.  The reciprocal is only a finite product; no
Euler-product scale is introduced. -/
theorem
    cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_reciprocal_comap_transition
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    (V.cliffordGeneralSpinHorizontalTransitionVolume S T)⁻¹ •
        ((V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure T).comap
          (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition S T hST)) =
      V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S := by
  rw [V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_comap_transition
    S T hST, ← smul_assoc]
  simp only [smul_eq_mul]
  rw [ENNReal.inv_mul_cancel
    (V.cliffordGeneralSpinHorizontalTransitionVolume_ne_zero S T)
    (V.cliffordGeneralSpinHorizontalTransitionVolume_ne_top S T), one_smul]

end RationalQuadraticSpaceMatrix
