import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockCylinderMeasure

/-!
# Transition coordinates and scalars for mixed finite-adelic principal blocks

For finite exceptional sets `S ⊆ T`, this module splits the direct product
coordinates used by the two mixed principal blocks:

* the `T`-exceptional product is the product of the old `S`-exceptional
  coordinates and the new coordinates in `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`; and
* the `S`-integral tail is the product of the new integral coordinates in
  `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)` and the common integral tail outside `T`.

Both splittings are continuous multiplicative equivalences for the displayed
product topologies.  On the new finite coordinate set, the product of the
comapped, unnormalized integral measures is exactly the product of their
literal integral volumes times the product of the normalized probabilities.

No topology or measure is transported through the restricted-family block
equivalence, and no global finite-adelic measure is constructed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance cliffordSpinCandidateMixedPrincipalBlockTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateMixedPrincipalBlockTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinCandidateMixedPrincipalBlockTransitionGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinCandidateMixedPrincipalBlockTransitionGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

/-- Normalizing the exceptional set is monotone in the user-supplied finite
set.  The fixed multiplication and identity-coordinate bad places are present
on both sides. -/
theorem cliffordSpinCandidateAdmissibleExceptionalPlaces_mono
    (V : RationalQuadraticSpaceMatrix n)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) :
    V.cliffordSpinCandidateAdmissibleExceptionalPlaces S ⊆
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces T := by
  intro v hv
  simp only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
    Finset.mem_union] at hv ⊢
  exact hv.elim (fun h => Or.inl (hST h)) Or.inr

/-! ## Direct transition coordinate carriers -/

/-- The finite product of the new unrestricted local coordinates in `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) →
    V.HeightOnePadicCliffordSpinCandidateGroup v.1

/-- The finite product of the new integral local coordinates in `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) →
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
      ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- Split the `T`-exceptional coordinates into the old `S` coordinates and
the new coordinates in `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T :=
  fun g =>
    (fun v => g ⟨v.1,
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST v.2⟩,
      fun v => g ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)

/-- Reassemble the old and new exceptional coordinates into the
`T`-exceptional product. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T :=
  fun g v =>
    if hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S then
      g.1 ⟨v.1, hv⟩
    else
      g.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩

/-- The exceptional transition splitting is a multiplicative equivalence. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T ≃*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T where
  toFun := V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit S T hST
  invFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    by_cases hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble]
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).2
      simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl

@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv_fst_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T)
    (v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv S T hST g).1
        v =
      g ⟨v.1,
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST v.2⟩ :=
  rfl

@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv_snd_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T)
    (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv S T hST g).2
        v =
      g ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ :=
  rfl

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv_symm_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T)
    (v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T})
    (hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv
        S T hST).symm g v =
      g.1 ⟨v.1, hv⟩ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv_symm_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T)
    (v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T})
    (hv : v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv
        S T hST).symm g v =
      g.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit S T hST) := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit
  fun_prop

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble S T hST) := by
  apply continuous_pi
  intro v
  by_cases hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
  · simpa [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]
      using
        (continuous_apply (⟨v.1, hv⟩ : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S})).comp continuous_fst
  · simpa [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble, hv]
      using
        (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ :
            {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)})).comp continuous_snd

/-- The exceptional transition splitting is a homeomorphism for the displayed
finite product topologies. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T ≃ₜ
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T where
  toEquiv :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv S T hST
  continuous_toFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit
      V S T hST
  continuous_invFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionAssemble
      V S T hST

/-- The strongest direct exceptional-coordinate transition equivalence. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct T ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionHomeomorph S T hST)
    (by
      intro g k
      change
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit S T hST
            (g * k) =
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit S T hST
              g *
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionSplit S T hST
              k
      exact
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTransitionMulEquiv
          S T hST).map_mul g k)

/-! ## The integral-tail transition -/

/-- Split the `S`-integral tail into the new integral coordinates in `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`
and the common integral tail outside `T`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T :=
  fun g =>
    (fun v => g ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
      fun v =>
        let w : V.CliffordSpinCandidateAdmissibleIntegralPlace S :=
          ⟨v.1, fun hv =>
            v.2
              (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)⟩
        ⟨(g w).1, fun _ => (g w).2 w.2⟩)

/-- Reassemble the new integral coordinates and common tail into the
`S`-integral tail. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T) →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S :=
  fun g v =>
    if hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T then
      let w : {v // v ∈
          (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} :=
        ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
      ⟨(g.1 w).1, fun _ => (g.1 w).2 v.2⟩
    else
      let w : V.CliffordSpinCandidateAdmissibleIntegralPlace T := ⟨v.1, hv⟩
      ⟨(g.2 w).1, fun _ => (g.2 w).2 hv⟩

/-- The integral-tail transition splitting is a multiplicative equivalence. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S ≃*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T where
  toFun := V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit S T hST
  invFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    by_cases hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble, hv]
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble, hv]
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).1
      simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble, hv]
    · funext v
      simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit,
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble, v.2]
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl

@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv_fst_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv S T hST g).1
        v =
      g ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ :=
  rfl

@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv_snd_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv S T hST g).2
        v =
      ⟨(g ⟨v.1, fun hv =>
          v.2
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)⟩).1,
        fun _ =>
          (g ⟨v.1, fun hv =>
            v.2
              (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv)⟩).2
            (fun hv =>
              v.2
                (V.cliffordSpinCandidateAdmissibleExceptionalPlaces_mono hST hv))⟩ :=
  rfl

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv_symm_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
        S T hST).symm g v =
      ⟨(g.1 ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩).1,
        fun _ =>
          (g.1 ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩).2 v.2⟩ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble,
    hv]

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv_symm_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
        S T hST).symm g v =
      ⟨(g.2 ⟨v.1, hv⟩).1, fun _ => (g.2 ⟨v.1, hv⟩).2 hv⟩ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble,
    hv]

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit S T hST) := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit
  fun_prop

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble
        S T hST) := by
  apply continuous_pi
  intro v
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble
  by_cases hv : v.1 ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces T
  · simp only [dif_pos hv]
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp
        ((continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩ :
            {v // v ∈
              (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
                (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)})).comp
          continuous_fst))
  · simp only [dif_neg hv]
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp
        ((continuous_apply
          (⟨v.1, hv⟩ : V.CliffordSpinCandidateAdmissibleIntegralPlace T)).comp
          continuous_snd))

/-- The integral-tail transition splitting is a homeomorphism for the
displayed product topologies. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S ≃ₜ
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T where
  toEquiv :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv S T hST
  continuous_toFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit
      V S T hST
  continuous_invFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionAssemble
      V S T hST

/-- The strongest direct integral-tail transition equivalence. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionHomeomorph S T hST)
    (by
      intro g k
      change
        V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit S T hST
            (g * k) =
          V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit S T hST
              g *
            V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionSplit S T hST
              k
      exact
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailTransitionMulEquiv
          S T hST).map_mul g k)

/-! ## The exact new-coordinate transition scalar -/

/-- The literal product of integral-factor volumes on the new coordinates
`(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)},
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1

/-- The transition volume is also the literal double finite-set product
displayed in the block-transition formula. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_prod_sdiff
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T =
      ∏ v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S),
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume
  exact
    (Finset.prod_subtype ((V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)) (fun _ => Iff.rfl)
      (fun v =>
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)).symm

/-- The finite product of the comapped, unnormalized differential measures
on the new integral coordinates. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  Measure.pi fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} ↦
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
      S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- The finite product of normalized integral-factor probabilities on the
new coordinates. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  Measure.pi fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} ↦
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- Before taking products, each comapped integral measure is its literal
volume times the normalized probability measure. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralLocalFactorMeasure_eq_volume_smul_normalized
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ =
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 •
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ :=
  V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_volume_smul_normalized
    S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩

/-- Exact finite-coordinate transition formula: the product of unnormalized
comapped integral measures is the literal transition-volume product times the
product of normalized probabilities. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure_eq_transitionVolume_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure S T =
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
        V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
          S T := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure
    finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
    finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume
  letI (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
      SigmaFinite
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  letI (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
      SigmaFinite
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply]
  rw [Measure.pi_pi _ s]
  simp only [smul_eq_mul]
  simp_rw [
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralLocalFactorMeasure_eq_volume_smul_normalized
      S T,
    Measure.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib.symm

end RationalQuadraticSpaceMatrix
