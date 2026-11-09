import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockCylinderMeasure

/-!
# Transition coordinates and scalars for mixed finite-adelic principal blocks

For finite exceptional sets `S ⊆ T`, this module splits the direct product
coordinates used by the two mixed principal blocks:

* the `T`-exceptional product is the product of the old `S`-exceptional
  coordinates and the new coordinates in `T \ S`; and
* the `S`-integral tail is the product of the new integral coordinates in
  `T \ S` and the common integral tail outside `T`.

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

local instance mixedPrincipalBlockTransitionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance mixedPrincipalBlockTransitionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockTransitionGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockTransitionGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

/-! ## Direct transition coordinate carriers -/

/-- The finite product of the new unrestricted local coordinates in `T \ S`. -/
abbrev FiniteAdelicSpecialOrthogonalNewExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ T \ S}) →
    V.HeightOnePadicSpecialOrthogonalGroup v.1

/-- The finite product of the new integral local coordinates in `T \ S`. -/
abbrev FiniteAdelicSpecialOrthogonalNewIntegralProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ T \ S}) →
    V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1

/-- Split the `T`-exceptional coordinates into the old `S` coordinates and
the new coordinates in `T \ S`. -/
def finiteAdelicSpecialOrthogonalExceptionalTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalExceptionalProduct T →
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T :=
  fun g =>
    (fun v => g ⟨v.1, hST v.2⟩,
      fun v => g ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)

/-- Reassemble the old and new exceptional coordinates into the
`T`-exceptional product. -/
def finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) →
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct T :=
  fun g v =>
    if hv : v.1 ∈ S then
      g.1 ⟨v.1, hv⟩
    else
      g.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩

/-- The exceptional transition splitting is a multiplicative equivalence. -/
def finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalExceptionalProduct T ≃*
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T where
  toFun := V.finiteAdelicSpecialOrthogonalExceptionalTransitionSplit S T hST
  invFun :=
    V.finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    by_cases hv : v.1 ∈ S
    · simp [finiteAdelicSpecialOrthogonalExceptionalTransitionSplit,
        finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]
    · simp [finiteAdelicSpecialOrthogonalExceptionalTransitionSplit,
        finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      simp [finiteAdelicSpecialOrthogonalExceptionalTransitionSplit,
        finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble]
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).2
      simp [finiteAdelicSpecialOrthogonalExceptionalTransitionSplit,
        finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv_fst_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicSpecialOrthogonalExceptionalProduct T)
    (v : {v // v ∈ S}) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv S T hST g).1
        v =
      g ⟨v.1, hST v.2⟩ :=
  rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv_snd_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicSpecialOrthogonalExceptionalProduct T)
    (v : {v // v ∈ T \ S}) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv S T hST g).2
        v =
      g ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ :=
  rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv_symm_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T)
    (v : {v // v ∈ T})
    (hv : v.1 ∈ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv
        S T hST).symm g v =
      g.1 ⟨v.1, hv⟩ := by
  simp [finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv,
    finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]

@[simp]
theorem
    finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv_symm_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T)
    (v : {v // v ∈ T})
    (hv : v.1 ∉ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv
        S T hST).symm g v =
      g.2 ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ := by
  simp [finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv,
    finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]

private theorem
    continuous_finiteAdelicSpecialOrthogonalExceptionalTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalExceptionalTransitionSplit S T hST) := by
  unfold finiteAdelicSpecialOrthogonalExceptionalTransitionSplit
  fun_prop

private theorem
    continuous_finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble S T hST) := by
  apply continuous_pi
  intro v
  by_cases hv : v.1 ∈ S
  · simpa [finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]
      using
        (continuous_apply (⟨v.1, hv⟩ : {v // v ∈ S})).comp continuous_fst
  · simpa [finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble, hv]
      using
        (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ :
            {v // v ∈ T \ S})).comp continuous_snd

/-- The exceptional transition splitting is a homeomorphism for the displayed
finite product topologies. -/
def finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalExceptionalProduct T ≃ₜ
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T where
  toEquiv :=
    V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv S T hST
  continuous_toFun :=
    continuous_finiteAdelicSpecialOrthogonalExceptionalTransitionSplit
      V S T hST
  continuous_invFun :=
    continuous_finiteAdelicSpecialOrthogonalExceptionalTransitionAssemble
      V S T hST

/-- The strongest direct exceptional-coordinate transition equivalence. -/
def finiteAdelicSpecialOrthogonalExceptionalTransitionContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalExceptionalProduct T ≃ₜ*
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicSpecialOrthogonalExceptionalTransitionHomeomorph S T hST)
    (by
      intro g k
      change
        V.finiteAdelicSpecialOrthogonalExceptionalTransitionSplit S T hST
            (g * k) =
          V.finiteAdelicSpecialOrthogonalExceptionalTransitionSplit S T hST
              g *
            V.finiteAdelicSpecialOrthogonalExceptionalTransitionSplit S T hST
              k
      exact
        (V.finiteAdelicSpecialOrthogonalExceptionalTransitionMulEquiv
          S T hST).map_mul g k)

/-! ## The integral-tail transition -/

/-- Split the `S`-integral tail into the new integral coordinates in `T \ S`
and the common integral tail outside `T`. -/
def finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalIntegralTail S →
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T :=
  fun g =>
    (fun v => g ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩,
      fun v => g ⟨v.1, fun hv => v.2 (hST hv)⟩)

/-- Reassemble the new integral coordinates and common tail into the
`S`-integral tail. -/
def finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (_hST : S ⊆ T) :
    (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T) →
      V.FiniteAdelicSpecialOrthogonalIntegralTail S :=
  fun g v =>
    if hv : v.1 ∈ T then
      g.1 ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩
    else
      g.2 ⟨v.1, hv⟩

/-- The integral-tail transition splitting is a multiplicative equivalence. -/
def finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalIntegralTail S ≃*
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T where
  toFun := V.finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit S T hST
  invFun :=
    V.finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble S T hST
  left_inv := by
    intro g
    funext v
    by_cases hv : v.1 ∈ T
    · simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit,
        finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]
    · simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit,
        finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]
  right_inv := by
    intro g
    apply Prod.ext
    · funext v
      have hv := (Finset.mem_sdiff.mp v.2).1
      simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit,
        finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]
    · funext v
      simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit,
        finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, v.2]
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv_fst_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : {v // v ∈ T \ S}) :
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv S T hST g).1
        v =
      g ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩ :=
  rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv_snd_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : {v // v ∉ T}) :
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv S T hST g).2
        v =
      g ⟨v.1, fun hv => v.2 (hST hv)⟩ :=
  rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv_symm_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T)
    (v : {v // v ∉ S})
    (hv : v.1 ∈ T) :
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
        S T hST).symm g v =
      g.1 ⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩ := by
  simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv,
    finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]

@[simp]
theorem
    finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv_symm_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g :
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T)
    (v : {v // v ∉ S})
    (hv : v.1 ∉ T) :
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
        S T hST).symm g v =
      g.2 ⟨v.1, hv⟩ := by
  simp [finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv,
    finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]

private theorem
    continuous_finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit S T hST) := by
  unfold finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit
  fun_prop

private theorem
    continuous_finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble
        S T hST) := by
  apply continuous_pi
  intro v
  by_cases hv : v.1 ∈ T
  · simpa [finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]
      using
        (continuous_apply
          (⟨v.1, Finset.mem_sdiff.mpr ⟨hv, v.2⟩⟩ :
            {v // v ∈ T \ S})).comp continuous_fst
  · simpa [finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble, hv]
      using
        (continuous_apply (⟨v.1, hv⟩ : {v // v ∉ T})).comp continuous_snd

/-- The integral-tail transition splitting is a homeomorphism for the
displayed product topologies. -/
def finiteAdelicSpecialOrthogonalIntegralTailTransitionHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalIntegralTail S ≃ₜ
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T where
  toEquiv :=
    V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv S T hST
  continuous_toFun :=
    continuous_finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit
      V S T hST
  continuous_invFun :=
    continuous_finiteAdelicSpecialOrthogonalIntegralTailTransitionAssemble
      V S T hST

/-- The strongest direct integral-tail transition equivalence. -/
def finiteAdelicSpecialOrthogonalIntegralTailTransitionContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.FiniteAdelicSpecialOrthogonalIntegralTail S ≃ₜ*
      V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail T :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionHomeomorph S T hST)
    (by
      intro g k
      change
        V.finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit S T hST
            (g * k) =
          V.finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit S T hST
              g *
            V.finiteAdelicSpecialOrthogonalIntegralTailTransitionSplit S T hST
              k
      exact
        (V.finiteAdelicSpecialOrthogonalIntegralTailTransitionMulEquiv
          S T hST).map_mul g k)

/-! ## The exact new-coordinate transition scalar -/

/-- The literal product of integral-factor volumes on the new coordinates
`T \ S`. -/
def finiteAdelicSpecialOrthogonalTransitionVolume
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  ∏ v : {v // v ∈ T \ S},
    V.heightOnePadicSpecialOrthogonalIntegralVolume v.1

/-- The transition volume is also the literal double finite-set product
displayed in the block-transition formula. -/
theorem finiteAdelicSpecialOrthogonalTransitionVolume_eq_prod_sdiff
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalTransitionVolume S T =
      ∏ v ∈ T \ S,
        V.heightOnePadicSpecialOrthogonalIntegralVolume v := by
  unfold finiteAdelicSpecialOrthogonalTransitionVolume
  exact
    (Finset.prod_subtype (T \ S) (fun _ => Iff.rfl)
      (fun v => V.heightOnePadicSpecialOrthogonalIntegralVolume v)).symm

/-- The finite product of the comapped, unnormalized differential measures
on the new integral coordinates. -/
def finiteAdelicSpecialOrthogonalNewIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  Measure.pi fun v : {v // v ∈ T \ S} ↦
    V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1

/-- The finite product of normalized integral-factor probabilities on the
new coordinates. -/
def finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  Measure.pi fun v : {v // v ∈ T \ S} ↦
    V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1

/-- Before taking products, each comapped integral measure is its literal
volume times the normalized probability measure. -/
theorem heightOnePadicSpecialOrthogonalIntegralMeasure_eq_volume_smul_normalized
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.heightOnePadicSpecialOrthogonalIntegralMeasure v =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v •
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v := by
  rw [heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure, ← smul_assoc]
  simp only [smul_eq_mul]
  rw [ENNReal.mul_inv_cancel
    (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v)
    (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v), one_smul]

/-- Exact finite-coordinate transition formula: the product of unnormalized
comapped integral measures is the literal transition-volume product times the
product of normalized probabilities. -/
theorem
    finiteAdelicSpecialOrthogonalNewIntegralProductMeasure_eq_transitionVolume_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicSpecialOrthogonalNewIntegralProductMeasure S T =
      V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
        V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
          S T := by
  unfold
    finiteAdelicSpecialOrthogonalNewIntegralProductMeasure
    finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
    finiteAdelicSpecialOrthogonalTransitionVolume
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite
        (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply]
  rw [Measure.pi_pi _ s]
  simp only [smul_eq_mul]
  simp_rw [
    V.heightOnePadicSpecialOrthogonalIntegralMeasure_eq_volume_smul_normalized,
    Measure.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib.symm

end RationalQuadraticSpaceMatrix
