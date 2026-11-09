import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization
import Mathlib.Probability.ProductMeasure

/-!
# Exceptional and integral-tail splitting of mixed principal blocks

For a finite set `S` of height-one places, the mixed principal-block carrier
has the full local special-orthogonal group at the places in `S` and the
integral local subgroup away from `S`.

This module splits that dependent product directly into:

* the finite exceptional product indexed by `{v // v ∈ S}`; and
* the integral tail indexed by `{v // v ∉ S}`.

The componentwise maps form a continuous multiplicative equivalence for the
displayed product topologies.  The integral tail carries the infinite product
of the normalized local invariant-differential probability measures.  Its
total mass and all finite-coordinate marginals are literal.

No measure is put on the exceptional product, no complete principal-block
cylinder measure is constructed, and no topology is transported through the
restricted-family block equivalence.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance mixedPrincipalBlockSplitDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance mixedPrincipalBlockSplitPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockSplitGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockSplitGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

/-! ## The exceptional and tail carriers -/

/-- The finite dependent product of unrestricted local groups at the places
in `S`. -/
abbrev FiniteAdelicSpecialOrthogonalExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    V.HeightOnePadicSpecialOrthogonalGroup v.1

/-- The dependent product of integral local factors away from `S`. -/
abbrev FiniteAdelicSpecialOrthogonalIntegralTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∉ S}) →
    V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1

/-- Assemble the exceptional and integral-tail components into the direct
mixed principal-block carrier. -/
def finiteAdelicSpecialOrthogonalExceptionalTailToMixed
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) →
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S :=
  fun g v =>
    if hv : v ∈ S then
      ⟨g.1 ⟨v, hv⟩, fun hnv => (hnv hv).elim⟩
    else
      ⟨(g.2 ⟨v, hv⟩).1, fun _ => (g.2 ⟨v, hv⟩).2⟩

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v).1 =
      g.1 ⟨v, hv⟩ := by
  simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v).1 =
      (g.2 ⟨v, hv⟩).1 := by
  simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]

/-- The direct exceptional/tail assembly is multiplicative. -/
def finiteAdelicSpecialOrthogonalExceptionalTailToMixedHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) →*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toFun := V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S
  map_one' := by
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ S
    · simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]
    · simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]
  map_mul' := by
    intro g h
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ S
    · simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]
    · simp [finiteAdelicSpecialOrthogonalExceptionalTailToMixed, hv]

/-- Extract the exceptional and integral-tail components from the direct
mixed principal-block carrier. -/
def finiteAdelicSpecialOrthogonalMixedToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  fun g =>
    (fun v => (g v.1).1,
      fun v => ⟨(g v.1).1, (g v.1).2 v.2⟩)

/-- The direct exceptional/tail extraction is multiplicative. -/
def finiteAdelicSpecialOrthogonalMixedToExceptionalTailHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →*
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) where
  toFun := V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S
  map_one' := by
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl

/-- The displayed exceptional/tail product and the mixed principal block are
multiplicatively equivalent. -/
def finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) ≃*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toFun :=
    V.finiteAdelicSpecialOrthogonalExceptionalTailToMixedHom S
  invFun :=
    V.finiteAdelicSpecialOrthogonalMixedToExceptionalTailHom S
  left_inv := by
    intro g
    apply Prod.ext
    · funext v
      change
        (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v.1).1 =
          g.1 v
      exact
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_mem
          S g v.1 v.2
    · funext v
      apply Subtype.ext
      change
        (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v.1).1 =
          (g.2 v).1
      simpa using
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_notMem
          S g v.1 v.2
  right_inv := by
    intro g
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ S
    · change
        (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S
          (V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S g) v).1 =
            (g v).1
      simpa [finiteAdelicSpecialOrthogonalMixedToExceptionalTail] using
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_mem
          S (V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S g) v hv
    · change
        (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S
          (V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S g) v).1 =
            (g v).1
      simpa [finiteAdelicSpecialOrthogonalMixedToExceptionalTail] using
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_notMem
          S (V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S g) v hv
  map_mul' :=
    (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixedHom S).map_mul

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S g v).1 =
      g.1 ⟨v, hv⟩ := by
  exact
    V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_mem S g v hv

@[simp]
theorem finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g :
      V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S g v).1 =
      (g.2 ⟨v, hv⟩).1 := by
  exact
    V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_notMem S g v hv

@[simp]
theorem
    finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_symm_fst_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : {v // v ∈ S}) :
    ((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S).symm g).1
        v =
      (g v.1).1 :=
  by
    rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv_symm_snd_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : {v // v ∉ S}) :
    (((V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S).symm g).2
        v).1 =
      (g v.1).1 :=
  by
    rfl

/-! ## Direct product topology -/

private def finiteAdelicSpecialOrthogonalExceptionalCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) →
      V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v :=
  fun g => ⟨g.1 ⟨v, hv⟩, fun hnv => (hnv hv).elim⟩

private theorem continuous_finiteAdelicSpecialOrthogonalExceptionalCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
    Continuous
      (finiteAdelicSpecialOrthogonalExceptionalCoordinate V S v hv) := by
  apply
    (continuous_induced_rng
      (f := fun x :
          V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v =>
        (x : V.HeightOnePadicSpecialOrthogonalGroup v))
      (g :=
        finiteAdelicSpecialOrthogonalExceptionalCoordinate V S v hv)).2
  exact
    (continuous_apply
      (⟨v, hv⟩ : {v // v ∈ S})).comp continuous_fst

private def finiteAdelicSpecialOrthogonalIntegralTailCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) →
      V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v :=
  fun g => ⟨(g.2 ⟨v, hv⟩).1, fun _ => (g.2 ⟨v, hv⟩).2⟩

private theorem
    continuous_finiteAdelicSpecialOrthogonalIntegralTailCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    Continuous
      (finiteAdelicSpecialOrthogonalIntegralTailCoordinate V S v hv) := by
  apply
    (continuous_induced_rng
      (f := fun x :
          V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v =>
        (x : V.HeightOnePadicSpecialOrthogonalGroup v))
      (g :=
        finiteAdelicSpecialOrthogonalIntegralTailCoordinate V S v hv)).2
  have htail :
      Continuous (fun
          g : V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
            V.FiniteAdelicSpecialOrthogonalIntegralTail S =>
        g.2 (⟨v, hv⟩ : {v // v ∉ S})) :=
    (continuous_apply
      (⟨v, hv⟩ : {v // v ∉ S})).comp continuous_snd
  have hval :
      Continuous (fun
          g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v =>
        (g : V.HeightOnePadicSpecialOrthogonalGroup v)) :=
    continuous_subtype_val
  exact hval.comp htail

private theorem
    continuous_finiteAdelicSpecialOrthogonalExceptionalTailToMixed
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S) := by
  apply continuous_pi
  intro v
  by_cases hv : v ∈ S
  · have hfun :
        (fun g =>
          V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v) =
            finiteAdelicSpecialOrthogonalExceptionalCoordinate V S v hv := by
      funext g
      apply Subtype.ext
      exact
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_mem
          S g v hv
    rw [hfun]
    exact
      continuous_finiteAdelicSpecialOrthogonalExceptionalCoordinate
        V S v hv
  · have hfun :
        (fun g =>
          V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g v) =
            finiteAdelicSpecialOrthogonalIntegralTailCoordinate V S v hv := by
      funext g
      apply Subtype.ext
      exact
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed_apply_notMem
          S g v hv
    rw [hfun]
    exact
      continuous_finiteAdelicSpecialOrthogonalIntegralTailCoordinate
        V S v hv

private theorem
    continuous_finiteAdelicSpecialOrthogonalMixedToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalMixedToExceptionalTail S) := by
  exact Continuous.prodMk
    (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v.1))
    (continuous_pi fun v => by
      apply
        (continuous_induced_rng
          (f := fun x :
              V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 =>
            (x : V.HeightOnePadicSpecialOrthogonalGroup v.1))
          (g := fun
              g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
            ⟨(g v.1).1, (g v.1).2 v.2⟩)).2
      show Continuous (fun
          g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
        (g v.1).1)
      exact continuous_subtype_val.comp (continuous_apply v.1))

/-- The exceptional/tail splitting is a homeomorphism for the product
topologies carried directly by the displayed local factors. -/
def finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) ≃ₜ
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toEquiv :=
    V.finiteAdelicSpecialOrthogonalExceptionalTailMixedMulEquiv S
  continuous_toFun :=
    continuous_finiteAdelicSpecialOrthogonalExceptionalTailToMixed V S
  continuous_invFun :=
    continuous_finiteAdelicSpecialOrthogonalMixedToExceptionalTail V S

/-- The strongest direct carrier identification: the exceptional/tail split
is continuously multiplicative for the product topology, independently of
the unrestricted-family block subtype topology. -/
def finiteAdelicSpecialOrthogonalExceptionalTailMixedContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        V.FiniteAdelicSpecialOrthogonalIntegralTail S) ≃ₜ*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph S)
    (by
      intro g h
      change
        V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S (g * h) =
          V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S g *
            V.finiteAdelicSpecialOrthogonalExceptionalTailToMixed S h
      simpa only [
        finiteAdelicSpecialOrthogonalExceptionalTailToMixedHom] using
        (V.finiteAdelicSpecialOrthogonalExceptionalTailToMixedHom S).map_mul
          g h)

/-! ## The normalized integral-tail measure -/

/-- The infinite product of the normalized invariant-differential
probability measures on the integral factors away from `S`. -/
def finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Measure.infinitePi fun v : {v // v ∉ S} ↦
    V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1

/-- The normalized integral-tail product has total mass one. -/
instance
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
      V v.1
  unfold finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
  infer_instance

/-- Every finite-coordinate marginal of the normalized integral tail is the
finite product of the same normalized local factors. -/
theorem
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_map_restrict
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (T : Finset {v // v ∉ S}) :
    (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S).map
        T.restrict =
      Measure.pi fun v : {v // v ∈ T} ↦
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1.1 := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
      V v.1
  simpa only [
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure] using
      (Measure.infinitePi_map_restrict
        (μ := fun v : {v // v ∉ S} ↦
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
        (I := T))

/-- The normalized integral-tail product remains left invariant under
componentwise multiplication. -/
instance
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isProbability
      V v.1
  letI (v : {v // v ∉ S}) :
      Measure.IsMulLeftInvariant
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isMulLeftInvariant
      V v.1
  refine ⟨fun g ↦ ?_⟩
  unfold finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ g v * x v)
        (Measure.infinitePi fun v : {v // v ∉ S} ↦
          V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) =
      Measure.infinitePi fun v : {v // v ∉ S} ↦
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1
  rw [
    Measure.infinitePi_map_pi
      (μ := fun v : {v // v ∉ S} ↦
        V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
      (f := fun v x ↦ g v * x)
      (fun v ↦ measurable_const_mul (g v))]
  congr 1
  funext v
  exact map_mul_left_eq_self
    (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1)
    (g v)

end RationalQuadraticSpaceMatrix
