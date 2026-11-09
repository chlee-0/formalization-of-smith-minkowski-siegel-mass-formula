import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalTailMeasure
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicRestrictedFamily

/-!
# Horizontal GSpin principal blocks in the restricted-family carrier

For a finite exceptional set `S`, the horizontal source is the product of the
unrestricted local `GSpin` groups at
`S ∪ cliffordGeneralSpinHorizontalIntegralBadPlaces` and the compact-open
integral subgroups elsewhere.  This file identifies that source directly with
the corresponding fixed principal block inside the cofinally integral local
`GSpin` restricted family.

Both directions are continuous for the inherited restricted-family topology:
assembly is coordinatewise exceptional/tail case splitting, while extraction
is ordinary coordinate evaluation.  Transporting the exceptional/tail source
measure through this homeomorphism gives the first horizontal cylinder on the
restricted-family carrier with its exact source recovery and total mass.

No inverse continuity or measurability is asserted for the later algebraic
equivalence between the complete restricted family and the intrinsic
finite-adelic `GSpin` group.  No transition identity between two exceptional
sets, adelic Haar scalar, quotient measure, or disintegration is proved here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance horizontalRestrictedPrincipalDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalRestrictedPrincipalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalRestrictedPrincipalGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalRestrictedPrincipalGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance horizontalRestrictedPrincipalIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalRestrictedPrincipalIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalRestrictedPrincipalExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedPrincipalExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalRestrictedPrincipalTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalRestrictedPrincipalTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

/-! ## Fixed block inside the restricted family -/

/-- A cofinally integral local `GSpin` family whose only allowed
nonintegral places lie in the displayed horizontal exceptional set. -/
def IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily) : Prop :=
  ∀ v, v ∉ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces →
    V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 (g.1 v)

/-- The fixed horizontal principal block in the actual cofinally integral
local-family carrier. -/
abbrev CliffordGeneralSpinHorizontalRestrictedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily //
    V.IsCliffordGeneralSpinHorizontalPrincipalRestrictedFamily S g}

/-! ## Exceptional/tail assembly and extraction -/

/-- Assemble exceptional and normalized-tail coordinates into the fixed
restricted-family principal block. -/
def cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) →
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  fun g ↦ by
    let family : V.HeightOnePadicCliffordGeneralSpinGroupProduct :=
      fun v ↦
        if hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then
          g.1 ⟨v, hv⟩
        else
          (g.2 ⟨v, hv⟩).1
    have hrestricted :
        V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily family :=
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
        |>.eventually_cofinite_notMem.mono fun v hv ↦ by
          have hv' : ¬ (v ∈ S ∨
              v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
            simpa using hv
          have hgood : V.PadicCliffordGeneralSpinIsIntegral
              (Rat.HeightOneSpectrum.primesEquiv v).1
              (g.2 ⟨v, hv⟩).1 :=
            (V.mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff
              S ⟨v, hv⟩ (g.2 ⟨v, hv⟩).1).1 (g.2 ⟨v, hv⟩).2
          change V.PadicCliffordGeneralSpinIsIntegral
            (Rat.HeightOneSpectrum.primesEquiv v).1 (family v)
          rw [show family v = (g.2 ⟨v, hv⟩).1 by simp [family, hv']]
          exact hgood
    refine ⟨⟨family, hrestricted⟩, ?_⟩
    intro v hv
    have hv' : ¬ (v ∈ S ∨
        v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
      simpa using hv
    have hgood : V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v).1
        (g.2 ⟨v, hv⟩).1 :=
      (V.mem_padicCliffordGeneralSpinHorizontalIntegralSubgroup_iff
        S ⟨v, hv⟩ (g.2 ⟨v, hv⟩).1).1 (g.2 ⟨v, hv⟩).2
    change V.PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 (family v)
    rw [show family v = (g.2 ⟨v, hv⟩).1 by simp [family, hv']]
    exact hgood

@[simp]
theorem
    cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
      S g).1.1 v = g.1 ⟨v, hv⟩ := by
  have hv' : v ∈ S ∨
      v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    simpa using hv
  change (if h : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then
      g.1 ⟨v, h⟩ else (g.2 ⟨v, h⟩).1) = g.1 ⟨v, hv⟩
  simp [hv']

@[simp]
theorem
    cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
      S g).1.1 v = (g.2 ⟨v, hv⟩).1 := by
  have hv' : ¬ (v ∈ S ∨
      v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
    simpa using hv
  change (if h : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then
      g.1 ⟨v, h⟩ else (g.2 ⟨v, h⟩).1) = (g.2 ⟨v, hv⟩).1
  simp [hv']

/-- Extract the finite exceptional coordinates and integral good tail from a
fixed restricted-family principal block. -/
def cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S →
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  fun g ↦
    (fun v ↦ g.1.1 v.1,
      fun v ↦ ⟨g.1.1 v.1, g.2 v.1 v.2⟩)

/-- The exceptional/tail source is algebraically equivalent to the fixed
restricted-family principal block. -/
def cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) ≃
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S where
  toFun :=
    V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock S
  invFun :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail S
  left_inv := by
    intro g
    apply Prod.ext
    · funext v
      exact
        V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
          S g v.1 v.2
    · funext v
      apply Subtype.ext
      exact
        V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
          S g v.1 v.2
  right_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    · exact
        V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
          S
          (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
            S g) v hv
    · simpa using
        V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
          S
          (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
            S g) v hv

/-- The fixed restricted-family block carries the exact group structure
transported by exceptional/tail assembly. -/
noncomputable instance cliffordGeneralSpinHorizontalRestrictedPrincipalBlockGroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Group (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :=
  Equiv.group
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockEquiv
      S).symm

/-- Exceptional/tail assembly is multiplicative for that exact transported
group law. -/
def cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) ≃*
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  (Equiv.mulEquiv
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockEquiv
      S).symm).symm

/-! ## Product-topology compatibility -/

private theorem
    continuous_cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
        S) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  · have hv' : v ∈ S ∨
        v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
      simpa using hv
    have hcoord : Continuous (fun
        g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
          V.CliffordGeneralSpinHorizontalIntegralTail S ↦
        g.1 ⟨v, hv⟩) :=
      (continuous_apply
        (⟨v, hv⟩ :
          {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}))
        |>.comp continuous_fst
    simpa [hv'] using hcoord
  · have hv' : ¬ (v ∈ S ∨
        v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
      simpa using hv
    have hcoord : Continuous (fun
        g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
          V.CliffordGeneralSpinHorizontalIntegralTail S ↦
        (g.2 ⟨v, hv⟩).1) :=
      continuous_subtype_val.comp
        ((continuous_apply
          (⟨v, hv⟩ : V.CliffordGeneralSpinHorizontalIntegralPlace S))
          |>.comp continuous_snd)
    simpa [hv'] using hcoord

private theorem
    continuous_cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
        S) := by
  apply Continuous.prodMk
  · exact continuous_pi fun v ↦
      (continuous_apply v.1).comp
        (continuous_subtype_val.comp continuous_subtype_val)
  · apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact (continuous_apply v.1).comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- Exceptional/tail assembly is a homeomorphism onto the fixed principal
block of the actual cofinally integral restricted-family carrier. -/
def cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) ≃ₜ
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S where
  toEquiv :=
    V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockEquiv S
  continuous_toFun :=
    continuous_cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
      V S
  continuous_invFun :=
    continuous_cliffordGeneralSpinHorizontalRestrictedPrincipalBlockToExceptionalTail
      V S

/-- The exact exceptional/tail splitting is simultaneously topological and
multiplicative. -/
def
    cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) ≃ₜ*
      V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S)
    (by
      intro g h
      change
        V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
            S (g * h) =
          V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
              S g *
            V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
              S h
      exact
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockMulEquiv
          S).map_mul g h)

/-- The transported principal-block multiplication is continuous for the
inherited restricted-family topology. -/
noncomputable instance
    cliffordGeneralSpinHorizontalRestrictedPrincipalBlockContinuousMul
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ContinuousMul
      (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) where
  continuous_mul := by
    let e :=
      V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
        S
    change Continuous (fun p :
        V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ×
          V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S ↦
      e (e.symm p.1 * e.symm p.2))
    exact e.continuous.comp
      ((e.symm.continuous.comp continuous_fst).mul
        (e.symm.continuous.comp continuous_snd))

/-! ## The first restricted-family horizontal cylinder -/

/-- Transport the direct exceptional/tail source measure to the fixed
principal block of the cofinally integral restricted family. -/
def cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :=
  Measure.map
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S)
    (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S)

/-- The first horizontal restricted-family cylinder is invariant under the
exact transported principal-block group law. -/
instance cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S) := by
  letI : Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_isMulLeftInvariant
      S
  unfold cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
  exact isMulLeftInvariant_map
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
      S |>.toMulHom)
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
      S |>.continuous.measurable)
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
      S |>.surjective)

/-- Pulling the restricted-family block measure back through the exact
exceptional/tail splitting recovers the literal source product. -/
theorem
    map_cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_homeomorph_symm
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S).symm
        (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S) =
      V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S := by
  unfold cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
  exact MeasurableEquiv.map_symm_map
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S |>.toMeasurableEquiv)

/-- The restricted-family principal-block cylinder has total mass equal to the
product of the exceptional local horizontal Haar total masses. -/
@[simp]
theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S Set.univ =
      ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1 Set.univ := by
  rw [cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure,
    Measure.map_apply
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
        S |>.continuous.measurable)
      MeasurableSet.univ]
  change V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S
    Set.univ = _
  exact
    V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_univ S

end RationalQuadraticSpaceMatrix
