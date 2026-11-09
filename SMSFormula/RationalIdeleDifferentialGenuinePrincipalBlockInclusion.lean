import SMSFormula.RationalIdeleDifferentialGenuinePrincipalBlockMeasure

/-!
# Literal inclusion of differential rational-idele principal blocks

The direct exceptional/tail transition only changes which coordinates are
displayed as exceptional.  It preserves the underlying local unit at every
finite place.  Consequently its conjugate through the genuine fixed-block
homeomorphisms is the literal inclusion of the unchanged finite idele into a
larger principal block.

No ambient measure or directed gluing is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2400000

local instance rationalIdeleGenuineInclusionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleGenuineInclusionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Enlarging the exceptional set changes only the presentation of a direct
source point, not its local unit at any finite place. -/
theorem rationalIdeleDifferentialExceptionalTailTransition_localUnit
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (z : RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalIdeleDifferentialExceptionalTailLocalUnit T
        (rationalIdeleDifferentialExceptionalTailTransition S T hST z) v =
      rationalIdeleDifferentialExceptionalTailLocalUnit S z v := by
  by_cases hvS : v ∈ S
  · have hvT : v ∈ T := hST hvS
    simp [rationalIdeleDifferentialExceptionalTailTransition,
      rationalIdeleDifferentialLargerTransitionSourceHomeomorph,
      rationalIdeleDifferentialSmallerTransitionSourceHomeomorph,
      rationalIdeleDifferentialTransitionSourceInclusion,
      rationalIdeleDifferentialExceptionalTransitionHomeomorph,
      rationalIdeleDifferentialExceptionalTransitionAssemble,
      rationalIdeleDifferentialIntegralTailTransitionHomeomorph,
      rationalIdeleDifferentialIntegralTailTransitionSplit,
      rationalIdeleDifferentialExceptionalTailLocalUnit,
      Homeomorph.prodAssoc, hvS, hvT]
  · by_cases hvT : v ∈ T
    · simp [rationalIdeleDifferentialExceptionalTailTransition,
        rationalIdeleDifferentialLargerTransitionSourceHomeomorph,
        rationalIdeleDifferentialSmallerTransitionSourceHomeomorph,
        rationalIdeleDifferentialTransitionSourceInclusion,
        rationalIdeleDifferentialExceptionalTransitionHomeomorph,
        rationalIdeleDifferentialExceptionalTransitionAssemble,
        rationalIdeleDifferentialIntegralTailTransitionHomeomorph,
        rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialNewIntegralExceptionalInclusion,
        rationalIdeleDifferentialExceptionalTailLocalUnit,
        Homeomorph.prodAssoc, hvS, hvT]
    · simp [rationalIdeleDifferentialExceptionalTailTransition,
        rationalIdeleDifferentialLargerTransitionSourceHomeomorph,
        rationalIdeleDifferentialSmallerTransitionSourceHomeomorph,
        rationalIdeleDifferentialTransitionSourceInclusion,
        rationalIdeleDifferentialExceptionalTransitionHomeomorph,
        rationalIdeleDifferentialIntegralTailTransitionHomeomorph,
        rationalIdeleDifferentialIntegralTailTransitionSplit,
        rationalIdeleDifferentialExceptionalTailLocalUnit,
        Homeomorph.prodAssoc, hvS, hvT]
      congr 1

/-- Extracting the direct coordinates of a genuine block point keeps its local
unit unchanged. -/
theorem rationalIdeleDifferentialExceptionalTailLocalUnit_extract
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : RationalIdeleDifferentialGenuinePrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalIdeleDifferentialExceptionalTailLocalUnit S
        (rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S a) v =
      finiteAdelicUnitHeightOneComponentHom v a.1 := by
  by_cases hv : v ∈ S
  · simp [rationalIdeleDifferentialExceptionalTailLocalUnit,
      rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail, hv]
  · simp [rationalIdeleDifferentialExceptionalTailLocalUnit,
      rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail, hv]

/-- Literal inclusion of a genuine principal block into one with a larger
finite exceptional set.  The underlying finite idele is unchanged. -/
def rationalIdeleDifferentialGenuinePrincipalBlockInclusion
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    RationalIdeleDifferentialGenuinePrincipalBlock S →
      RationalIdeleDifferentialGenuinePrincipalBlock T :=
  fun a ↦ ⟨a.1, fun v hvT ↦ a.2 v (fun hvS ↦ hvT (hST hvS))⟩

@[simp]
theorem rationalIdeleDifferentialGenuinePrincipalBlockInclusion_val
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : RationalIdeleDifferentialGenuinePrincipalBlock S) :
    (rationalIdeleDifferentialGenuinePrincipalBlockInclusion S T hST a).1 =
      a.1 :=
  rfl

/-- The conjugated genuine transition preserves its underlying finite idele. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockTransition_val
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (a : RationalIdeleDifferentialGenuinePrincipalBlock S) :
    (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST a).1 =
      a.1 := by
  apply Units.ext
  ext v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
  change
    ((finiteAdelicUnitHeightOneComponentHom v
      (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST a).1 :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) =
      ((finiteAdelicUnitHeightOneComponentHom v a.1 :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
  rw [show finiteAdelicUnitHeightOneComponentHom v
      (rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST a).1 =
        rationalIdeleDifferentialExceptionalTailLocalUnit T
          (rationalIdeleDifferentialExceptionalTailTransition S T hST
            ((rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
              S).symm a)) v by
        exact exceptionalTailToGenuinePrincipalBlock_component T _ v]
  rw [rationalIdeleDifferentialExceptionalTailTransition_localUnit]
  rw [show
      (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph
        S).symm a =
        rationalIdeleDifferentialGenuinePrincipalBlockToExceptionalTail S a by
      rfl]
  exact congrArg Units.val
    (rationalIdeleDifferentialExceptionalTailLocalUnit_extract S a v)

/-- The conjugated transition is literally the unchanged-point block
inclusion. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockTransition_eq_inclusion
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    rationalIdeleDifferentialGenuinePrincipalBlockTransition S T hST =
      rationalIdeleDifferentialGenuinePrincipalBlockInclusion S T hST := by
  funext a
  apply Subtype.ext
  exact rationalIdeleDifferentialGenuinePrincipalBlockTransition_val S T hST a

end RationalQuadraticSpaceMatrix
