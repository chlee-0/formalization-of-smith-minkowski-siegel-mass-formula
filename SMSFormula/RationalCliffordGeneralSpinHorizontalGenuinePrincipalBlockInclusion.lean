import SMSFormula.RationalCliffordGeneralSpinHorizontalGenuinePrincipalBlockMeasure

/-!
# Inclusions between genuine horizontal GSpin blocks

The block transitions are defined by splitting the
exceptional/tail coordinates, including the newly exceptional integral
coordinates, and reassembling.  This file proves that this coordinate
operation does not change the underlying local family.  After transport to
the intrinsic finite-adelic carrier, the genuine transition is therefore the
inclusion of the same point into the larger principal block.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance horizontalGenuineInclusionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- Splitting, including, and reassembling the horizontal source preserves
every underlying local `GSpin` coordinate. -/
theorem cliffordGeneralSpinHorizontalTransitionSource_assemble_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock T
      (V.cliffordGeneralSpinHorizontalTransitionSource S T hST g)).1.1 v =
      (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock
        S g).1.1 v := by
  by_cases hvS : v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S
  · have hvT : v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T :=
      V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST hvS
    simp [cliffordGeneralSpinHorizontalTransitionSource,
      cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph,
      cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph,
      cliffordGeneralSpinHorizontalTransitionSourceInclusion,
      cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph,
      cliffordGeneralSpinHorizontalExceptionalTransitionAssemble,
      cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph,
      cliffordGeneralSpinHorizontalIntegralTailTransitionSplit,
      Homeomorph.prodAssoc, hvS, hvT]
  · by_cases hvT : v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces T
    · simp [cliffordGeneralSpinHorizontalTransitionSource,
        cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph,
        cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph,
        cliffordGeneralSpinHorizontalTransitionSourceInclusion,
        cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph,
        cliffordGeneralSpinHorizontalExceptionalTransitionAssemble,
        cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph,
        cliffordGeneralSpinHorizontalIntegralTailTransitionSplit,
        cliffordGeneralSpinHorizontalNewIntegralExceptionalInclusion,
        Homeomorph.prodAssoc, hvS, hvT]
    · simp [cliffordGeneralSpinHorizontalTransitionSource,
        cliffordGeneralSpinHorizontalLargerTransitionSourceHomeomorph,
        cliffordGeneralSpinHorizontalSmallerTransitionSourceHomeomorph,
        cliffordGeneralSpinHorizontalTransitionSourceInclusion,
        cliffordGeneralSpinHorizontalExceptionalTransitionHomeomorph,
        cliffordGeneralSpinHorizontalIntegralTailTransitionHomeomorph,
        cliffordGeneralSpinHorizontalIntegralTailTransitionSplit,
        Homeomorph.prodAssoc, hvS, hvT]
      congr 1

/-- The restricted-family block transition changes only the proof that the
same local family belongs to the larger block. -/
theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_val
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (g : V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) :
    (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition
      S T hST g).1 = g.1 := by
  apply Subtype.ext
  funext v
  let eS :=
    V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
  change
    (V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock T
      (V.cliffordGeneralSpinHorizontalTransitionSource S T hST
        (eS.symm g))).1.1 v = g.1.1 v
  rw [V.cliffordGeneralSpinHorizontalTransitionSource_assemble_apply
    S T hST (eS.symm g) v]
  exact congrArg (fun x ↦ x.1.1 v) (eS.apply_symm_apply g)

/-- Literal inclusion of a genuine horizontal principal block into a larger
one, retaining the identical intrinsic finite-adelic point. -/
def cliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T) :
    V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S →
      V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock T :=
  fun x ↦ ⟨x.1, fun v hv ↦
    x.2 v fun hS ↦ hv
      (V.cliffordGeneralSpinHorizontalExceptionalPlaces_mono hST hS)⟩

@[simp]
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion_val
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (x : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion
      S T hST x).1 = x.1 := rfl

/-- The conjugated genuine transition is exactly the literal inclusion of the
unchanged intrinsic finite-adelic point. -/
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_eq_inclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (x : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition S T hST x =
      V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockInclusion S T hST x := by
  let eS :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S
  let eT :=
    V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph T
  apply eT.injective
  simp only [cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition,
    Function.comp_apply]
  rw [eT.apply_symm_apply]
  apply Subtype.ext
  exact V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockTransition_val
    S T hST (eS x)

@[simp]
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_val
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST : S ⊆ T)
    (x : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition
      S T hST x).1 = x.1 := by
  rw [V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockTransition_eq_inclusion
    S T hST x]
  rfl

end RationalQuadraticSpaceMatrix
