import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedRealFiniteSource

/-!
# Restrict the retained real--finite Spin source to the literal orbit carrier

The translated real and finite source embeddings pull raw Spin Haar
back with the exact finite block coefficient.  Here that source identity is
restricted to the retained orbit preimage.  Its source-side inverse
image is exactly the full real chart source times the retained
finite identity cylinder.

This is a preimage statement only.  Neither translated source is shown to be a
global parametrization.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance retainedRealFiniteRestrictionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedRealFiniteRestrictionRealGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedRealFiniteRestrictionRealGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedRealFiniteRestrictionFiniteGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedRealFiniteRestrictionFiniteGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedRealFiniteRestrictionExceptionalSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedRealFiniteRestrictionExceptionalBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B) :=
  Pi.borelSpace

local instance retainedRealFiniteRestrictionIntegralFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance retainedRealFiniteRestrictionIntegralFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace B) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor B v) :=
  Subtype.borelSpace _

local instance retainedRealFiniteRestrictionTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance retainedRealFiniteRestrictionTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B) :=
  Pi.borelSpace

/-- The translated real chart source lies entirely in the retained real orbit
preimage.  This uses only the literal right-translation formula. -/
theorem preimage_retainedRealSpinSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.retainedRealSpinSourceToOrbitPreimage S x ⁻¹'
        L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x =
      Set.univ := by
  rw [L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage_eq_preimage_mul S x]
  ext u
  simp [retainedRealSpinSourceToOrbitPreimage, mul_assoc]

/-- The translated finite block source meets the retained finite orbit
preimage on exactly the exceptional identity cylinder. -/
theorem preimage_retainedSpinBlockSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    L.retainedSpinBlockSourceToOrbitPreimage S x ⁻¹'
        L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x =
      V.retainedSpinExceptionalTailIdentityCylinder B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let j := L.retainedSpinBlockSourceToOrbitPreimage S x
  rw [L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_image_orbitPreimageSource
    S x]
  exact Set.preimage_image_eq _
    (L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x).injective

/-- Pulling the Cartesian retained orbit preimage back through the paired
translated source gives the full real source times the finite identity
cylinder. -/
theorem preimage_retainedRealFiniteOrbitPreimageSources
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
        (L.retainedSpinBlockSourceToOrbitPreimage S x) ⁻¹'
      (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
        L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x) =
      Set.univ ×ˢ V.retainedSpinExceptionalTailIdentityCylinder B := by
  dsimp only
  have hR := Set.ext_iff.mp
    (L.preimage_retainedRealSpinSourceToOrbitPreimage S x)
  have hF := Set.ext_iff.mp
    (L.preimage_retainedSpinBlockSourceToOrbitPreimage S x)
  ext u
  simpa only [Set.mem_preimage, Set.mem_prod, Prod.map_apply, Set.mem_univ,
    true_and] using and_congr (hR u.1) (hF u.2)

/-- The exact source-level restriction of raw real--finite Spin Haar.  The
only coefficient remains `spinFiniteScale * spinBlockWeight(B)`, and the
source restriction is literally `univ × retainedIdentityCylinder`. -/
theorem cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage_comap_sources
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict
        (L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
          L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x)).comap
      (Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
        (L.retainedSpinBlockSourceToOrbitPreimage S x)) =
      (V.realCliffordSpinCandidateIdentityChartSourceMeasure.prod
        (((↑D.spinFiniteScale *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) •
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure B))).restrict
        (Set.univ ×ˢ V.retainedSpinExceptionalTailIdentityCylinder B) := by
  dsimp only
  let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
    (L.retainedSpinBlockSourceToOrbitPreimage S x)
  have hj : MeasurableEmbedding j :=
    (L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x).prodMap
      (L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x)
  rw [hj.comap_restrict]
  rw [L.preimage_retainedRealFiniteOrbitPreimageSources S x]
  rw [L.cliffordSpinCandidateRealFiniteRawMeasure_comap_retainedOrbitPreimageSources D S x]

end PositiveDefiniteIntegralLattice

end
