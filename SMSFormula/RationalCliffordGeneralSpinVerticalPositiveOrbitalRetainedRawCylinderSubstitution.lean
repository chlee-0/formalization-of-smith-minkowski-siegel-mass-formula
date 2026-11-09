import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedCylinderIntegrationOrder

/-!
# Substitute the raw retained source into the reconstructed cylinder

The retained scalar square source and the translated raw Spin source have
already been compared as measures.  This file applies that comparison under
arbitrary nonnegative integrands and uses the a.e. reconstruction theorem to
replace the scalar-times-Spin orbit by the horizontal split
reconstruction.

The unique coefficient is the raw finite block scalar.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3200000

local instance retainedRawCylinderSubstitutionDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedRawCylinderSubstitutionRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedRawCylinderSubstitutionRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedRawCylinderSubstitutionFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedRawCylinderSubstitutionFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-- The full-adelic scalar-times-Spin orbit carried by the retained
source.  This is the right-hand side of the reconstruction
identity, named only to state the integral substitution compactly. -/
def cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.CliffordGeneralSpinVerticalRetainedCylinderSource S →
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  fun z =>
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        L.rationalQuadraticSpaceMatrix RationalAdele
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)
          z.1) *
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
        (L.retainedRealFiniteSpinSourceOrbit S x z.2)

/-- The retained componentwise Spin orbit is the real--finite splitting of
the full-adelic Spin orbit through the retained origin. -/
theorem fullAdelicCliffordGeneralSpinRealFinite_symm_retainedSpinSourceOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (u : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.realCliffordSpinCandidateIdentityChart.source ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail B)) :
    let V := L.rationalQuadraticSpaceMatrix
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
        (L.retainedRealFiniteSpinSourceOrbit S x u) =
      V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
          (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm
            (L.retainedRealSpinSourceToOrbitPreimage S x u.1,
              L.retainedSpinBlockSourceToOrbitPreimage S x u.2)) *
        L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  apply V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.injective
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_spinOrbit]
  rw [V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.apply_symm_apply]
  rfl

/-- The similitude coordinate of the retained cylinder orbit is
the square of its differential scalar coordinate times the
similitude of the retained origin. -/
theorem fullAdelicCliffordGeneralSpinSimilitude_retainedCylinderLiteralOrbit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (z : L.CliffordGeneralSpinVerticalRetainedCylinderSource S) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.fullAdelicCliffordGeneralSpinSimilitudeHom
        (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x z) =
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
          B z.1) ^ 2 *
        V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  unfold cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit
  rw [map_mul]
  rw [L.fullAdelicCliffordGeneralSpinRealFinite_symm_retainedSpinSourceOrbit S x z.2]
  rw [map_mul]
  change
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        V RationalAdele
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele
          (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
            B z.1)) *
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          V RationalAdele
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
            (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm
              (L.retainedRealSpinSourceToOrbitPreimage S x z.2.1,
                L.retainedSpinBlockSourceToOrbitPreimage S x z.2.2))) *
        V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x)) = _
  rw [RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom_comp_scalarGroupHom]
  unfold RationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom
  have hspin :
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          V RationalAdele
          ((V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele)
            (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm
              (L.retainedRealSpinSourceToOrbitPreimage S x z.2.1,
                L.retainedSpinBlockSourceToOrbitPreimage S x z.2.2))) = 1 := by
    change
      ((V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele)
        (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.symm
          (L.retainedRealSpinSourceToOrbitPreimage S x z.2.1,
            L.retainedSpinBlockSourceToOrbitPreimage S x z.2.2))).similitude = 1
    exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude _ _
  rw [hspin, one_mul]

/-- Under every nonnegative integrand, the full differential
square source paired with raw Spin Haar restricted to the retained
orbit preimage is exactly the reconstructed normalized cylinder multiplied
by `spinFiniteScale * spinBlockWeight(B)`. -/
theorem lintegral_cliffordGeneralSpinVerticalRetainedRawCylinderSubstitution
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ENNReal) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    let rawSource :=
      (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure B).prod
        (((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j)
    let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
    (∫⁻ z, f (L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x z)
        ∂rawSource) =
      ((D.spinFiniteScale : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B) *
        ∫⁻ z, f (toFull (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z))
          ∂L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let c : ℝ≥0∞ := (D.spinFiniteScale : ℝ≥0∞) *
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight B
  let μ := L.cliffordGeneralSpinVerticalRetainedCylinderSourceMeasure S
  let literal := L.cliffordGeneralSpinVerticalRetainedCylinderLiteralOrbit S x
  let toFull := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hsource :=
    L.rationalIdeleSquare_prod_rawSpinRestrict_comap_retainedSources D S x
  change (∫⁻ z, f (literal z) ∂_) = c * ∫⁻ z,
    f (toFull (L.cliffordGeneralSpinVerticalRetainedCylinderToSplit S x z)) ∂μ
  rw [hsource, lintegral_smul_measure]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [
    L.ae_cliffordGeneralSpinVerticalRetainedCylinderSource_mem_identityCarrier S] with z hz
  congr 1
  exact (L.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_retainedCylinder
    S x z hz).symm

end PositiveDefiniteIntegralLattice

end
