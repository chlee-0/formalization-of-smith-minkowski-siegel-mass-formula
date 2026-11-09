import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalCarrierRestriction
import SMSFormula.RationalCliffordSpinCandidateLatticeRefinedPieceRestrictedPushforward

/-!
# Real--finite form of the restricted Spin orbital kernel

The literal raw Spin orbit exposed by the carrier restriction is transported
through the exact real--finite equivalences.  Naturality of the intrinsic Spin
inclusion identifies the transported orbit componentwise, and the raw adelic
measure of its identity-carrier preimage becomes the established real--finite
raw Spin product measure.

This is only a coordinate-free product transport.  It introduces no chart,
section, or normalization coefficient.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The intrinsic Spin inclusion commutes with the exact full-adelic
real--finite splittings. -/
theorem fullAdelicCliffordSpinCandidateToGeneralSpinHom_realFinite
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x) =
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ
          (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).1,
        V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele
          (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).2) := by
  apply Prod.ext
  · change CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinRealAlgHom
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele x) = _
    exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality
      RationalAdele fullAdelicCliffordGeneralSpinRealAlgHom x
  · change CliffordGeneralSpinIntrinsicPoint.map V
        fullAdelicCliffordGeneralSpinFiniteAlgHom
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele x) = _
    exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality
      RationalAdele fullAdelicCliffordGeneralSpinFiniteAlgHom x

/-- The componentwise real--finite Spin orbit through an actual adelic
`GSpin` point. -/
def cliffordSpinCandidateRealFiniteOrbitAt
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    (V.RealCliffordSpinCandidateGroup ×
      V.FiniteAdelicCliffordSpinCandidateGroup) →
      (V.RealCliffordGeneralSpinGroup ×
        V.FiniteAdelicCliffordGeneralSpinGroup) :=
  fun y =>
    (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y.1 *
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1,
      V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalFiniteAdele y.2 *
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).2)

theorem continuous_cliffordSpinCandidateRealFiniteOrbitAt
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    Continuous (V.cliffordSpinCandidateRealFiniteOrbitAt g) := by
  exact
    (((V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom ℝ).comp
        continuous_fst).mul continuous_const).prodMk
      (((V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
        RationalFiniteAdele).comp continuous_snd).mul continuous_const)

/-- Splitting a literal full-adelic Spin orbit gives its componentwise
real--finite orbit. -/
theorem fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_spinOrbit
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x * g) =
      V.cliffordSpinCandidateRealFiniteOrbitAt g
        (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x) := by
  rw [map_mul, V.fullAdelicCliffordSpinCandidateToGeneralSpinHom_realFinite x]
  rfl

/-- The exposed full-adelic identity-carrier preimage is exactly the pullback
of the componentwise real--finite orbit preimage. -/
theorem preimage_fullAdelicCliffordSpinCandidateOrbit_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    (fun y : V.FullAdelicCliffordSpinCandidateGroup =>
        V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
        V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S =
      V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv ⁻¹'
        (V.cliffordSpinCandidateRealFiniteOrbitAt g ⁻¹'
          V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S) := by
  ext y
  change
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g ∈
        V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm ''
          V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S ↔ _
  rw [Set.mem_image]
  constructor
  · rintro ⟨z, hz, hzy⟩
    change V.cliffordSpinCandidateRealFiniteOrbitAt g
        (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv y) ∈
          V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S
    rw [← V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_spinOrbit g y,
      ← hzy]
    simpa using hz
  · intro hy
    refine ⟨V.cliffordSpinCandidateRealFiniteOrbitAt g
        (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv y), hy, ?_⟩
    rw [← V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_spinOrbit g y]
    exact V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm_apply_apply _

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance orbitalRealFiniteRealSpinMeasurableSpace (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance orbitalRealFiniteRealSpinBorelSpace (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance orbitalRealFiniteFiniteSpinMeasurableSpace (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance orbitalRealFiniteFiniteSpinBorelSpace (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance orbitalRealFiniteRealGSpinMeasurableSpace (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  borel _

local instance orbitalRealFiniteRealGSpinBorelSpace (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance orbitalRealFiniteFiniteGSpinMeasurableSpace (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance orbitalRealFiniteFiniteGSpinBorelSpace (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-- Raw Spin mass of the exposed full-adelic orbit preimage, expressed on the
literal real--finite product. -/
theorem spinOrbit_identityChart_mass_eq_realFinite
    (L : PositiveDefiniteIntegralLattice n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    D.spinData.adelicMeasure
        ((fun y : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup =>
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
          (L.rationalQuadraticSpaceMatrix
            |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S)) =
      L.cliffordSpinCandidateRealFiniteRawMeasure D
        (L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt g ⁻¹'
          (L.rationalQuadraticSpaceMatrix
            |>.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let C := V.cliffordSpinCandidateRealFiniteOrbitAt g ⁻¹'
    V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S
  have hC : MeasurableSet C :=
    (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S).preimage
      (V.continuous_cliffordSpinCandidateRealFiniteOrbitAt g).measurable
  rw [V.preimage_fullAdelicCliffordSpinCandidateOrbit_identityChart S g]
  rw [D.spinRaw.adelicMeasure_eq]
  unfold cliffordSpinCandidateRealFiniteRawMeasure
  rw [← V.map_fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite
    D.spinFiniteScale]
  exact (Measure.map_apply E.continuous.measurable hC).symm

/-- The descended orbital-kernel mass on the identity carrier is therefore
the real--finite raw Spin mass of the componentwise orbit preimage. -/
theorem positiveSpinOrbitalKernel_projection_apply_identityChart_eq_realFinite
    {r : ℕ}
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)
        (L.rationalQuadraticSpaceMatrix
          |>.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) =
      L.cliffordSpinCandidateRealFiniteRawMeasure D
        (L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateRealFiniteOrbitAt g ⁻¹'
          (L.rationalQuadraticSpaceMatrix
            |>.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S)) := by
  rw [L.positiveSpinOrbitalKernel_projection_apply_identityChart hr D S g]
  exact L.spinOrbit_identityChart_mass_eq_realFinite D S g

end PositiveDefiniteIntegralLattice

end
