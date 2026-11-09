import SMSFormula.RationalCliffordGeneralSpinHorizontalLocalCentralOrbitChart
import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralCentralFiber

/-!
# Exceptional-product and integral-tail central-orbit intersections

The local central-orbit/identity-sheet equality is assembled over the finite
horizontal exceptional product.  On the unchanged good tail, a central
translate of a fixed integral `GSpin` point is integral exactly when its
scalar is an integral unit.  Taking the dependent product gives the exact
preimage of the integral `GSpin` tail inside the unrestricted tail.

These are set-level restricted-product statements.  No Cartesian
presentation of `GSpin`, measurable section, measure identity, or adelic
carrier conjugation is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalCentralOrbitChartProductPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalCentralOrbitChartProductDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-! ## Integral local orbit -/

/-- At a retained good place, translating an integral horizontal `GSpin`
point by an arbitrary scalar remains integral exactly when the scalar is an
integral unit. -/
theorem padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (a : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :
    V.PadicCliffordGeneralSpinIsIntegral
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] a * g.1) ↔
      a ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
  let hvStructure :=
    V.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
      v.1 (fun hv => v.2 (Finset.mem_union_right S hv))
  constructor
  · intro h
    have hnu := h.2.2.1
    have hgNu : g.1.similitude ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 := g.2.2.2.1
    rw [CliffordGeneralSpinIntrinsicPoint.mul_similitude] at hnu
    change a ^ 2 * g.1.similitude ∈ padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 at hnu
    have haSq : a ^ 2 ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
      have hmul :=
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).mul_mem hnu
          ((padicIntegralUnitsSubgroup
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).inv_mem hgNu)
      simpa [mul_assoc] using hmul
    exact mem_padicIntegralUnitsSubgroup_of_sq_mem
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 a haSq
  · intro ha
    exact V.padicCliffordGeneralSpinIsIntegral_mul v.1 hvStructure
      (V.padicCliffordGeneralSpin_ofScalar_isIntegral v.1 hvStructure a ha) g.2

/-! ## Finite exceptional product -/

/-- Componentwise central orbit through fixed Spin-chart points at every
horizontal exceptional place. -/
def cliffordGeneralSpinHorizontalExceptionalCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    RationalIdeleDifferentialExceptionalProduct
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
  fun a v =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (a v) *
      V.cliffordSpinCandidateToCliffordGeneralSpinHom
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (s v)

/-- The exceptional central orbit meets the product identity carrier exactly
on the product of the chosen scalar square branches. -/
theorem preimage_cliffordGeneralSpinHorizontalExceptionalCentralOrbit_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s ⁻¹'
        V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S =
      rationalIdeleDifferentialExceptionalSquareChartCarrier
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  ext a
  constructor
  · intro ha v _
    have hv := ha v (Set.mem_univ v)
    have hlocal :=
      V.preimage_padicCliffordGeneralSpinCentralOrbit_identityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 (s v) (s v).2
    exact (Set.ext_iff.mp hlocal (a v)).mp hv
  · intro ha v _
    have hlocal :=
      V.preimage_padicCliffordGeneralSpinCentralOrbit_identityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 (s v) (s v).2
    exact (Set.ext_iff.mp hlocal (a v)).mpr (ha v (Set.mem_univ v))

/-! ## Infinite good tail -/

/-- Componentwise central orbit through a fixed integral `GSpin` tail, with
the scalar coordinates initially unrestricted. -/
def cliffordGeneralSpinHorizontalIntegralTailCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    RationalIdeleDifferentialUnrestrictedTail
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) →
      V.CliffordGeneralSpinHorizontalUnrestrictedGoodTail S :=
  fun a v =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (a v) *
      (g v).1

/-- The unrestricted scalar tail maps back into the integral `GSpin` tail
exactly on the range of the integral-unit scalar tail. -/
theorem preimage_cliffordGeneralSpinHorizontalIntegralTailCentralOrbit_integralTail
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalIntegralTailCentralOrbit S g ⁻¹'
        Set.range (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S) =
      Set.range (rationalIdeleDifferentialIntegralTailInclusion
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  ext a
  constructor
  · rintro ⟨h, hh⟩
    let z : RationalIdeleDifferentialIntegralTail
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :=
      fun v => ⟨a v, by
        apply (V.padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff
          S v (a v) (g v)).mp
        have hev : (h v).1 =
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (a v) *
              (g v).1 := by
          simpa [cliffordGeneralSpinHorizontalIntegralTailCentralOrbit] using
            congrFun hh v
        rw [← hev]
        exact (h v).2⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    let h : V.CliffordGeneralSpinHorizontalIntegralTail S :=
      fun v => ⟨
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (z v).1 *
          (g v).1,
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff
          S v (z v).1 (g v)).mpr (z v).2⟩
    exact ⟨h, rfl⟩

/-! ## Combined finite restricted-product source -/

/-- Product of the exceptional central orbit and the unrestricted good-tail
central orbit through fixed compatible chart data. -/
def cliffordGeneralSpinHorizontalExceptionalTailCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    RationalIdeleDifferentialExceptionalProduct
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) ×
        RationalIdeleDifferentialUnrestrictedTail
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalUnrestrictedGoodTail S :=
  Prod.map
    (V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s)
    (V.cliffordGeneralSpinHorizontalIntegralTailCentralOrbit S g)

/-- On the direct exceptional/unrestricted-tail source, the central orbit
meets the exceptional identity charts and integral `GSpin` tail exactly on
the scalar square charts and integral-unit scalar tail. -/
theorem preimage_cliffordGeneralSpinHorizontalExceptionalTailCentralOrbit_chart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalExceptionalTailCentralOrbit S s g ⁻¹'
        (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ×ˢ
          Set.range (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S)) =
      rationalIdeleDifferentialExceptionalSquareChartCarrier
            (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) ×ˢ
        Set.range (rationalIdeleDifferentialIntegralTailInclusion
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  ext a
  change
    V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s a.1 ∈
          V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ∧
        V.cliffordGeneralSpinHorizontalIntegralTailCentralOrbit S g a.2 ∈
          Set.range (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S) ↔
      a.1 ∈ rationalIdeleDifferentialExceptionalSquareChartCarrier
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) ∧
        a.2 ∈ Set.range (rationalIdeleDifferentialIntegralTailInclusion
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
  have hExceptional :
      V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s a.1 ∈
          V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ↔
        a.1 ∈ rationalIdeleDifferentialExceptionalSquareChartCarrier
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
    change a.1 ∈
        V.cliffordGeneralSpinHorizontalExceptionalCentralOrbit S s ⁻¹'
          V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ↔ _
    exact Set.ext_iff.mp
      (V.preimage_cliffordGeneralSpinHorizontalExceptionalCentralOrbit_identityChart
        S s) a.1
  have hTail :
      V.cliffordGeneralSpinHorizontalIntegralTailCentralOrbit S g a.2 ∈
          Set.range (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S) ↔
        a.2 ∈ Set.range (rationalIdeleDifferentialIntegralTailInclusion
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
    change a.2 ∈
        V.cliffordGeneralSpinHorizontalIntegralTailCentralOrbit S g ⁻¹'
          Set.range (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S) ↔ _
    exact Set.ext_iff.mp
      (V.preimage_cliffordGeneralSpinHorizontalIntegralTailCentralOrbit_integralTail
        S g) a.2
  exact and_congr hExceptional hTail

end RationalQuadraticSpaceMatrix
