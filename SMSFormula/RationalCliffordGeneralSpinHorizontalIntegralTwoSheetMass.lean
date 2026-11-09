import SMSFormula.RationalCliffordGeneralSpinHorizontalTwoSheet
import SMSFormula.RationalCliffordGeneralSpinHorizontalCentralOrbitChartProduct
import SMSFormula.RationalCliffordGeneralSpinHorizontalExactness

/-! The integral GSpin locus as a central-fiber preimage. At a horizontal good
place, if every integral `SO` point has an integral `GSpin` lift (the
integral Cartan–Dieudonné lift at odd unimodular places), then a `GSpin` point
is integral exactly when its similitude is an integral unit and its `SO` image
is integral: the integral locus is `φ⁻¹(ℤ_p^× × SO_int)` for the central
fiber map `φ`. With the two-sheet mass,

`v^G_{V,p} = 2 · (Haar × μ_SO)((ℤ_p^× × SO_int) ∩ range φ)`.

This is step (b) of the GSpin central factor. The lift is a supplied hypothesis
here; no section or sheet is chosen. -/
noncomputable section
open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance integralTwoSheetPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

noncomputable local instance integralTwoSheetPadicUnitMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance integralTwoSheetPadicUnitBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance integralTwoSheetPadicSOMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance integralTwoSheetPadicSOBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- The integral `GSpin` locus is the central-fiber preimage of `ℤ_p^× × SO_int`,
given integral lifts of integral `SO` points. -/
theorem padicCliffordGeneralSpinIsIntegral_iff_centralFiber
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hlift : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      g ∈ V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 →
      ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
        V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 y ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g)
    (x : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) :
    V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 x ↔
      x.similitude ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 ∧
        x.matrixGroup ∈ V.padicSpecialOrthogonalIntegralSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
  constructor
  · intro h
    exact ⟨h.2.2.1, h.2.2.2⟩
  · rintro ⟨hnu, hg⟩
    obtain ⟨y, hy, hyx⟩ := hlift x.matrixGroup hg
    have hker : x * y⁻¹ ∈ (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]
      change x.matrixGroup * x.matrixGroup⁻¹ = 1
      exact mul_inv_cancel _
    rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom] at hker
    obtain ⟨a, ha⟩ := hker
    have hx : x = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] a * y := by
      rw [ha, inv_mul_cancel_right]
    have hyInt : y ∈ V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v := hy
    have haU : a ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
      have hsim : x.similitude = a ^ 2 * y.similitude := by
        rw [hx, CliffordGeneralSpinIntrinsicPoint.mul_similitude]
        rfl
      have hyNu : y.similitude ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 := hy.2.2.1
      have haSq : a ^ 2 ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
        have hmul := (padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1).mul_mem hnu
          ((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1).inv_mem hyNu)
        rw [hsim] at hmul
        simpa [mul_assoc] using hmul
      exact Rat.mem_padicIntegralUnitsSubgroup_of_sq_mem (Rat.HeightOneSpectrum.primesEquiv v.1).1 a haSq
    rw [hx]
    exact (V.padicCliffordGeneralSpinHorizontalIntegralCentralOrbit_isIntegral_iff S v a
      ⟨y, hyInt⟩).mpr haU

/-- Step (b): the horizontal integral `GSpin` volume is twice the product
mass of the integral part of the central-fiber image. -/
theorem padicCliffordGeneralSpinHorizontalIntegralVolume_eq_two_mul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hlift : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      g ∈ V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 →
      ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
        V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 y ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 =
      2 * V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
        (((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set _) ×ˢ
            (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
              Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) := by
  have hset : {g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] | V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 g} =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
        ((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set _) ×ˢ
          (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) := by
    ext x
    exact V.padicCliffordGeneralSpinIsIntegral_iff_centralFiber S v hlift x
  have hB : MeasurableSet ((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) ×ˢ
      (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) :=
    ((isOpen_padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
      (V.isOpen_padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1)).measurableSet
  rw [padicCliffordGeneralSpinHorizontalIntegralVolume, hset]
  exact V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage (Rat.HeightOneSpectrum.primesEquiv v.1).1 hB

end RationalQuadraticSpaceMatrix
