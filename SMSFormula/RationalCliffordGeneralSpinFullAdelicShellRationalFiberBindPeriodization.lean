import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRationalFiberPeriodization

/-!
# Periodization across the rational block-shell fiber bind

Rational-diagonal periodization commutes, at the nonnegative-integral level,
with binding any measurable kernel into the rational adelic GSpin quotient.
The proof uses the quotient left-periodization formula and kernel
Tonelli; it chooses no representatives.

For the block shell, the shell measure bound against the inverse-translated
crossed rational fibers is one measure on the block rational GSpin
quotient.  Periodizing this bound measure is exactly the
shell integral of the periodized fibers.  At an orbit point, the inner measure is
the vertical scalar times the inverse right translate of the complete
rational shell-coset raw-fiber sum.  No term or scalar is cancelled.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open ProbabilityTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Periodizing a kernel bind is the same as integrating the periodization of
each fiber.  This is stated at the nonnegative-integral level so no auxiliary
periodized-fiber kernel or measurable structure is introduced. -/
theorem lintegral_periodizedQuotientLift_bind
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X)
    (kappa : Kernel X V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (mu.bind kappa) =
      ∫⁻ x, ∫⁻ g, f g
          ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift (kappa x)
        ∂mu := by
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (mu.bind kappa) f hf]
  have hperiodize : Measurable
      (leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f) :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize f hf
  rw [Measure.lintegral_bind kappa.aemeasurable hperiodize.aemeasurable]
  apply lintegral_congr
  intro x
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (kappa x) f hf]

end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

noncomputable local instance rationalFiberBindShellMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance rationalFiberBindShellBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The measure on the existing block rational GSpin quotient obtained by
binding the crossed rational fibers against the native invariant shell
measure. -/
noncomputable def fullAdelicNonisotropicLastShellRationalFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measure
      (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  (L.rationalQuadraticSpaceMatrix
      |>.fullAdelicNonisotropicLastShellMeasure a ha).bind
    (D.fullAdelicNonisotropicLastShellRationalFiberKernel
      L hn a ha hsurj)

/-- At a shell orbit point, periodization of the rational fiber is the
vertical scalar times the inverse translate of the complete rational
shell-coset raw-fiber sum. -/
theorem periodized_nonisotropicLastShellRationalFiberKernel_orbit
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.fullAdelicNonisotropicLastShellRationalFiberKernel
          L hn a ha hsurj
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele g)) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        Measure.map
          (fun z : V.FullAdelicCliffordGeneralSpinGroup => z * g⁻¹)
          (Measure.sum fun xi :
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
            W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
              a ha xi) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  rw [D.fullAdelicNonisotropicLastShellRationalFiberKernel_orbit
    L hn a ha hsurj g]
  rw [← D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply
    L hn a ha hsurj g]
  exact D.periodized_nonisotropicLastShellAmbientRationalFiberKernel_apply
    L hn a ha hsurj g

/-- Every native shell point has an ambient representative for which its
periodized rational fiber has the full inverse-translated rational-coset
formula.  This is existential only and does not select a shell section. -/
theorem exists_periodized_nonisotropicLastShellRationalFiberKernel_eq_rawFibers
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    ∃ g : V.FullAdelicCliffordGeneralSpinGroup,
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha RationalAdele g = x ∧
        V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
            (D.fullAdelicNonisotropicLastShellRationalFiberKernel
              L hn a ha hsurj x) =
          D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
            Measure.map
              (fun z : V.FullAdelicCliffordGeneralSpinGroup => z * g⁻¹)
              (Measure.sum fun xi :
                V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
                  W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
                W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
                  a ha xi) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  obtain ⟨g, rfl⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha x
  exact ⟨g, rfl,
    D.periodized_nonisotropicLastShellRationalFiberKernel_orbit
      L hn a ha hsurj g⟩

/-- Periodization commutes exactly with the native-shell bind of the crossed
rational fibers.  The right side remains representative-free; the preceding
orbit theorem gives its full inverse-translated rational-coset value. -/
theorem lintegral_periodized_nonisotropicLastShellRationalFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    ∫⁻ g, f g
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.fullAdelicNonisotropicLastShellRationalFiberBoundMeasure
            L hn a ha hsurj) =
      ∫⁻ x, ∫⁻ g, f g
          ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
            (D.fullAdelicNonisotropicLastShellRationalFiberKernel
              L hn a ha hsurj x)
        ∂W.fullAdelicNonisotropicLastShellMeasure a ha := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  exact V.lintegral_periodizedQuotientLift_bind
    (W.fullAdelicNonisotropicLastShellMeasure a ha)
    (D.fullAdelicNonisotropicLastShellRationalFiberKernel
      L hn a ha hsurj) f hf

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
