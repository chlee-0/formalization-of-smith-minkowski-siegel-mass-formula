import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRawCosetSumKernel

/-!
# The exact nonisotropic one-shell cutoff

A measurable nonnegative test on the quadratic shell weights its invariant
measure.  Binding this weighted measure against the crossed
rational-quotient fibers gives the one-shell measure on the block rational
`GSpin` quotient.

Every translated rational fiber has the same logarithmic cutoff: translation
adds a constant to the logarithmic similitude coordinate, and the fixed
idèle-class Haar cutoff is translation invariant.  The one-shell cutoff
therefore factors exactly as

```text
shell integral * idèle-class cutoff * lower-rank Spin volume.
```

Periodizing the same measure gives the vertical scalar times the
shell-weighted complete rational shell-coset raw-fiber kernel.  Thus the
rational shell-coset sum is the theta-orbit sum; it is not collapsed to a
singleton.  No representative or section is chosen, and no scalar is
cancelled.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

/-- The common rational idèle-class logarithmic cutoff is invariant under
translation of its real logarithmic coordinate. -/
theorem rationalIdeleClassLogCutoffLIntegral_add_right
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (c : ℝ) :
    rationalIdeleClassLogCutoffLIntegral (fun t => f (t + c)) =
      rationalIdeleClassLogCutoffLIntegral f := by
  calc
    rationalIdeleClassLogCutoffLIntegral (fun t => f (t + c)) =
        rationalIdeleClassLogHaarScalar * ∫⁻ t : ℝ, f (t + c) :=
      rationalIdeleClassLogCutoffLIntegral_eq_real _
        (hf.comp (measurable_id.add measurable_const))
    _ = rationalIdeleClassLogHaarScalar * ∫⁻ t : ℝ, f t := by
      rw [lintegral_add_right_eq_self]
    _ = rationalIdeleClassLogCutoffLIntegral f :=
      (rationalIdeleClassLogCutoffLIntegral_eq_real f hf).symm

variable {n : ℕ}

noncomputable local instance oneShellCutoffTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance oneShellCutoffTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- At an actual shell orbit, inverse translation of the crossed rational
fiber does not change its full logarithmic cutoff. -/
theorem
    lintegral_fullAdelicNonisotropicLastShellRationalFiberKernel_orbit_logCutoff
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂D.fullAdelicNonisotropicLastShellRationalFiberKernel
        L hn a ha hsurj
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          L.rationalQuadraticSpaceMatrix a ha RationalAdele g)) =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  rw [D.fullAdelicNonisotropicLastShellRationalFiberKernel_orbit
    L hn a ha hsurj g]
  change (∫⁻ z,
      (f ∘ V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule) z
      ∂Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj)) = _
  rw [lintegral_map'
    (hf.comp V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable).aemeasurable
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹).aemeasurable]
  let c : ℝ := rationalIdeleLogModule
    (V.fullAdelicCliffordGeneralSpinSimilitudeHom g⁻¹)
  let f' : ℝ → ℝ≥0∞ := fun t => f (t + c)
  have hf' : Measurable f' := hf.comp (measurable_id.add measurable_const)
  simp only [Function.comp_apply]
  calc
    (∫⁻ z, f
        (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹ z))
        ∂D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) =
        ∫⁻ z, f'
          (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
          ∂D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
            L hn a ha hsurj := by
      apply lintegral_congr
      intro z
      rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_rightMul]
    _ = rationalIdeleClassLogCutoffLIntegral f' *
          D.spinTamagawaNumberENNReal :=
      D.lintegral_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_logCutoff_eq
        L hn a ha hsurj f' hf'
    _ = rationalIdeleClassLogCutoffLIntegral f *
          D.spinTamagawaNumberENNReal := by
      rw [rationalIdeleClassLogCutoffLIntegral_add_right f hf c]

/-- Every point of the actual shell has the same crossed rational-fiber
logarithmic cutoff, with the lower-rank Spin volume as its sole nontrivial
coefficient. -/
theorem lintegral_fullAdelicNonisotropicLastShellRationalFiberKernel_logCutoff
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (x : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂D.fullAdelicNonisotropicLastShellRationalFiberKernel
        L hn a ha hsurj x) =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  obtain ⟨g, rfl⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      L.rationalQuadraticSpaceMatrix a ha x
  exact
    lintegral_fullAdelicNonisotropicLastShellRationalFiberKernel_orbit_logCutoff
      L hn a ha D hsurj g f hf

/-- The actual one-shell measure on the existing block rational `GSpin`
quotient.  The nonnegative test `phi` weights the native shell measure; no
new shell carrier is introduced. -/
noncomputable def fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞) :
    Measure
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  ((L.rationalQuadraticSpaceMatrix
      |>.fullAdelicNonisotropicLastShellMeasure a ha).withDensity phi).bind
    (D.fullAdelicNonisotropicLastShellRationalFiberKernel
      L hn a ha hsurj)

/-- The quotient-side one-shell cutoff factors exactly into the shell test
integral, the common idèle-class cutoff, and the lower-rank Spin volume. -/
theorem
    lintegral_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_logCutoff_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
        L hn a ha D hsurj phi) =
      (∫⁻ x, phi x
        ∂(L.rationalQuadraticSpaceMatrix
          |>.fullAdelicNonisotropicLastShellMeasure a ha)) *
        rationalIdeleClassLogCutoffLIntegral f *
          D.spinTamagawaNumberENNReal := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let muX := W.fullAdelicNonisotropicLastShellMeasure a ha
  let kappa := D.fullAdelicNonisotropicLastShellRationalFiberKernel
    L hn a ha hsurj
  rw [fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure]
  change (∫⁻ z,
      (f ∘ V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule) z
      ∂(muX.withDensity phi).bind kappa) = _
  rw [Measure.lintegral_bind kappa.aemeasurable
    (hf.comp V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable).aemeasurable]
  simp only [Function.comp_apply]
  calc
    (∫⁻ x, ∫⁻ z,
        f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
          ∂kappa x ∂muX.withDensity phi) =
        ∫⁻ _x, rationalIdeleClassLogCutoffLIntegral f *
          D.spinTamagawaNumberENNReal ∂muX.withDensity phi := by
      apply lintegral_congr
      intro x
      exact
        lintegral_fullAdelicNonisotropicLastShellRationalFiberKernel_logCutoff
          L hn a ha D hsurj x f hf
    _ = (∫⁻ x, phi x ∂muX) *
          rationalIdeleClassLogCutoffLIntegral f *
            D.spinTamagawaNumberENNReal := by
      rw [lintegral_withDensity_eq_lintegral_mul muX hphi measurable_const]
      simp only [Pi.mul_apply]
      rw [lintegral_mul_const _ hphi]
      ac_rfl

/-- Periodizing the same one-shell quotient measure gives the
vertical scalar times the shell-weighted complete rational shell-coset raw
orbit kernel.  This is the theta-orbit side of the unfolding; the rational
coset sum is kept in full. -/
theorem
    lintegral_periodized_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (F : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hF : Measurable F) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    ∫⁻ g, F g
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
            L hn a ha D hsurj phi) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj *
        ∫⁻ x, phi x *
          (∫⁻ g, F g
            ∂W.fullAdelicNonisotropicLastShellRawCosetSumKernel a ha x)
          ∂W.fullAdelicNonisotropicLastShellMeasure a ha := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let muX := W.fullAdelicNonisotropicLastShellMeasure a ha
  let kappa := D.fullAdelicNonisotropicLastShellRationalFiberKernel
    L hn a ha hsurj
  let rho := W.fullAdelicNonisotropicLastShellRawCosetSumKernel a ha
  let q := D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj
  dsimp only
  rw [fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure]
  rw [V.lintegral_periodizedQuotientLift_bind
    (muX.withDensity phi) kappa F hF]
  have hinner : Measurable (fun x => ∫⁻ g, F g ∂rho x) :=
    hF.lintegral_kernel
  calc
    (∫⁻ x, ∫⁻ g, F g
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift (kappa x)
        ∂muX.withDensity phi) =
        ∫⁻ x, q * (∫⁻ g, F g ∂rho x) ∂muX.withDensity phi := by
      apply lintegral_congr
      intro x
      rw [show V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift (kappa x) =
          q • rho x by
        exact
          periodized_nonisotropicLastShellRationalFiberKernel_eq_smul_rawCosetSumKernel
            L hn a ha D hsurj x]
      rw [lintegral_smul_measure]
      rfl
    _ = q * ∫⁻ x, phi x * (∫⁻ g, F g ∂rho x) ∂muX := by
      rw [lintegral_withDensity_eq_lintegral_mul muX hphi
        (measurable_const.mul hinner)]
      simp only [Pi.mul_apply]
      rw [show (fun x => phi x * (q * ∫⁻ g, F g ∂rho x)) =
          fun x => q * (phi x * ∫⁻ g, F g ∂rho x) by
        funext x
        ac_rfl]
      rw [lintegral_const_mul q (hphi.mul hinner)]

end RationalQuadraticSpaceMatrix
