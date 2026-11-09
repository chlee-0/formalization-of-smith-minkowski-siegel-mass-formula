import SMSFormula.RationalAdeleCovarianceCutoffTransport
import SMSFormula.RationalAdeleWeylTransformNonnegative
import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedStandardTest
import SMSFormula.RationalCliffordGeneralSpinBoundedThetaFiniteness

/-!
# `I_V(Phi) = I_V(W Phi)` for the standard test and its polar Weyl transform

The transport of the geometric covariance lives in the complex layer: the complex cutoff integral
of the standard test equals that of its polar Weyl transform.  The cutoff-normalized functional
`I_V` lives in the nonnegative layer.  The two layers are already known to agree at the standard
test, because that test is a nonnegative real at a real width.  The same is true of the Weyl
transform, so the agreement extends to it and the covariance descends.

Both raw cutoff integrals are finite against the existing unit cutoff -- by the existing proper
domain bound, for the standard test and for the Weyl transform alike -- so equality of their
real values is equality of the `ENNReal` values themselves.  The cutoff-normalized functional
multiplies by a fixed scalar and divides by a fixed cutoff mass, and therefore agrees as well.

Negative scope: no Haar, cutoff, subgroup, chart, section or decomposition is introduced, and
nothing is rescaled.  This is one functional evaluated at two tests, not a comparison of two
functionals: nothing here touches the Eisenstein side, the shell agreement, or a Tamagawa
number, and no value of `t_V` is claimed.  With the existing origin separation this makes the
separation identity `(t_V - 1) * (Phi 0 - (W Phi) 0) = 0` non-vacuous only once the shell
agreement is also available.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing nonnegative Weyl-transform test is measurable. -/
theorem measurable_weylStandardTestENNReal
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    Measurable (L.weylStandardTestENNReal a) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  unfold weylStandardTestENNReal
  exact
    ((L.measurable_rationalAdeleRankOneWeylOperator_polarGaussianLattice hb).norm).ennreal_ofReal

/-- The descended nonnegative theta of the Weyl transform is finite on the whole left quotient,
by the existing proper domain bound. -/
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_weylStandard_ne_top
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
        (L.weylStandardTestENNReal a) Z ≠ ⊤ :=
  ne_top_of_le_ne_top
    (L.properThetaBound_ne_top inst
      (fun g ↦ L.concreteSpecialOrthogonalTheta_weylStandard_ne_top hn ha g))
    (L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_le_properThetaBound
      (fun h x ↦ L.weylStandardTestENNReal_concreteStabilizer_mulVec ha h x) inst Z)

/-- The layer agreement at the Weyl transform: its complex cutoff integral is the real value of
the existing nonnegative cutoff integral of the existing nonnegative Weyl-transform test. -/
theorem complexCutoffIntegral_weylStandard_eq_ofReal_toReal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) f =
      (((L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (L.weylStandardTestENNReal a) f).toReal : ℝ) : ℂ) := by
  have hcoe : (fun y ↦ (((L.weylStandardTestENNReal a y).toReal : ℝ) : ℂ)) =
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) := by
    funext y
    exact L.weylStandardTestENNReal_toReal ha y
  rw [← hcoe]
  exact L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_ofReal_toReal _
    (fun _ ↦ ENNReal.ofReal_ne_top) (L.measurable_weylStandardTestENNReal ha)
    (fun Z ↦ L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_weylStandard_ne_top hn ha inst Z)
    f hf

/-- The covariance in the nonnegative layer, in real values: the raw cutoff integrals of the
existing nonnegative standard test and of the existing nonnegative Weyl-transform test have the
same real value. -/
theorem toReal_thetaLogCutoffIntegral_weylStandard_eq_standard
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (L.weylStandardTestENNReal a) f).toReal =
      (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) f).toReal := by
  have h := (L.complexCutoffIntegral_weylStandard_eq_ofReal_toReal hn ha inst f hf).symm.trans
    (L.complexCutoffIntegral_weyl_polarGaussianLatticeTest_eq_standard hn ha f hf)
  exact_mod_cast h

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Raw finiteness for the Weyl transform against the existing unit cutoff. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_weylStandard_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral (L.weylStandardTestENNReal a)
        rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_ne_top_of_thetaOnLeftQuotient_le
    hr inst hP hconv _
    (L.properThetaBound_ne_top inst
      (fun g ↦ L.concreteSpecialOrthogonalTheta_weylStandard_ne_top (by omega) ha g))
    (fun Z ↦ L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_le_properThetaBound
      (fun h x ↦ L.weylStandardTestENNReal_concreteStabilizer_mulVec ha h x) inst Z)

/-- The covariance in the nonnegative layer: the raw cutoff integrals themselves agree, both
being finite. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_weylStandard_eq_standard
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral (L.weylStandardTestENNReal a)
        rationalIdeleClassUnitLogCutoff =
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff :=
  (ENNReal.toReal_eq_toReal_iff'
    (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_weylStandard_ne_top
      hr inst hP hconv ha)
    (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top
      hr inst hP hconv ha)).1
    (L.toReal_thetaLogCutoffIntegral_weylStandard_eq_standard (by omega) ha inst
      rationalIdeleClassUnitLogCutoff measurable_rationalIdeleClassUnitLogCutoff)

/-- `I_V(Phi) = I_V(W Phi)`: the cutoff-normalized functional takes the same value at the
standard test and at its polar Weyl transform.  This is one functional at two tests; nothing
here compares two functionals. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_eq_standard
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (L.weylStandardTestENNReal a) rationalIdeleClassUnitLogCutoff =
      L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hP hconv
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff := by
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
  rw [L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_weylStandard_eq_standard
    hr inst hP hconv ha]

/-- The separation precursor.  Expanding the same cutoff-normalized functional at the two tests
through the existing target shape turns `I_V(Phi) = I_V(W Phi)` into a statement relating the
origin deviation, weighted by the intrinsic Spin quantity, to the shell deviation.  The standard
test is one at the origin, so only the Weyl transform's origin value appears.

This is exactly the point where the shell agreement is needed: without it the shell sums on the
two sides are not known to cancel, and no conclusion about the intrinsic Spin quantity follows. -/
theorem spinTamagawaNumberENNReal_mul_weylStandardTestENNReal_zero_add_representedNorm_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal *
          L.weylStandardTestENNReal a 0 +
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hP hconv b (L.weylStandardTestENNReal a)
            rationalIdeleClassUnitLogCutoff =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal +
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hP hconv b
            (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
            rationalIdeleClassUnitLogCutoff := by
  rw [← L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
      hr inst hP hconv _ (L.measurable_weylStandardTestENNReal ha) _
      measurable_rationalIdeleClassUnitLogCutoff
      rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top,
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_weylStandard_eq_standard
      hr inst hP hconv ha,
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_standard_eq hr inst hP hconv a]

end PositiveDefiniteIntegralLattice

end
