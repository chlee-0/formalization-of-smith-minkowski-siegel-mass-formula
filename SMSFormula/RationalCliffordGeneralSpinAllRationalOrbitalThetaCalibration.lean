import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormNormalizedContribution
import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormCoefficient

/-!
# Section-free orbital calibration of the normalized quotient theta

The normalized contribution of a represented nonzero rational norm is divided
by its positive finite Spin coefficient to define an intrinsic orbital
functional.  Any supplied complement-lattice calibration identifies this
functional with the auxiliary shell integral multiplied by the exact
ambient-to-lower horizontal scalar ratio.  The shell measure itself is not
made intrinsic.

The ordinary quotient theta is then reassembled as its zero value plus the
sum of these orbital functionals times the unique Spin coefficients.  This is
a measure-level identity, not a pointwise equality with the weighted theta
function.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Every certified raw Spin datum on a rank-at-least-three integral lattice
has finite quotient volume.  A lattice datum supplies one finite
normalization, and fixed-matrix raw uniqueness transfers finiteness to the
given datum. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.spinTamagawaNumberENNReal_ne_top_of_integralLattice
    {m : ℕ} (L : PositiveDefiniteIntegralLattice m) (hm : 3 ≤ m)
    (D : L.rationalQuadraticSpaceMatrix
      |>.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinTamagawaNumberENNReal ≠ ⊤ := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
  letI : Nonempty (Fin (t + 3)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  let inst : Fintype L.ConcreteProperRationalDoubleCosetSet := inferInstance
  obtain ⟨P, hP, hconv⟩ :=
    L.exists_pos_massLocalInverseProductTendsTo
      (by omega : 3 ≤ t + 3)
  let E := PositiveDefiniteIntegralLattice.cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ t + 3) inst hP hconv
  have hrelative : E.IsOnoRelativeTamagawaComparison := by
    simpa only [E] using
      L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) inst hP hconv
  rw [D.spinTamagawaNumberENNReal_eq E]
  exact E.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison hrelative

/-- The unique represented-norm Spin coefficient is nonzero whenever the
ambient raw Spin volume is finite. -/
theorem representedNormOneShellSpinTamagawaCoefficient_ne_zero
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hAmbientFinite : DAmbient.spinTamagawaNumberENNReal ≠ ⊤)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (a : V.RepresentedNonzeroRationalNorm) :
    V.representedNormOneShellSpinTamagawaCoefficient
        DAmbient hLocal a ≠ 0 := by
  exact (hLocal.coefficientWitness a).elim fun w ↦ by
    rw [V.representedNormOneShellSpinTamagawaCoefficient_eq_witness
      DAmbient hLocal a w]
    change
      w.lowerRawData.spinTamagawaNumberENNReal /
          DAmbient.spinTamagawaNumberENNReal ≠ 0
    exact ENNReal.div_ne_zero.mpr
      ⟨w.lowerRawData.spinTamagawaNumberENNReal_ne_zero, hAmbientFinite⟩

/-- The unique represented-norm Spin coefficient is finite. -/
theorem representedNormOneShellSpinTamagawaCoefficient_ne_top
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (a : V.RepresentedNonzeroRationalNorm) :
    V.representedNormOneShellSpinTamagawaCoefficient
        DAmbient hLocal a ≠ ⊤ := by
  exact (hLocal.coefficientWitness a).elim fun w ↦ by
    rw [V.representedNormOneShellSpinTamagawaCoefficient_eq_witness
      DAmbient hLocal a w]
    change
      w.lowerRawData.spinTamagawaNumberENNReal /
          DAmbient.spinTamagawaNumberENNReal ≠ ⊤
    exact ENNReal.div_ne_top
      (w.lowerRawData.spinTamagawaNumberENNReal_ne_top_of_integralLattice
        w.lowerLattice w.lowerRank_atLeastThree)
      DAmbient.spinTamagawaNumberENNReal_ne_zero

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r s : ℕ}

noncomputable local instance orbitalCalibrationTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance orbitalCalibrationTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

/-- The intrinsic normalized orbital functional of one represented nonzero
norm.  It is defined from the fixed quotient integral and the unique positive
finite Spin coefficient, without a complement witness. -/
noncomputable def probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo
      A ambientCutoffProduct)
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    A (by omega) instA hAmbientCutoffProduct hconvA
  A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      hr instA hAmbientCutoffProduct hconvA a Phi f /
    (A.rationalQuadraticSpaceMatrix
      |>.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a)

/-- The intrinsic orbital factor times the unique Spin coefficient recovers
the normalized represented-norm quotient contribution exactly. -/
theorem probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor_mul_coefficient
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo
      A ambientCutoffProduct)
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) :
    let V := A.rationalQuadraticSpaceMatrix
    let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      A (by omega) instA hAmbientCutoffProduct hconvA
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
        hr instA hAmbientCutoffProduct hconvA hLocal a Phi f *
      V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a =
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      hr instA hAmbientCutoffProduct hconvA a Phi f := by
  let V := A.rationalQuadraticSpaceMatrix
  let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    A (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  let coefficient :=
    V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a
  have hrelative : DAmbient.IsOnoRelativeTamagawaComparison := by
    simpa only [DAmbient] using
      A.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) instA hAmbientCutoffProduct hconvA
  have hcoefficient_ne_zero : coefficient ≠ 0 :=
    V.representedNormOneShellSpinTamagawaCoefficient_ne_zero
      DAmbient
      (DAmbient.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison
        hrelative)
      hLocal a
  have hcoefficient_ne_top : coefficient ≠ ⊤ :=
    V.representedNormOneShellSpinTamagawaCoefficient_ne_top
      DAmbient hLocal a
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
  dsimp only
  exact ENNReal.div_mul_cancel hcoefficient_ne_zero hcoefficient_ne_top

/-- Every supplied local complement calibration evaluates the intrinsic
orbital factor as the auxiliary shell integral times the exact
ambient-to-lower horizontal scalar ratio. -/
theorem probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor_eq_horizontalRatio_mul_shell
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo
      A ambientCutoffProduct)
    (L : PositiveDefiniteIntegralLattice (s + 2)) [Nonempty (Fin (s + 2))]
    (hs : 1 ≤ s)
    (instL : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {lowerCutoffProduct : ℝ}
    (hLowerCutoffProduct : 0 < lowerCutoffProduct)
    (hconvL : massLocalInverseProductTendsTo
      L lowerCutoffProduct)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber A.rationalQuadraticSpaceMatrix)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm
        |>.orthogonalRestriction x.1))
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    let V := A.rationalQuadraticSpaceMatrix
    let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
    let ambientHorizontalScalar :=
      A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instA hAmbientCutoffProduct hconvA
    let lowerHorizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instL hLowerCutoffProduct hconvL
    let ambientShellIntegral :=
      ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure
        (by rw [x.property]; exact a.property.1)
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
        hr instA hAmbientCutoffProduct hconvA hLocal a Phi f =
      ((ambientHorizontalScalar : ℝ≥0∞) /
          (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral := by
  let V := A.rationalQuadraticSpaceMatrix
  let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    A (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
  let ambientHorizontalScalar :=
    A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  let lowerHorizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ s + 2) instL hLowerCutoffProduct hconvL
  let ambientShellIntegral : ℝ≥0∞ :=
    ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure
      (by rw [x.property]; exact a.property.1)
  let coefficient :=
    V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a
  let normalizedContribution :=
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      hr instA hAmbientCutoffProduct hconvA a Phi f
  have hrelative : DAmbient.IsOnoRelativeTamagawaComparison := by
    simpa only [DAmbient] using
      A.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) instA hAmbientCutoffProduct hconvA
  have hcoefficient_ne_zero : coefficient ≠ 0 :=
    V.representedNormOneShellSpinTamagawaCoefficient_ne_zero
      DAmbient
      (DAmbient.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison
        hrelative)
      hLocal a
  have hcoefficient_ne_top : coefficient ≠ ⊤ :=
    V.representedNormOneShellSpinTamagawaCoefficient_ne_top
      DAmbient hLocal a
  have hnormalized :
      normalizedContribution =
        (((ambientHorizontalScalar : ℝ≥0∞) /
            (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral) *
          coefficient := by
    simpa only [V, DAmbient, P, ambientHorizontalScalar,
      lowerHorizontalScalar, ambientShellIntegral, coefficient,
      normalizedContribution] using
      A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_horizontalRatio_mul_shell_mul_coefficient
        hr instA hAmbientCutoffProduct hconvA L hs instL
          hLowerCutoffProduct hconvL a x e hLocal Phi hPhi f hf
          hcutoffMass_ne_zero hcutoffMass_ne_top
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
  dsimp only
  change normalizedContribution / coefficient =
    ((ambientHorizontalScalar : ℝ≥0∞) /
      (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral
  apply Eq.symm
  apply (ENNReal.eq_div_iff hcoefficient_ne_zero hcoefficient_ne_top).2
  rw [hnormalized]
  ac_rfl

/-- Section-free orbital reassembly of the probability-normalized ordinary
quotient theta. -/
theorem probabilityNormalizedFullAdelicCliffordGeneralSpinTheta_eq_zero_add_orbitalFactor_mul_coefficient
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo
      A ambientCutoffProduct)
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    let V := A.rationalQuadraticSpaceMatrix
    let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      A (by omega) instA hAmbientCutoffProduct hconvA
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
        hr instA hAmbientCutoffProduct hconvA Phi f =
      Phi 0 +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor
              hr instA hAmbientCutoffProduct hconvA hLocal a Phi f *
            V.representedNormOneShellSpinTamagawaCoefficient
              DAmbient hLocal a := by
  let V := A.rationalQuadraticSpaceMatrix
  let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    A (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  rw [A.probabilityNormalizedFullAdelicCliffordGeneralSpinTheta_eq_zero_add_representedNorm
    hr instA hAmbientCutoffProduct hconvA Phi hPhi f hf
      hcutoffMass_ne_zero hcutoffMass_ne_top]
  congr 1
  apply tsum_congr
  intro a
  symm
  simpa only [V, DAmbient] using
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormOrbitalFactor_mul_coefficient
      hr instA hAmbientCutoffProduct hconvA hLocal a Phi f

end PositiveDefiniteIntegralLattice

end
