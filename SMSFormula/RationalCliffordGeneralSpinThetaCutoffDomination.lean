import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedStandardTest

/-!
# Finiteness by domination, so each new test needs only a comparison

The cutoff-normalized layer needs the raw theta cutoff integral of the chosen test to be
finite.  That is proved for the standard polar Gaussian--lattice test; for any further test
it should not have to be reproved from scratch.

The raw integral is monotone in the test -- the theta is a `tsum` of test values, `withDensity`
is monotone in its density, and `lintegral` is monotone in its measure -- and it is homogeneous
under multiplying the test by a constant.  So a test dominated by a finite multiple of a test
with finite raw integral has finite raw integral itself, and the whole cutoff-normalized layer
applies to it.

Specialized to the standard test, this reduces finiteness for any new test to a
pointwise domination check.

Scope: domination is a real hypothesis and is supplied for no new test here.  In
particular the Weyl transform of the standard test is not claimed to be dominated by a multiple
of it; its carrier conditions are swapped, so that comparison must be proved where it is wanted.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The theta function is monotone in the test. -/
theorem fullAdelicCliffordGeneralSpinTheta_mono
    (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞} (h : Phi ≤ Psi)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinTheta Phi g ≤
      V.fullAdelicCliffordGeneralSpinTheta Psi g :=
  ENNReal.tsum_le_tsum fun _ => h _

/-- Monotonicity descends to the left quotient. -/
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_mono
    (V : RationalQuadraticSpaceMatrix n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞} (h : Phi ≤ Psi) :
    V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi ≤
      V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Psi := by
  intro Z
  induction Z using Quot.ind with
  | _ g => exact V.fullAdelicCliffordGeneralSpinTheta_mono h g

/-- The theta function is homogeneous in the test. -/
theorem fullAdelicCliffordGeneralSpinTheta_const_mul
    (V : RationalQuadraticSpaceMatrix n) (c : ℝ≥0∞)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinTheta (fun x => c * Phi x) g =
      c * V.fullAdelicCliffordGeneralSpinTheta Phi g :=
  ENNReal.tsum_mul_left

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The raw theta cutoff integral is monotone in the test. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_mono
    (L : PositiveDefiniteIntegralLattice n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞} (h : Phi ≤ Psi)
    (f : ℝ → ℝ≥0∞) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≤
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Psi f := by
  have hq := L.rationalQuadraticSpaceMatrix
    |>.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_mono h
  unfold fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
  dsimp only
  exact lintegral_mono' (withDensity_mono (Filter.Eventually.of_forall fun Z => hq Z)) le_rfl

/-- The raw theta cutoff integral is homogeneous in the test. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_const_mul
    (L : PositiveDefiniteIntegralLattice n) (c : ℝ≥0∞)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) (hPhi : Measurable Phi) (f : ℝ → ℝ≥0∞) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral (fun x => c * Phi x) f =
      c * L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f := by
  have hdens : L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
      (fun x => c * Phi x) =
      c • L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi := by
    funext Z
    induction Z using Quot.ind with
    | _ g =>
      show L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta
          (fun x => c * Phi x) g =
        c * L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta Phi g
      exact L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinTheta_const_mul c Phi g
  have hmeas : Measurable
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi) :=
    L.rationalQuadraticSpaceMatrix.measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
      Phi hPhi
  unfold fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
  dsimp only
  rw [hdens, withDensity_smul c hmeas, lintegral_smul_measure, smul_eq_mul]

/-- Finiteness by domination. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_ne_top_of_le_const_mul
    (L : PositiveDefiniteIntegralLattice n)
    {Phi Psi : (Fin n → RationalAdele) → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hPsi : Measurable Psi) (hle : Phi ≤ fun x => c * Psi x) (f : ℝ → ℝ≥0∞)
    (hfin : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Psi f ≠ ⊤) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_
    (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_mono hle f)
  rw [L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_const_mul c Psi hPsi f]
  exact ENNReal.mul_ne_top hc hfin

/-- The practical form: for the existing unit cutoff, any test dominated by a finite multiple of
the standard polar Gaussian--lattice test has a finite cutoff-normalized functional, so the whole
layer applies to it. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top_of_le_const_mul_standard
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    {a : ℝ} (ha : 0 < a)
    (hle : Phi ≤ fun x => c * rationalAdeleVectorPolarGaussianLatticeTestENNReal L a x) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv Phi
        rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top hr inst hcutoffProduct hconv _ _
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_ne_top_of_le_const_mul hc
      (L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal a) hle _
      (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top
        hr inst hcutoffProduct hconv ha))

end PositiveDefiniteIntegralLattice

end
