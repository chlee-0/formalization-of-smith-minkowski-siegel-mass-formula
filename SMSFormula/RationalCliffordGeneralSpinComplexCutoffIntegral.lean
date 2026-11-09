import SMSFormula.RationalCliffordGeneralSpinComplexThetaQuotientIntegrable

/-!
# The complex cutoff integral: linearity, and agreement with the nonnegative one

The complex theta descends to the `GSpin` left quotient and is Bochner integrable against the
cutoff-weighted quotient measure, so the complex-valued cutoff integral is available.  This
file records the two properties that the nonnegative layer cannot have.

Linearity.  The theta is a `tsum` of test values, so it is additive on tests whose families are
absolutely summable and homogeneous under a complex scalar with no hypothesis at all; both
descend to the quotient and pass through the Bochner integral.  `ENNReal` has no subtraction, so
this is exactly the structure a difference of functionals needs.

Agreement.  For a nonnegative test with finite values and finite theta, the complex cutoff
integral of its real coercion is the real value of the existing nonnegative cutoff integral.  So
the complex object is an extension, not a new normalization, and everything already proved about
the nonnegative cutoff integral transfers to it on such tests.

Negative scope: no covariance, no Poisson identity, no Fourier inversion, and no comparison
between a test and its Weyl transform.  Linearity relates a functional to itself at different
tests; it never evaluates one.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Additivity of the complex theta on absolutely summable tests. -/
theorem fullAdelicCliffordGeneralSpinComplexTheta_add
    (V : RationalQuadraticSpaceMatrix n) {Phi Psi : (Fin n → RationalAdele) → ℂ}
    {g : V.FullAdelicCliffordGeneralSpinGroup}
    (hPhi : Summable (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g))
    (hPsi : Summable (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Psi g)) :
    V.fullAdelicCliffordGeneralSpinComplexTheta (fun y ↦ Phi y + Psi y) g =
      V.fullAdelicCliffordGeneralSpinComplexTheta Phi g +
        V.fullAdelicCliffordGeneralSpinComplexTheta Psi g :=
  hPhi.tsum_add hPsi

/-- Homogeneity of the complex theta, with no summability hypothesis. -/
theorem fullAdelicCliffordGeneralSpinComplexTheta_const_smul
    (V : RationalQuadraticSpaceMatrix n) (c : ℂ) (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinComplexTheta (fun y ↦ c * Phi y) g =
      c * V.fullAdelicCliffordGeneralSpinComplexTheta Phi g :=
  tsum_mul_left

/-- Additivity on the left quotient. -/
theorem fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_add
    (V : RationalQuadraticSpaceMatrix n) {Phi Psi : (Fin n → RationalAdele) → ℂ}
    (hPhi : ∀ g, Summable
      (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g))
    (hPsi : ∀ g, Summable
      (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Psi g))
    (Z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient (fun y ↦ Phi y + Psi y) Z =
      V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi Z +
        V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Psi Z := by
  induction Z using Quot.inductionOn with
  | _ g => exact V.fullAdelicCliffordGeneralSpinComplexTheta_add (hPhi g) (hPsi g)

/-- Homogeneity on the left quotient. -/
theorem fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_const_smul
    (V : RationalQuadraticSpaceMatrix n) (c : ℂ) (Phi : (Fin n → RationalAdele) → ℂ)
    (Z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient (fun y ↦ c * Phi y) Z =
      c * V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi Z := by
  induction Z using Quot.inductionOn with
  | _ g => exact V.fullAdelicCliffordGeneralSpinComplexTheta_const_smul c Phi g

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The complex cutoff integral: the Bochner integral of the descended complex theta against the
existing cutoff-weighted quotient measure. -/
def complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
    (L : PositiveDefiniteIntegralLattice n) (Phi : (Fin n → RationalAdele) → ℂ) (f : ℝ → ℝ≥0∞) : ℂ :=
  ∫ Z,
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi Z
  ∂(L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure f)

/-- Additivity of the complex cutoff integral on integrable tests. -/
theorem complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_add
    (L : PositiveDefiniteIntegralLattice n) {Phi Psi : (Fin n → RationalAdele) → ℂ} (f : ℝ → ℝ≥0∞)
    (hPhi : ∀ g, Summable ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g))
    (hPsi : ∀ g, Summable ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Psi g))
    (hiPhi : Integrable
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi)
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure f))
    (hiPsi : Integrable
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Psi)
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure f)) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral (fun y ↦ Phi y + Psi y) f =
      L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral Phi f +
        L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral Psi f := by
  unfold complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
  rw [← integral_add hiPhi hiPsi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun Z ↦
    (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_add
      hPhi hPsi Z)

/-- Homogeneity of the complex cutoff integral. -/
theorem complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_const_smul
    (L : PositiveDefiniteIntegralLattice n) (c : ℂ) (Phi : (Fin n → RationalAdele) → ℂ) (f : ℝ → ℝ≥0∞) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral (fun y ↦ c * Phi y) f =
      c * L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral Phi f := by
  unfold complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun Z ↦
    (L.rationalQuadraticSpaceMatrix)
      |>.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_const_smul c Phi Z)

/-! ## Agreement with the existing nonnegative cutoff integral -/

/-- Pointwise on the quotient: the complex theta of the real coercion of a finite-valued
nonnegative test is the coercion of the real value of its nonnegative theta. -/
theorem fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_ofReal_toReal
    (L : PositiveDefiniteIntegralLattice n) (PhiENN : (Fin n → RationalAdele) → ℝ≥0∞)
    (hval : ∀ y, PhiENN y ≠ ⊤)
    (hfin : ∀ Z, (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN Z ≠ ⊤)
    (Z : (L.rationalQuadraticSpaceMatrix).FullAdelicCliffordGeneralSpinLeftQuotient) :
    (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient
        (fun y ↦ (((PhiENN y).toReal : ℝ) : ℂ)) Z =
      ((((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
        PhiENN Z).toReal : ℝ) : ℂ) := by
  induction Z using Quot.inductionOn with
  | _ g =>
      have hne : (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinTheta PhiENN g ≠ ⊤ :=
        hfin ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinLeftQuotientMap g)
      have hsum : Summable (fun x : Fin n → ℚ ↦
          (PhiENN ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinRationalVectorAction g x)).toReal) :=
        ENNReal.summable_toReal hne
      have hreal : ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinTheta PhiENN g).toReal =
          ∑' x : Fin n → ℚ,
            (PhiENN ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinRationalVectorAction g x)).toReal :=
        ENNReal.tsum_toReal_eq fun x ↦ hval _
      show (∑' x : Fin n → ℚ,
          (((PhiENN ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinRationalVectorAction g x)).toReal : ℝ) : ℂ)) =
        ((((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinTheta PhiENN g).toReal : ℝ) : ℂ)
      rw [hreal]
      exact (Complex.ofRealCLM.map_tsum hsum).symm

/-- The agreement: on the real coercion of a finite-valued nonnegative test with finite quotient
theta, the complex cutoff integral is the real value of the existing nonnegative one. -/
theorem complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_ofReal_toReal
    (L : PositiveDefiniteIntegralLattice n) (PhiENN : (Fin n → RationalAdele) → ℝ≥0∞)
    (hval : ∀ y, PhiENN y ≠ ⊤) (hmeas : Measurable PhiENN)
    (hfin : ∀ Z, (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN Z ≠ ⊤)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (fun y ↦ (((PhiENN y).toReal : ℝ) : ℂ)) f =
      (((L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral PhiENN f).toReal : ℝ) : ℂ) := by
  set V := L.rationalQuadraticSpaceMatrix with hV
  set mu := V.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure f with hmu
  have hthetaMeas : Measurable (V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN) :=
    V.measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN hmeas
  unfold complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
  rw [L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_eq_lintegral_cutoffQuotientMeasure
    PhiENN hmeas f hf]
  calc
    (∫ Z, V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient
        (fun y ↦ (((PhiENN y).toReal : ℝ) : ℂ)) Z ∂mu) =
        ∫ Z, (((V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN Z).toReal : ℝ) : ℂ)
          ∂mu := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun Z ↦
        L.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_ofReal_toReal
          PhiENN hval hfin Z)
    _ = (((∫ Z, (V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN Z).toReal ∂mu : ℝ)) : ℂ) :=
      integral_ofReal
    _ = (((∫⁻ Z, V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient PhiENN Z ∂mu).toReal : ℝ) : ℂ) := by
      rw [integral_toReal hthetaMeas.aemeasurable
        (Filter.Eventually.of_forall fun Z ↦ lt_top_iff_ne_top.2 (hfin Z))]

/-- Non-vacuous: at the standard test the agreement is an identity between the complex cutoff
integral of the existing complex test and the existing nonnegative one. -/
theorem complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_standard
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) f =
      (((L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) f).toReal : ℝ) : ℂ) := by
  have hcoe : (fun y ↦
      (((rationalAdeleVectorPolarGaussianLatticeTestENNReal L a y).toReal : ℝ) : ℂ)) =
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) := by
    funext y
    exact L.rationalAdeleVectorPolarGaussianLatticeTestENNReal_toReal a y
  have hfin : ∀ Z, (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
      (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) Z ≠ ⊤ := by
    intro Z
    induction Z using Quot.inductionOn with
    | _ g => exact L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeTheta_ne_top ha g
  rw [← hcoe]
  exact L.complexFullAdelicCliffordGeneralSpinThetaCutoffIntegral_ofReal_toReal _
    (fun y ↦ rationalAdeleVectorPolarGaussianLatticeTestENNReal_ne_top L a y)
    (L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal a) hfin f hf

end PositiveDefiniteIntegralLattice

end
