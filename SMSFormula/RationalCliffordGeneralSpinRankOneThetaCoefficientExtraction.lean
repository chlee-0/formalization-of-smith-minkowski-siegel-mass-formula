import SMSFormula.RationalAdeleRankOneQuadraticPhase
import SMSFormula.RationalCliffordGeneralSpinRepresentedNormThetaQuotient

/-!
# Rank-one coefficient extraction for the actual GSpin theta family

This file specializes the compact-additive-quotient extraction theorem to the
existing inverse `GSpin` action on rational vectors.  The analytic hypothesis
is stated without a surrogate test class: at a given adelic `GSpin` point,
the complex family `x ↦ Phi (g⁻¹ x)` must be summable.

Multiplication by the quadratic character has complex norm one, so this
hypothesis is equivalent to summability of every phase-twisted family.  It
also gives uniform convergence, continuity, and integrability in the
`A/ℚ` parameter.  Rational-left invariance lets both the hypothesis and the
twisted theta descend to the repository's existing `GSpin` quotient.  The
extracted coefficient is the literal section-free represented-norm theta
density on that same quotient.

No quotient representative, Schwartz space, generic Weil representation,
Fourier invariance, or Eisenstein--Siegel functional is introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complex theta summand on the actual full-adelic `GSpin` carrier. -/
def fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ) : ℂ :=
  Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)

/-- Unit-modulus quadratic twisting preserves, and is detected by, the exact
summability hypothesis on the rational theta family. -/
theorem summable_rationalAdeleModRationalCliffordGeneralSpinNormExtractionTerm_iff
    (V : RationalQuadraticSpaceMatrix n)
    (b : ℚ) (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (a : RationalAdeleModRational) :
    Summable (fun x : Fin n → ℚ ↦
      (V.rationalAdeleModRationalNormExtractionPhase b x a : ℂ) *
        V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
          Phi g x) ↔
      Summable
        (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
          Phi g) := by
  constructor
  · intro h
    apply Summable.of_norm
    simpa using h.norm
  · intro h
    apply Summable.of_norm
    simpa using h.norm

set_option maxHeartbeats 800000 in
/-- Absolute summability of the complex rational theta family is invariant
under the rational diagonal and hence is meaningful on the left quotient. -/
theorem summable_fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand_rational_mul_iff
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    Summable
        (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi
          ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g)) ↔
      Summable
        (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
          Phi g) := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
  simp_rw [fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul]
  let e := V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d.matrixGroup⁻¹)
  simpa only [Function.comp_apply] using
    (e.toEquiv.summable_iff
      (f := fun x : Fin n → ℚ ↦
        Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)))

/-- The exact theta summability condition descended to the existing `GSpin`
left quotient.  Its definition selects no representative. -/
def IsSummableFullAdelicCliffordGeneralSpinComplexThetaAtQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → Prop :=
  Quot.lift
    (fun g ↦ Summable
      (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand Phi g))
    (by
      intro g h hrel
      rcases hrel with ⟨delta, rfl⟩
      exact propext
        (V.summable_fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand_rational_mul_iff
          Phi delta g).symm)

@[simp]
theorem isSummableFullAdelicCliffordGeneralSpinComplexThetaAtQuotient_mk
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.IsSummableFullAdelicCliffordGeneralSpinComplexThetaAtQuotient Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) ↔
      Summable
        (V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
          Phi g) :=
  Iff.rfl

/-- The complex represented-norm theta density on the full-adelic group. -/
def fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta
    (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup) : ℂ :=
  ∑' x : b.rationalVectorFiber V,
    V.fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand
      Phi g x.1

theorem fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta b Phi
        ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g) =
      V.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta b Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta
  simp_rw [fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand,
    fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul,
    ← b.rationalGeneralSpinInvFiberEquiv_coe d]
  exact (b.rationalGeneralSpinInvFiberEquiv d).tsum_eq
    (fun x ↦ Phi
      (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1))

/-- The literal complex norm-fiber theta density on the existing quotient. -/
def fullAdelicCliffordGeneralSpinComplexRepresentedNormThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → ℂ :=
  Quot.lift
    (V.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta b Phi)
    (by
      intro g h hrel
      rcases hrel with ⟨delta, rfl⟩
      exact
        (V.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta_rational_mul
          b Phi delta g).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinComplexRepresentedNormThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinComplexRepresentedNormThetaOnLeftQuotient
        b Phi (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinComplexRepresentedNormTheta b Phi g :=
  rfl

end RationalQuadraticSpaceMatrix

end
