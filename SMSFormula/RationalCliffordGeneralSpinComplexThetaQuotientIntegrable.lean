import SMSFormula.RationalCliffordGeneralSpinComplexThetaBound

/-!
# The complex theta descends and is integrable against the cutoff-weighted quotient measure

The complex theta is already uniformly bounded and measurable on the full-adelic `GSpin` group.
This file completes the structural half of the complex layer: the theta is invariant under the
rational diagonal, so it descends to the left quotient exactly as the nonnegative one does; the
uniform bound and the measurability carry across; and the existing horizontal quotient measure
weighted by the existing unit logarithmic cutoff is a finite measure, because that weight already
has finite integral.  A bounded measurable function against a finite measure is integrable.

The weighted measure is not a new cutoff or a new Haar: the existing logarithmic-cutoff integral
of a nonnegative theta is literally the integral of that theta against it, and that
identification is recorded.

Negative scope: integrability is a size statement.  No Poisson identity, no Fourier inversion, no
interchange of the Weyl transform with this integral, and no comparison between the complex theta
of a test and that of its transform is asserted here.
-/

noncomputable section

open Matrix MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complex theta is invariant under the rational `GSpin` diagonal, by the same rational
isometry reindexing that the nonnegative theta uses. -/
theorem fullAdelicCliffordGeneralSpinComplexTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinComplexTheta Phi
        ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g) =
      V.fullAdelicCliffordGeneralSpinComplexTheta Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinComplexTheta
  simp_rw [fullAdelicCliffordGeneralSpinComplexRationalVectorThetaSummand,
    fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul]
  exact
    (V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d.matrixGroup⁻¹)).toEquiv.tsum_eq
      (fun x ↦ Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x))

/-- The complex theta on the existing rational `GSpin` left quotient. -/
def fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → ℂ :=
  Quot.lift (V.fullAdelicCliffordGeneralSpinComplexTheta Phi) (by
    intro g h hrel
    rcases hrel with ⟨delta, rfl⟩
    exact (V.fullAdelicCliffordGeneralSpinComplexTheta_rational_mul Phi delta g).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinComplexTheta Phi g :=
  rfl

/-- The descended complex theta is measurable for the existing map-generated quotient
measurable structure. -/
theorem measurable_fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n) {Phi : (Fin n → RationalAdele) → ℂ}
    (hmeas : Measurable (V.fullAdelicCliffordGeneralSpinComplexTheta Phi)) :
    Measurable (V.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa only [Set.preimage_preimage,
    fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient_mk] using
      (measurable_iff_comap_le.mp hmeas)
        ((V.fullAdelicCliffordGeneralSpinComplexTheta Phi) ⁻¹' t) ⟨t, ht, rfl⟩

/-- The existing horizontal quotient measure weighted by a cutoff of the existing logarithmic
module.  No new quotient, Haar or cutoff is introduced. -/
def fullAdelicCliffordGeneralSpinCutoffQuotientMeasure
    (V : RationalQuadraticSpaceMatrix n) (f : ℝ → ℝ≥0∞) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  (V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure).withDensity
    (fun Z ↦ f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z))

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Consistency: the existing logarithmic-cutoff integral of a nonnegative theta is literally the
integral of that theta against the cutoff-weighted quotient measure. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_eq_lintegral_cutoffQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n) (Phi : (Fin n → RationalAdele) → ℝ≥0∞) (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f =
      ∫⁻ Z, L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi Z
        ∂(L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure f) := by
  set V := L.rationalQuadraticSpaceMatrix with hV
  have htheta : Measurable (V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi) :=
    V.measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi hPhi
  have hcut : Measurable
      (fun Z ↦ f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)) :=
    hf.comp V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable
  rw [fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral,
    RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure,
    lintegral_withDensity_eq_lintegral_mul _ htheta hcut,
    lintegral_withDensity_eq_lintegral_mul _ hcut htheta]
  exact lintegral_congr fun Z ↦ mul_comm _ _

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The cutoff-weighted quotient measure is finite, because the existing unit logarithmic cutoff
already has finite integral against the horizontal quotient measure. -/
theorem isFiniteMeasure_fullAdelicCliffordGeneralSpinCutoffQuotientMeasure_unit
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    IsFiniteMeasure
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure
        RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff) := by
  refine ⟨?_⟩
  rw [RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lt_top_iff_ne_top.2
    (L.lintegral_horizontalQuotient_unitLogCutoff_ne_top hr inst hP hconv)

/-- The integrability: a complex test whose modulus is stabilizer invariant with pointwise finite
concrete `SO` theta, and which is measurable with pointwise absolutely summable theta, has a
Bochner integrable complex theta on the `GSpin` left quotient against the cutoff-weighted
measure. -/
theorem integrable_fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (Phi : (Fin (r + 2) → RationalAdele) → ℂ)
    (hmeas : Measurable
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexTheta Phi))
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin (r + 2) → RationalAdele),
      complexTestModulusENNReal Phi (h.1.1.1.1.mulVec x) = complexTestModulusENNReal Phi x)
    (hfin : ∀ G : L.ConcreteFullAdelicSpecialOrthogonalGroup,
      L.concreteSpecialOrthogonalTheta (complexTestModulusENNReal Phi) G ≠ ⊤) :
    Integrable
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient Phi)
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinCutoffQuotientMeasure
        RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff) := by
  haveI := L.isFiniteMeasure_fullAdelicCliffordGeneralSpinCutoffQuotientMeasure_unit
    hr inst hP hconv
  have hquot := RationalQuadraticSpaceMatrix.measurable_fullAdelicCliffordGeneralSpinComplexThetaOnLeftQuotient L.rationalQuadraticSpaceMatrix hmeas
  refine Integrable.mono' (integrable_const
      ((L.properThetaBound (complexTestModulusENNReal Phi) inst).toReal))
    (hquot.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun Z ↦ ?_
  induction Z using Quot.inductionOn with
  | _ g =>
      exact L.norm_fullAdelicCliffordGeneralSpinComplexTheta_le_properThetaBound_toReal
        Phi hinv hfin inst g

end PositiveDefiniteIntegralLattice

end
