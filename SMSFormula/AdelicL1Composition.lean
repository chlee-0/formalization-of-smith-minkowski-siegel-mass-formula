import SMSFormula.GeneralCarrierL1
import SMSFormula.RationalAdeleBruhatIntegralLocalProduct
import SMSFormula.RationalAdeleArchimedeanLocalIntegral

/-!
# Multiplying the two halves

The finite half of `G_b subset L` is closed at every carrier scale and the archimedean modulus is
integrable on the line in every rank above two.  This file supplies the two structural steps that
turn those into `A_Phi in L^1(A)`.

First, the factorization at an arbitrary product test.  The repository already factors the adelic
Bruhat coefficient of the standard test into a real factor times a finite one; the same proof works
for any test of the form `Phi_inf(x_inf) Phi_fin(x_fin)`, because the three inputs it uses -- the
quadratic phase splitting as a real phase times a finite one, the coordinate vectors splitting
measure-preservingly, and mathlib's `integral_prod_mul` -- none of them mention the Gaussian.  The
only thing the standard test contributed was the evaluation of the archimedean factor, which is
dropped here: the statement leaves both local integrals as integrals.  No integrability hypothesis
is needed, since `integral_prod_mul` carries none.

Second, the Tonelli composition.  Given such a factorization with each local factor's `lintegral`
finite, the adelic coefficient is integrable: the adelic Haar is the product of the two local Haars,
so the enorm integral splits as a product of two finite numbers, and measurability of the
coefficient is free from the repository's own continuity of the coefficient at every integrable
test.

And a structural finding worth recording: the conductor route deliberately avoided measurability in
the frequency -- `lintegral_iUnion` asks only that the strata be measurable -- but the Tonelli step
does not avoid it: `lintegral_prod_mul` needs each factor measurable separately.  So the finite
factor's continuity in the frequency, which the chain never needed before, is needed here, and it is
proved by dominated convergence against the indicator of the integral vectors.

Negative scope.  Nothing here evaluates either local integral.  The archimedean factor of a shifted
Gaussian is not identified with any integral -- that remains the naming convention recorded for
`ArchimedeanShiftedCentreBound` -- so `G_b subset L` is not closed by this file; what is closed is
the composition and the standard test's own instance of it.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The factorization at an arbitrary product test -/

/-- The factorization at an arbitrary product test: the adelic Bruhat coefficient of
`Phi_inf(x_inf) Phi_fin(x_fin)` is the archimedean local integral times the finite one.  The
standard test contributed only the evaluation of the archimedean factor, which is dropped. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_productTest
    (V : RationalQuadraticSpaceMatrix n) (a : RationalAdele)
    (PhiInf : (Fin n → ℝ) → ℂ) (PhiFin : (Fin n → RationalFiniteAdele) → ℂ) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun x ↦ PhiInf (rationalAdeleVectorRealPart n x) *
          PhiFin (rationalAdeleVectorFinitePart n x)) a =
      (∫ x : Fin n → ℝ,
          ((Real.fourierChar
              (rationalAdeleRealScalar a * V.realQuadraticFormValue x) : Circle) : ℂ) * PhiInf x
          ∂(volume : Measure (Fin n → ℝ))) *
        (∫ x : Fin n → RationalFiniteAdele,
          ((V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : Circle) : ℂ) * PhiFin x
          ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  set gr : (Fin n → ℝ) → ℂ := fun x ↦
    ((Real.fourierChar
        (rationalAdeleRealScalar a * V.realQuadraticFormValue x) : Circle) : ℂ) * PhiInf x with hgr
  set gf : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦
    ((V.rationalFiniteAdeleQuadraticPhaseAt a.2 x : Circle) : ℂ) * PhiFin x with hgf
  set g : ((Fin n → ℝ) × (Fin n → RationalFiniteAdele)) → ℂ := fun z ↦ gr z.1 * gf z.2 with hg
  have hintegrand :
      (fun x : Fin n → RationalAdele ↦
        (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) *
          (PhiInf (rationalAdeleVectorRealPart n x) *
            PhiFin (rationalAdeleVectorFinitePart n x))) =
        fun x ↦ g (rationalAdeleVectorRealFiniteEquiv n x) := by
    funext x
    rw [V.rationalAdeleRankOneQuadraticPhase_eq_real_mul_finiteAt]
    simp only [hg, hgr, hgf, rationalAdeleVectorRealFiniteEquiv_apply]
    ring
  rw [rationalAdeleRankOneAdelicBruhatCoefficient,
    rationalAdeleRankOneWeylOperator, Fourier.fourierIntegral_def]
  simp only [Matrix.mulVec_zero, mul_zero, neg_zero,
    rationalAdeleRankOneUnipotentOperator]
  rw [AddChar.map_zero_eq_one]
  simp only [one_smul]
  rw [hintegrand,
    (measurePreserving_rationalAdeleVectorRealFiniteSplit n).integral_comp' g,
    MeasureTheory.integral_prod_mul]

/-! ## The Tonelli composition -/

/-- The Tonelli composition: a factorized adelic Bruhat coefficient whose two local factors have
finite `lintegral` is integrable over the adeles.  Measurability of the coefficient is free from the
repository's own continuity at every integrable test; the two factors' measurability is what
`lintegral_prod_mul` consumes and is not free. -/
theorem integrable_adelicBruhatCoefficient_of_localFactors
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n))
    (R : RationalInfiniteAdele → ℂ) (F : RationalFiniteAdele → ℂ)
    (hfact : ∀ u : RationalAdele,
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u = R u.1 * F u.2)
    (hRmeas : AEMeasurable (fun w ↦ ENNReal.ofReal ‖R w‖) rationalInfiniteAdeleAddHaarMeasure)
    (hFmeas : AEMeasurable (fun y ↦ ENNReal.ofReal ‖F y‖) rationalFiniteAdeleAddHaarMeasure)
    (hR : ∫⁻ w, ENNReal.ofReal ‖R w‖ ∂rationalInfiniteAdeleAddHaarMeasure < ⊤)
    (hF : ∫⁻ y, ENNReal.ofReal ‖F y‖ ∂rationalFiniteAdeleAddHaarMeasure < ⊤) :
    Integrable (V.rationalAdeleRankOneAdelicBruhatCoefficient Phi)
      rationalAdeleAddHaarMeasure := by
  refine ⟨(V.continuous_rationalAdeleRankOneAdelicBruhatCoefficient Phi hPhi).aestronglyMeasurable,
    ?_⟩
  have hpt : ∀ u : RationalAdele,
      ENNReal.ofReal ‖V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u‖ =
        ENNReal.ofReal ‖R u.1‖ * ENNReal.ofReal ‖F u.2‖ := by
    intro u
    rw [hfact u, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  have hsplit : ∫⁻ u, ENNReal.ofReal ‖V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u‖
        ∂rationalAdeleAddHaarMeasure =
      (∫⁻ w, ENNReal.ofReal ‖R w‖ ∂rationalInfiniteAdeleAddHaarMeasure) *
        ∫⁻ y, ENNReal.ofReal ‖F y‖ ∂rationalFiniteAdeleAddHaarMeasure := by
    simp only [hpt]
    rw [rationalAdeleAddHaarMeasure_eq_prod]
    exact lintegral_prod_mul hRmeas hFmeas
  rw [hasFiniteIntegral_iff_enorm]
  simp only [← ofReal_norm_eq_enorm]
  rw [hsplit]
  exact ENNReal.mul_lt_top hR hF

/-! ## The archimedean half, on the infinite adeles -/

/-- The infinite-adelic `lintegral` is the Lebesgue one -- the companion of the repository's own
Bochner transport, proved the same way. -/
theorem lintegral_infiniteAdele_eq_lintegral_real (F : RationalInfiniteAdele → ℝ≥0∞) :
    (∫⁻ w, F w ∂rationalInfiniteAdeleAddHaarMeasure) =
      ∫⁻ v : ℝ, F (rationalInfiniteAdeleContinuousAddEquivReal.symm v) := by
  rw [rationalInfiniteAdeleAddHaarMeasure]
  exact lintegral_map_equiv F
    rationalInfiniteAdeleContinuousAddEquivReal.symm.toHomeomorph.toMeasurableEquiv

/-- The archimedean factor's modulus is measurable, through the repository's own modulus formula:
the complex power never has to be handled, only the square root of a norm. -/
theorem aemeasurable_norm_archimedeanFactor (L : PositiveDefiniteIntegralLattice n) (c : ℝ) :
    AEMeasurable (fun w : RationalInfiniteAdele ↦
      ENNReal.ofReal ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
          Complex.I) ^ (1 / 2 : ℂ)) ^ n‖)
      rationalInfiniteAdeleAddHaarMeasure := by
  have hpt : ∀ w : RationalInfiniteAdele,
      ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
          Complex.I) ^ (1 / 2 : ℂ)) ^ n‖ =
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) -
          ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) * Complex.I‖)⁻¹ ^ n :=
    fun w ↦ norm_archimedeanBruhatFactor L c _
  simp only [hpt]
  refine Measurable.aemeasurable ?_
  refine ENNReal.measurable_ofReal.comp ?_
  refine measurable_const.mul ?_
  have hequiv : Measurable (fun w : RationalInfiniteAdele ↦
      (rationalInfiniteAdeleContinuousAddEquivReal w : ℝ)) :=
    rationalInfiniteAdeleContinuousAddEquivReal.continuous.measurable
  have hcont : Continuous fun v : ℝ ↦ ‖(c : ℂ) - (v : ℂ) * Complex.I‖ := by fun_prop
  exact ((((Real.continuous_sqrt.comp hcont).measurable.inv).pow_const n).comp hequiv)

/-- The archimedean half on the infinite adeles: the factor's `lintegral` is finite above rank
two, transported from the repository's own integrable majorant on the line. -/
theorem lintegral_norm_archimedeanFactor_lt_top (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) :
    ∫⁻ w, ENNReal.ofReal ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
          Complex.I) ^ (1 / 2 : ℂ)) ^ n‖
      ∂rationalInfiniteAdeleAddHaarMeasure < ⊤ := by
  rw [lintegral_infiniteAdele_eq_lintegral_real]
  have hpt : ∀ v : ℝ,
      ENNReal.ofReal ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((c : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal
            (rationalInfiniteAdeleContinuousAddEquivReal.symm v) : ℝ) : ℂ) *
          Complex.I) ^ (1 / 2 : ℂ)) ^ n‖ =
      ENNReal.ofReal ((L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n) := by
    intro v
    rw [show (rationalInfiniteAdeleContinuousAddEquivReal
        (rationalInfiniteAdeleContinuousAddEquivReal.symm v) : ℝ) = v from by simp,
      norm_archimedeanBruhatFactor L c v]
  simp only [hpt]
  have hint : Integrable (fun v : ℝ ↦ (L.polarRealDeterminantScale : ℝ)⁻¹ *
      (Real.sqrt ‖(c : ℂ) - (v : ℂ) * Complex.I‖)⁻¹ ^ n) (volume : Measure ℝ) :=
    (integrable_archimedeanBound hc hn).const_mul _
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun v ↦ ?_) hfin
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-! ## The finite half's measurability in the frequency -/

/-- The finite factor is measurable in the frequency.  This is the one place the chain needs
parameter measurability: `lintegral_iUnion` never did, but `lintegral_prod_mul` does.  Both inputs
are the repository's own -- joint continuity of the phase and measurability of the integral-vector
indicator -- and mathlib's product-integral measurability finishes, so no first countability of the
finite adeles is invoked. -/
theorem stronglyMeasurable_gaussIntegralAt (L : PositiveDefiniteIntegralLattice n) :
    StronglyMeasurable (fun s : RationalFiniteAdele ↦
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt s) := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hjoint : StronglyMeasurable
      (fun z : RationalFiniteAdele × (Fin n → RationalFiniteAdele) ↦
        ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt z.1 z.2 :
            Circle) : ℂ) *
          rationalFiniteAdeleVectorIntegralIndicator z.2) :=
    Measurable.stronglyMeasurable
      ((L.continuous_quadraticPhaseAt_uncurry).measurable.mul
        ((measurable_vectorIntegralIndicator n).comp measurable_snd))
  exact hjoint.integral_prod_right'

/-- Hence its modulus is measurable, which is what the Tonelli step consumes. -/
theorem aemeasurable_norm_gaussIntegralAt (L : PositiveDefiniteIntegralLattice n) :
    AEMeasurable (fun y ↦ ENNReal.ofReal
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y‖)
      rationalFiniteAdeleAddHaarMeasure :=
  (ENNReal.measurable_ofReal.comp
    (stronglyMeasurable_gaussIntegralAt L).measurable.norm).aemeasurable

/-! ## The two halves multiplied, at the standard test -/

/-- The composition run end to end at the standard test: the archimedean half, the finite half and
the factorization multiply to integrability of the adelic Bruhat coefficient.  The conclusion is
the repository's own `integrable_rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice`,
reached here by the local route instead of the block/height one -- so this is a check that the two
halves compose, not a new fact about the standard test. -/
theorem integrable_adelicBruhatCoefficient_polarGaussianLattice_localRoute
    (L : PositiveDefiniteIntegralLattice n) {scale : ℝ} (hscale : 0 < scale) (hn : 4 < n) :
    Integrable (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (scale : ℂ)))
      rationalAdeleAddHaarMeasure := by
  have hre : 0 < ((scale : ℝ) : ℂ).re := by simpa using hscale
  refine integrable_adelicBruhatCoefficient_of_localFactors
    L.rationalQuadraticSpaceMatrix _
    (integrable_rationalAdeleVectorPolarGaussianLatticeTest hre L)
    (fun w ↦ (L.polarRealDeterminantScale : ℂ)⁻¹ *
      (1 / ((scale : ℂ) - ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) : ℂ) *
        Complex.I) ^ (1 / 2 : ℂ)) ^ n)
    (fun y ↦ L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y)
    (fun a ↦
      rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
        L hre a)
    (aemeasurable_norm_archimedeanFactor L scale)
    (aemeasurable_norm_gaussIntegralAt L)
    (lintegral_norm_archimedeanFactor_lt_top L hscale (by omega))
    (IntegralFiniteAdelePhase.lintegral_norm_gaussIntegralAt_lt_top L
      L.rationalQuadraticSpaceMatrix rfl hn)

end PositiveDefiniteIntegralLattice
