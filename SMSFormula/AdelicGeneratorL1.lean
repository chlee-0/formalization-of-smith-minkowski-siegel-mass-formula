import SMSFormula.GeneralCarrierL1
import SMSFormula.RationalAdeleAdelicBruhatL1Class
import SMSFormula.ShiftedGaussianCoordinateEvaluation

/-!
# `G_b subset L` at a general generator

Both local halves are closed: the finite factor's `lintegral` is finite at every carrier scale, and
the archimedean factor at a shifted centre is evaluated and its `lintegral` bounded.  What the
local-factor criterion still asks for is the composition data -- two measurability statements and
integrability of the product test itself.  This file supplies them and runs the composition.

What is free and what is not.  The finite carrier's own measurability and integrability are free:
the repository's spanning theorem writes a test carried at scale one and periodic at level `r` as a
finite sum of coset indicators, each the indicator of a measurable set inside the integral vectors,
which have mass one.  At a general carrier scale both transport along the repository's own scale
pullback, a homeomorphism whose Haar factor is an explicit positive constant.

What is not free is measurability of the finite factor in the frequency, exactly as the Tonelli step
already recorded: `lintegral_iUnion` never needed it, `lintegral_prod_mul` does.  The input is the
joint measurability of `(t, x) |-> g x * psi(t Q(x))`, which is the repository's own phase continuity
in both variables together with measurability of `g`.

Negative scope.  The conclusion is integrability of the adelic Bruhat coefficient at one generator.
It is an upper bound: the zero test satisfies it, and nothing here evaluates either local integral,
compares two measures, or says anything about a family of tests -- a determining
positive-bump space is a statement about a family and is untouched.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open MeasureTheory Matrix RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

variable {n : ℕ}

/-! ## The finite carrier is measurable and integrable, for free -/

/-- The coset indicator is measurable. -/
theorem measurable_standardCosetIndicator {r : ℕ} (hr : r ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range) :
    Measurable (standardCosetIndicator n r alpha) :=
  measurable_one.indicator (measurableSet_standardCosetSet hr alpha)

/-- And integrable: the coset sits inside the integral vectors, whose mass is one. -/
theorem integrable_standardCosetIndicator {r : ℕ} (hr : r ≠ 0)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n r).range) :
    Integrable (standardCosetIndicator n r alpha)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hVmeas := measurableSet_integralFiniteAdeleVectors n
  have hmass : rationalFiniteAdeleCoordinateAddHaarMeasure n (integralFiniteAdeleVectors n) ≠ ⊤ := by
    rw [measure_integralFiniteAdeleVectors n]
    exact ENNReal.one_ne_top
  have hgint : Integrable
      ((integralFiniteAdeleVectors n).indicator (fun _ ↦ (1 : ℝ)))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    (integrable_indicator_iff hVmeas).2 (integrableOn_const hmass)
  refine hgint.mono' (measurable_standardCosetIndicator hr alpha).aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ standardCosetSet n r alpha
  · rw [standardCosetIndicator, Set.indicator_of_mem hx,
      Set.indicator_of_mem (standardCosetSet_subset_integral r alpha hx)]
    simp
  · rw [standardCosetIndicator, Set.indicator_of_notMem hx, norm_zero]
    exact Set.indicator_apply_nonneg fun _ ↦ zero_le_one

/-- At carrier scale one both are free, from the repository's own spanning theorem. -/
theorem measurable_of_standardScaleOne {r : ℕ} [NeZero r]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic r g) :
    Measurable g := by
  rw [standardScaleOne_eq_sum_cosetIndicator hcarried hperiodic]
  exact Finset.measurable_sum _ fun alpha _ ↦
    measurable_const.mul (measurable_standardCosetIndicator (NeZero.ne r) alpha)

theorem integrable_of_standardScaleOne {r : ℕ} [NeZero r]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic r g) :
    Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  rw [standardScaleOne_eq_sum_cosetIndicator hcarried hperiodic]
  exact integrable_finset_sum _ fun alpha _ ↦
    (integrable_standardCosetIndicator (NeZero.ne r) alpha).const_mul _

/-! ## Transport to a general carrier scale -/

/-- The pullback undoes the scaling, which is what transports both statements. -/
theorem standardScalePullback_scale {c : ℕ} (hc : c ≠ 0)
    (g : (Fin n → RationalFiniteAdele) → ℂ) (x : Fin n → RationalFiniteAdele) :
    standardScalePullback c g (rationalFiniteAdeleCoordinateScale ((c : ℚ)) x) = g x := by
  rw [standardScalePullback, rationalFiniteAdeleCoordinateScale_trans,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hc : ((c : ℚ)) ≠ 0),
    rationalFiniteAdeleCoordinateScale_one]

theorem measurable_of_standardCarried {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    Measurable g := by
  haveI : NeZero (c * d) := ⟨Nat.mul_ne_zero hc hd⟩
  have hgp : Measurable (standardScalePullback c g) :=
    measurable_of_standardScaleOne (hcarried.scalePullback hc) (hperiodic.scalePullback hc)
  have hcomp : g = (standardScalePullback c g) ∘
      (rationalFiniteAdeleCoordinateScale (n := n) ((c : ℚ))) := by
    funext x
    exact (standardScalePullback_scale hc g x).symm
  rw [hcomp]
  exact hgp.comp (continuous_rationalFiniteAdeleCoordinateScale ((c : ℚ))).measurable

theorem integrable_of_standardCarried {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  haveI : NeZero (c * d) := ⟨Nat.mul_ne_zero hc hd⟩
  have hq : ((c : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hc)
  have hgp : Integrable (standardScalePullback c g)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    integrable_of_standardScaleOne (hcarried.scalePullback hc) (hperiodic.scalePullback hc)
  have hgmeas : Measurable g := measurable_of_standardCarried hc hd hcarried hperiodic
  have hT : AEMeasurable (rationalFiniteAdeleCoordinateScale (n := n) ((c : ℚ))⁻¹)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    (continuous_rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹).measurable.aemeasurable
  have hmapped : Integrable g
      (Measure.map (rationalFiniteAdeleCoordinateScale (n := n) ((c : ℚ))⁻¹)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :=
    (integrable_map_measure hgmeas.aestronglyMeasurable hT).2 hgp
  rw [map_rationalFiniteAdeleCoordinateAddHaarMeasure_scale_inv n hc hq] at hmapped
  have hsmul : ((((c : ℝ≥0))⁻¹ ^ n : ℝ≥0)) •
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ((((c : ℝ≥0))⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) •
        (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [ENNReal.smul_def]
  rw [hsmul] at hmapped
  refine (integrable_smul_measure ?_ ?_).1 hmapped
  · simp [hc]
  · exact ENNReal.coe_ne_top

/-! ## The finite factor is measurable in the frequency -/

/-- The phase is jointly measurable, in the frequency and the vector together. -/
theorem measurable_uncurry_dotQuadraticPhase (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) :
    Measurable (fun z : RationalFiniteAdele × (Fin n → RationalFiniteAdele) ↦
      complexFiniteChar (z.1 * dotQuadratic C z.2)) := by
  have hc : Continuous (fun z : RationalFiniteAdele × (Fin n → RationalFiniteAdele) ↦
      rationalFiniteAdeleFourierChar (z.1 * dotQuadratic C z.2)) := by
    apply continuous_rationalFiniteAdeleFourierChar.comp
    unfold dotQuadratic Matrix.mulVec dotProduct
    fun_prop
  exact hc.subtype_val.measurable

/-- Hence the finite factor is measurable in the frequency, for any measurable carrier -- the one
hypothesis the Tonelli step consumes and the conductor route never needed. -/
theorem stronglyMeasurable_finiteFactor {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hg : Measurable g) (C : Matrix (Fin n) (Fin n) RationalFiniteAdele) :
    StronglyMeasurable (fun t : RationalFiniteAdele ↦
      ∫ x, g x * complexFiniteChar (t * dotQuadratic C x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hjoint : StronglyMeasurable
      (fun z : RationalFiniteAdele × (Fin n → RationalFiniteAdele) ↦
        g z.2 * complexFiniteChar (z.1 * dotQuadratic C z.2)) :=
    Measurable.stronglyMeasurable
      ((hg.comp measurable_snd).mul (measurable_uncurry_dotQuadraticPhase C))
  exact hjoint.integral_prod_right'

/-! ## The archimedean factor is measurable in the frequency -/

/-- The shifted coefficient is continuous in the frequency.  The complex power is handled at a base
of positive real part, where it is continuous, and the completion factor's denominator never
vanishes there either. -/
theorem continuous_shiftedCoefficient (n : ℕ) {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Continuous fun s : ℝ ↦ SMSFormula.ArchimedeanCentre.shiftedCoefficient n b s c := by
  have hw : Continuous fun s : ℝ ↦ SMSFormula.ArchimedeanCentre.width b s := by
    unfold SMSFormula.ArchimedeanCentre.width
    fun_prop
  have hre : ∀ s : ℝ, 0 < (SMSFormula.ArchimedeanCentre.width b s).re := by
    intro s
    rw [SMSFormula.ArchimedeanCentre.width_re]
    exact hb
  refine Continuous.mul ?_ (Complex.continuous_exp.comp ?_)
  · exact hw.cpow continuous_const
      (fun s ↦ Complex.mem_slitPlane_iff.2 (Or.inl (hre s)))
  · unfold SMSFormula.ArchimedeanCentre.shiftExponent
    exact continuous_const.mul
      (((Complex.continuous_ofReal.mul continuous_const).div hw
        (fun s ↦ SMSFormula.ArchimedeanCentre.width_ne_zero hb s)))

/-- Hence the shifted archimedean factor's modulus is measurable on the infinite adeles -- the
second of the two hypotheses the Tonelli step consumes, and the place the evaluation is used: the
factor is an integral, and only the evaluation makes it a continuous function of the frequency. -/
theorem aemeasurable_norm_shiftedArchimedeanFactor (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 < b)
    (u : Fin n → ℝ) :
    AEMeasurable (fun w : RationalInfiniteAdele ↦ ENNReal.ofReal
        ‖∫ x : Fin n → ℝ, ((Real.fourierChar
              ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) *
                L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
            polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ))‖)
      rationalInfiniteAdeleAddHaarMeasure := by
  have hpt : ∀ w : RationalInfiniteAdele,
      (∫ x : Fin n → ℝ, ((Real.fourierChar
            ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) *
              L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
          polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ))) =
        ((L.polarRealDeterminantScale : ℝ) : ℂ)⁻¹ *
          SMSFormula.ArchimedeanCentre.shiftedCoefficient n b
            (rationalInfiniteAdeleContinuousAddEquivReal w)
            (L.rationalQuadraticSpaceMatrix.realQuadraticFormValue u) := fun w ↦
    L.integral_fourierChar_polarRealGaussian_sub hb _ u
  simp only [hpt]
  refine Measurable.aemeasurable (ENNReal.measurable_ofReal.comp ?_)
  refine (Measurable.norm ?_)
  refine measurable_const.mul ?_
  exact ((continuous_shiftedCoefficient n hb
      (L.rationalQuadraticSpaceMatrix.realQuadraticFormValue u)).measurable).comp
    rationalInfiniteAdeleContinuousAddEquivReal.continuous.measurable

/-! ## The finite phase is the chain's own phase -/

/-- The lattice's rational presentation has the integral model as its finite-adelic form matrix, so
the conductor chain's hypothesis is discharged here rather than assumed. -/
theorem finiteAdelicFormMatrix_rationalQuadraticSpaceMatrix (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicFormMatrix = integralModelMatrix L.pairingMatrix := by
  rw [RationalQuadraticSpaceMatrix.finiteAdelicFormMatrix,
    rationalQuadraticSpaceMatrix_pairingMatrix,
    ← L.finiteAdelicFormMatrix_eq_map_rationalFormMatrix,
    finiteAdelicFormMatrix_eq_integralModelMatrix L]

/-- Hence the Bruhat phase is the chain's own phase, with no change of integrand. -/
theorem quadraticPhaseAt_eq_complexFiniteChar (L : PositiveDefiniteIntegralLattice n)
    (t : RationalFiniteAdele) (x : Fin n → RationalFiniteAdele) :
    ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt t x : Circle) : ℂ) =
      complexFiniteChar (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x) := by
  rw [← finiteAdelicFormMatrix_rationalQuadraticSpaceMatrix L]
  rfl

theorem integral_finiteFactor_eq (L : PositiveDefiniteIntegralLattice n) (t : RationalFiniteAdele)
    (g : (Fin n → RationalFiniteAdele) → ℂ) :
    (∫ x, ((L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhaseAt t x :
          Circle) : ℂ) * g x ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) =
      ∫ x, g x * complexFiniteChar (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
  integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    dsimp only
    rw [quadraticPhaseAt_eq_complexFiniteChar L t x, mul_comm])

/-! ## The generator itself is integrable -/

/-- The product test is integrable: the shifted archimedean Gaussian is a translate of the
repository's own integrable Gaussian, the finite carrier is integrable for free, and the adelic
coordinate Haar is the product of the two local ones. -/
theorem integrable_shiftedGaussianProductTest (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 < b)
    (u : Fin n → ℝ) {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hg : Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n)) :
    Integrable (fun x : Fin n → RationalAdele ↦
        polarRealGaussian L ((b : ℂ)) (rationalAdeleVectorRealPart n x - u) *
          g (rationalAdeleVectorFinitePart n x))
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hbre : 0 < ((b : ℂ)).re := by simpa using hb
  have hInf : Integrable (fun x : Fin n → ℝ ↦ polarRealGaussian L ((b : ℂ)) (x - u))
      (volume : Measure (Fin n → ℝ)) :=
    (integrable_polarRealGaussian hbre L).comp_sub_right u
  have hprod : Integrable (fun z : (Fin n → ℝ) × (Fin n → RationalFiniteAdele) ↦
      polarRealGaussian L ((b : ℂ)) (z.1 - u) * g z.2)
      ((volume : Measure (Fin n → ℝ)).prod
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) := MeasureTheory.Integrable.mul_prod hInf hg
  have hcomp := ((measurePreserving_rationalAdeleVectorRealFiniteSplit n).integrable_comp_emb
    (rationalAdeleVectorRealFiniteEquiv n).measurableEmbedding).2 hprod
  simpa [Function.comp_def, rationalAdeleVectorRealFiniteEquiv_apply] using hcomp

/-! ## The composition at a general generator -/

/-- `G_b subset L` at a general generator: for a shifted archimedean Gaussian at any positive width
and any centre, tensored with any finite carrier standard-carried at a nonzero scale and
standard-periodic at a nonzero level, the adelic Bruhat coefficient is integrable above rank four.

Both local `lintegral`s are the ones already closed; what this adds is the composition data --
measurability of each local factor in the frequency and integrability of the test. -/
theorem integrable_adelicBruhatCoefficient_shiftedGaussianGenerator (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) (u : Fin n → ℝ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    Integrable (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun x ↦ polarRealGaussian L ((b : ℂ)) (rationalAdeleVectorRealPart n x - u) *
          g (rationalAdeleVectorFinitePart n x)))
      rationalAdeleAddHaarMeasure := by
  have hgmeas : Measurable g := measurable_of_standardCarried hc hd hcarried hperiodic
  have hgint : Integrable g (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    integrable_of_standardCarried hc hd hcarried hperiodic
  refine integrable_adelicBruhatCoefficient_of_localFactors L.rationalQuadraticSpaceMatrix _
    (integrable_shiftedGaussianProductTest L hb u hgint)
    (fun w ↦ ∫ x : Fin n → ℝ, ((Real.fourierChar
        ((rationalInfiniteAdeleContinuousAddEquivReal w : ℝ) *
          L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x) : Circle) : ℂ) *
        polarRealGaussian L ((b : ℂ)) (x - u) ∂(volume : Measure (Fin n → ℝ)))
    (fun t ↦ ∫ x, g x * complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
      ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n))
    (fun a ↦ ?_) (aemeasurable_norm_shiftedArchimedeanFactor L hb u)
    ((ENNReal.measurable_ofReal.comp
      (stronglyMeasurable_finiteFactor hgmeas
        (integralModelMatrix L.pairingMatrix)).measurable.norm).aemeasurable)
    (lintegral_norm_shiftedArchimedeanFactor_lt_top L hb (by omega) u)
    (lintegral_norm_finiteFactor_generalCarrier_lt_top L hn hc hd hcarried hperiodic)
  rw [rationalAdeleRankOneAdelicBruhatCoefficient_shiftedGaussianTest L b u g a,
    integral_finiteFactor_eq L a.2 g]

/-! ## The span: `G_b subset L` -/

/-- The generator set `G_b`: a shifted archimedean polar Gaussian of fixed width at an arbitrary
centre, tensored with an arbitrary finite carrier of the repository's standard family. -/
def shiftedGaussianGenerators (L : PositiveDefiniteIntegralLattice n) (b : ℝ) :
    Set ((Fin n → RationalAdele) → ℂ) :=
  {Phi | ∃ (u : Fin n → ℝ) (c d : ℕ) (g : (Fin n → RationalFiniteAdele) → ℂ),
    c ≠ 0 ∧ d ≠ 0 ∧ IsStandardCarried c g ∧ IsStandardPeriodic d g ∧
      Phi = fun x ↦ polarRealGaussian L ((b : ℂ)) (rationalAdeleVectorRealPart n x - u) *
        g (rationalAdeleVectorFinitePart n x)}

/-- Each generator Lies in the `L^1` class. -/
theorem isAdelicBruhatL1_shiftedGaussianGenerator (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ}
    (hb : 0 < b) (u : Fin n → ℝ) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    L.rationalQuadraticSpaceMatrix.IsAdelicBruhatL1
      (fun x ↦ polarRealGaussian L ((b : ℂ)) (rationalAdeleVectorRealPart n x - u) *
        g (rationalAdeleVectorFinitePart n x)) :=
  ⟨integrable_shiftedGaussianProductTest L hb u
      (integrable_of_standardCarried hc hd hcarried hperiodic),
    integrable_adelicBruhatCoefficient_shiftedGaussianGenerator L hn hb u hc hd hcarried hperiodic⟩

/-- `G_b subset L`, in the form the route states it: the whole complex span of the generator set
lies in the adelic Bruhat `L^1` class above rank four.  The class being a subspace is the
repository's own fact, so only the generators had to be checked -- exactly the reduction the
per-width class-membership note predicted. -/
theorem isAdelicBruhatL1_of_mem_span_shiftedGaussianGenerators (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) {Phi : (Fin n → RationalAdele) → ℂ}
    (hmem : Phi ∈ Submodule.span ℂ (shiftedGaussianGenerators L b)) :
    L.rationalQuadraticSpaceMatrix.IsAdelicBruhatL1 Phi := by
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, c, d, g, hc, hd, hcarried, hperiodic, rfl⟩ := hx
      exact isAdelicBruhatL1_shiftedGaussianGenerator L hn hb u hc hd hcarried hperiodic
  | zero =>
      have h0 := isAdelicBruhatL1_shiftedGaussianGenerator L hn hb (0 : Fin n → ℝ)
        one_ne_zero one_ne_zero
        (g := (0 : (Fin n → RationalFiniteAdele) → ℂ)) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      simpa using h0
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
