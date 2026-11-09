import SMSFormula.AdelicGaussianSpinTamagawaEisensteinComparison
import SMSFormula.RationalAdeleRationalDilationHaar
import SMSFormula.RationalAdeleAdelicBruhatCoefficientActionInvariance
import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationFourier

/-!
# Rational dilation of shells: `Θ_b(Φ) = Θ_{q²b}(Φ(q⁻¹ ·))` and `d_Φ(b) = d_{Φ(q⁻¹ ·)}(q² b)`

For a nonzero rational `q`, the map `x ↦ q x` is a bijection from the rational vectors of norm `b`
to those of norm `q² b`, and it commutes with the GSpin action (the action is linear).  So the
shell theta of `Φ` at `b` equals the shell theta of the dilated test `Φ_q = Φ(q⁻¹ ·)` at `q² b`, and
the same holds for every normalization.  On the value-density side the rational dilation
invariance of the adelic Haar measures (product formula, `|q|_𝔸 = 1`) gives
`B_{Φ_q}(u) = B_Φ(q² u)` and `d_{Φ_q}(w) = d_Φ(q⁻² w)`.

Hence a shell identity `Θ^p_b · τ_V = ofReal ρ(b)` for `Φ` at `b` is equivalent to the same identity
for `Φ_q` at `q² b`.  With `q = |polarDeterminant L|` this moves the dual-test shells `b ∈ N⁻¹ ℤ` to integer norms,
where the core shell identity applies.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Coordinatewise multiplication of an adelic vector by a rational scalar. -/
def rationalAdeleVectorRationalDilation (q : ℚ) (x : Fin n → RationalAdele) :
    Fin n → RationalAdele :=
  fun i ↦ algebraMap ℚ RationalAdele q * x i

theorem rationalAdeleVectorRationalDilation_eq_smul (q : ℚ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorRationalDilation q x = algebraMap ℚ RationalAdele q • x := by
  funext i
  simp [rationalAdeleVectorRationalDilation]

theorem rationalAdeleVectorRationalDilation_inv_cancel {q : ℚ} (hq : q ≠ 0)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorRationalDilation q⁻¹ (rationalAdeleVectorRationalDilation q x) = x := by
  funext i
  simp only [rationalAdeleVectorRationalDilation, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq,
    map_one, one_mul]

/-- The GSpin action on rational vectors commutes with rational dilation. -/
theorem fullAdelicCliffordGeneralSpinRationalVectorAction_smul (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicCliffordGeneralSpinGroup) (q : ℚ) (x : Fin n → ℚ) :
    V.fullAdelicCliffordGeneralSpinRationalVectorAction g (q • x) =
      rationalAdeleVectorRationalDilation q (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x) := by
  have hdiag : rationalAdeleVectorDiagonal n (q • x) =
      algebraMap ℚ RationalAdele q • rationalAdeleVectorDiagonal n x := by
    funext i
    simp [rationalAdeleVectorDiagonal]
  rw [rationalAdeleVectorRationalDilation_eq_smul, fullAdelicCliffordGeneralSpinRationalVectorAction,
    fullAdelicCliffordGeneralSpinRationalVectorAction, hdiag, Matrix.mulVec_smul]

/-- The dilated represented norm `q² b`, represented by `q x`. -/
def RepresentedNonzeroRationalNorm.dilate (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm) {q : ℚ} (hq : q ≠ 0) : V.RepresentedNonzeroRationalNorm :=
  ⟨q ^ 2 * b.1, mul_ne_zero (pow_ne_zero 2 hq) b.2.1, by
    obtain ⟨x, hx⟩ := b.2.2
    refine ⟨q • x, ?_⟩
    rw [QuadraticMap.map_smul, hx, smul_eq_mul]
    ring⟩

@[simp]
theorem RepresentedNonzeroRationalNorm.dilate_coe (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm) {q : ℚ} (hq : q ≠ 0) :
    (RepresentedNonzeroRationalNorm.dilate V b hq).1 = q ^ 2 * b.1 :=
  rfl

/-- The shell theta is dilation-covariant: `Θ_{q²b}(Φ(q⁻¹ ·)) = Θ_b(Φ)` pointwise on the group. -/
theorem fullAdelicCliffordGeneralSpinRepresentedNormTheta_dilate (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm) {q : ℚ} (hq : q ≠ 0)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormTheta (RepresentedNonzeroRationalNorm.dilate V b hq)
        (fun y ↦ Phi (rationalAdeleVectorRationalDilation q⁻¹ y)) g =
      V.fullAdelicCliffordGeneralSpinRepresentedNormTheta b Phi g := by
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  let e : RepresentedNonzeroRationalNorm.rationalVectorFiber V b ≃
      RepresentedNonzeroRationalNorm.rationalVectorFiber V
        (RepresentedNonzeroRationalNorm.dilate V b hq) :=
    { toFun := fun x ↦ ⟨q • x.1, by
        change V.nativeRationalQuadraticForm (q • x.1) = q ^ 2 * b.1
        rw [QuadraticMap.map_smul, x.2, smul_eq_mul]
        ring⟩
      invFun := fun y ↦ ⟨q⁻¹ • y.1, by
        have hy : V.nativeRationalQuadraticForm y.1 = q ^ 2 * b.1 := y.2
        rw [QuadraticMap.map_smul, hy, smul_eq_mul]
        field_simp⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        change q⁻¹ • q • x.1 = x.1
        rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
      right_inv := fun y ↦ by
        apply Subtype.ext
        change q • q⁻¹ • y.1 = y.1
        rw [smul_smul, mul_inv_cancel₀ hq, one_smul] }
  unfold fullAdelicCliffordGeneralSpinRepresentedNormTheta
  rw [← e.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  unfold fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
  change Phi (rationalAdeleVectorRationalDilation q⁻¹
      (V.fullAdelicCliffordGeneralSpinRationalVectorAction g (q • x.1))) =
    Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x.1)
  rw [fullAdelicCliffordGeneralSpinRationalVectorAction_smul,
    rationalAdeleVectorRationalDilation_inv_cancel hq]

theorem fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_dilate
    (V : RationalQuadraticSpaceMatrix n) (b : V.RepresentedNonzeroRationalNorm) {q : ℚ} (hq : q ≠ 0)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
        (RepresentedNonzeroRationalNorm.dilate V b hq)
        (fun y ↦ Phi (rationalAdeleVectorRationalDilation q⁻¹ y)) =
      V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient b Phi := by
  funext Z
  induction Z using Quot.ind with
  | mk g => exact V.fullAdelicCliffordGeneralSpinRepresentedNormTheta_dilate b hq Phi g

/-- The adelic Bruhat coefficient of the dilated test is the rescaled coefficient. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_dilate (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) {q : ℚ} (hq : q ≠ 0) (u : RationalAdele) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient
        (fun y ↦ Phi (rationalAdeleVectorRationalDilation q⁻¹ y)) u =
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi (algebraMap ℚ RationalAdele (q ^ 2) * u) := by
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral,
    V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral]
  have hmp := PositiveDefiniteIntegralLattice.measurePreserving_rationalAdeleCoordinate_rationalDilation n q hq
  let e : (Fin n → RationalAdele) ≃ᵐ (Fin n → RationalAdele) :=
    { toFun := fun x ↦ rationalAdeleVectorRationalDilation q x
      invFun := fun x ↦ rationalAdeleVectorRationalDilation q⁻¹ x
      left_inv := fun x ↦ rationalAdeleVectorRationalDilation_inv_cancel hq x
      right_inv := fun x ↦ by
        have := rationalAdeleVectorRationalDilation_inv_cancel (inv_ne_zero hq) x
        rwa [inv_inv] at this
      measurable_toFun := hmp.measurable
      measurable_invFun :=
        (PositiveDefiniteIntegralLattice.measurePreserving_rationalAdeleCoordinate_rationalDilation n q⁻¹
          (inv_ne_zero hq)).measurable }
  have hmp' : MeasurePreserving e (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := hmp
  rw [← hmp'.integral_comp' (fun x ↦ Phi (rationalAdeleVectorRationalDilation q⁻¹ x) *
    (V.rationalAdeleRankOneQuadraticPhase u x : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  change Phi (rationalAdeleVectorRationalDilation q⁻¹ (rationalAdeleVectorRationalDilation q y)) *
      (V.rationalAdeleRankOneQuadraticPhase u (rationalAdeleVectorRationalDilation q y) : ℂ) =
    Phi y * (V.rationalAdeleRankOneQuadraticPhase (algebraMap ℚ RationalAdele (q ^ 2) * u) y : ℂ)
  rw [rationalAdeleVectorRationalDilation_inv_cancel hq]
  congr 2
  unfold rationalAdeleRankOneQuadraticPhase
  rw [rationalAdeleVectorRationalDilation_eq_smul, V.fullAdelicQuadraticFormValue_smul, map_pow]
  ring_nf

/-- The value density is dilation-covariant: `d_{Φ(q⁻¹ ·)}(q² w) = d_Φ(w)`. -/
theorem complexValueFourierDensity_dilate (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) {q : ℚ} (hq : q ≠ 0) (w : RationalAdele) :
    V.complexValueFourierDensity (fun y ↦ Phi (rationalAdeleVectorRationalDilation q⁻¹ y))
        (algebraMap ℚ RationalAdele (q ^ 2) * w) =
      V.complexValueFourierDensity Phi w := by
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  unfold complexValueFourierDensity
  rw [Fourier.fourierIntegral_def, Fourier.fourierIntegral_def]
  simp_rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_dilate Phi hq]
  have hmp := PositiveDefiniteIntegralLattice.measurePreserving_rationalAdele_rationalDilation (q ^ 2) hq2
  let e : RationalAdele ≃ᵐ RationalAdele :=
    { toFun := fun u ↦ algebraMap ℚ RationalAdele (q ^ 2) * u
      invFun := fun u ↦ algebraMap ℚ RationalAdele (q ^ 2)⁻¹ * u
      left_inv := fun u ↦ by
        simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq2, map_one, one_mul]
      right_inv := fun u ↦ by
        simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq2, map_one, one_mul]
      measurable_toFun := hmp.measurable
      measurable_invFun :=
        (PositiveDefiniteIntegralLattice.measurePreserving_rationalAdele_rationalDilation (q ^ 2)⁻¹
          (inv_ne_zero hq2)).measurable }
  have hmp' : MeasurePreserving e rationalAdeleAddHaarMeasure rationalAdeleAddHaarMeasure := hmp
  rw [← hmp'.integral_comp' (fun u : RationalAdele ↦
    rationalAdeleFourierChar (-(u * w)) • V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  change rationalAdeleFourierChar (-(u * (algebraMap ℚ RationalAdele (q ^ 2) * w))) •
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi (algebraMap ℚ RationalAdele (q ^ 2) * u) =
    rationalAdeleFourierChar (-(algebraMap ℚ RationalAdele (q ^ 2) * u * w)) •
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi (algebraMap ℚ RationalAdele (q ^ 2) * u)
  congr 3
  ring

theorem realValueDensity_dilate (V : RationalQuadraticSpaceMatrix n)
    (f : (Fin n → RationalAdele) → ℝ) {q : ℚ} (hq : q ≠ 0) (b : ℚ) :
    V.realValueDensity (fun y ↦ f (rationalAdeleVectorRationalDilation q⁻¹ y))
        (algebraMap ℚ RationalAdele (q ^ 2 * b)) =
      V.realValueDensity f (algebraMap ℚ RationalAdele b) := by
  simp only [realValueDensity]
  rw [map_mul, V.complexValueFourierDensity_dilate (fun x ↦ (f x : ℂ)) hq]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- The shell identity is dilation-invariant: the identity for `f` at `b` is equivalent to the
identity for `f(q⁻¹ ·)` at `q² b`. -/
theorem shellIdentity_iff_dilate
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    (f : (Fin (r + 2) → RationalAdele) → ℝ)
    (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm) {q : ℚ} (hq : q ≠ 0)
    (cutoff : ℝ → ℝ≥0∞) :
    (L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv
          (RepresentedNonzeroRationalNorm.dilate _ b hq)
          (fun y ↦ ENNReal.ofReal (f (rationalAdeleVectorRationalDilation q⁻¹ y))) cutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (fun y ↦ f (rationalAdeleVectorRationalDilation q⁻¹ y))
        (algebraMap ℚ RationalAdele (RepresentedNonzeroRationalNorm.dilate _ b hq).1))) ↔
    (L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal (f y)) cutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity f
        (algebraMap ℚ RationalAdele b.1))) := by
  have htheta : L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP
      hconv (RepresentedNonzeroRationalNorm.dilate _ b hq)
      (fun y ↦ ENNReal.ofReal (f (rationalAdeleVectorRationalDilation q⁻¹ y))) cutoff =
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
        (fun y ↦ ENNReal.ofReal (f y)) cutoff := by
    unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
      fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    dsimp only
    rw [L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_dilate
      b hq (fun y ↦ ENNReal.ofReal (f y))]
  rw [htheta, RepresentedNonzeroRationalNorm.dilate_coe,
    L.rationalQuadraticSpaceMatrix.realValueDensity_dilate f hq]

/-! ## The dilated dual core `Ψ(·/D)` as a real-Gaussian-core member -/

namespace IntegralFiniteAdelePhase

variable {n : ℕ}

theorem realShiftedGaussian_smul (L : PositiveDefiniteIntegralLattice n) (b t : ℝ) (x : Fin n → ℝ) :
    realShiftedGaussian L b 0 (t • x) = realShiftedGaussian L (b * t ^ 2) 0 x := by
  rw [realShiftedGaussian_eq, realShiftedGaussian_eq,
    SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply,
    SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  simp only [ContinuousMap.id_apply, sub_zero, QuadraticMap.map_smul, smul_eq_mul]
  congr 1
  ring

theorem rationalAdeleVectorRealPart_rationalDilation (q : ℚ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (rationalAdeleVectorRationalDilation q x) =
      (q : ℝ) • rationalAdeleVectorRealPart n x := by
  funext i
  simp only [rationalAdeleVectorRealPart, rationalAdeleVectorRationalDilation, Pi.smul_apply,
    smul_eq_mul]
  change rationalInfiniteAdeleContinuousAddEquivReal
    ((algebraMap ℚ RationalAdele q).1 * (x i).1) = _
  rw [show (algebraMap ℚ RationalAdele q).1 = algebraMap ℚ RationalInfiniteAdele q from
    DFunLike.congr_fun (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q]
  rw [show rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele q * (x i).1) =
      rationalInfiniteAdeleContinuousAddEquivReal (algebraMap ℚ RationalInfiniteAdele q) *
        rationalInfiniteAdeleContinuousAddEquivReal (x i).1 from
    rationalInfiniteAdeleRingEquivReal.map_mul _ _,
    rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  simp

theorem rationalAdeleVectorFinitePart_rationalDilation (q : ℚ) (x : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (rationalAdeleVectorRationalDilation q x) =
      algebraMap ℚ RationalFiniteAdele q • rationalAdeleVectorFinitePart n x := by
  funext i
  simp only [rationalAdeleVectorFinitePart, rationalAdeleVectorRationalDilation, Pi.smul_apply,
    smul_eq_mul]
  change (algebraMap ℚ RationalAdele q).2 * (x i).2 = _
  rw [show (algebraMap ℚ RationalAdele q).2 = algebraMap ℚ RationalFiniteAdele q from
    DFunLike.congr_fun (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q]

/-- The finite factor of the dilated dual test: the indicator of `D · L^#`. -/
def realDilatedPolarDualIndicator (L : PositiveDefiniteIntegralLattice n) (y : Fin n → RationalFiniteAdele) : ℝ :=
  realFinitePolarDualLatticeIndicator L
    (algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ • y)

theorem isStandardCarried_realDilatedPolarDualIndicator (L : PositiveDefiniteIntegralLattice n) :
    IsStandardCarried 1 (fun y ↦ (realDilatedPolarDualIndicator L y : ℂ)) := by
  have hD : ((L.polarDeterminant.natAbs : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne'
  intro y hy
  have h := isStandardCarried_finitePolarDualLatticeIndicator L
    (algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ • y) ?_
  · simpa [realDilatedPolarDualIndicator] using h
  · intro hmem
    apply hy
    change 1 • y ∈ integralFiniteAdeleVectors n
    rw [one_smul]
    have hmem' : L.polarDeterminant.natAbs • (algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ • y) ∈
        integralFiniteAdeleVectors n := hmem
    rwa [← Nat.cast_smul_eq_nsmul RationalFiniteAdele, smul_smul,
      show ((L.polarDeterminant.natAbs : ℕ) : RationalFiniteAdele) *
          algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ = 1 by
        rw [← map_natCast (algebraMap ℚ RationalFiniteAdele), ← map_mul, mul_inv_cancel₀ hD,
          map_one], one_smul] at hmem'

theorem isStandardPeriodic_realDilatedPolarDualIndicator (L : PositiveDefiniteIntegralLattice n) :
    IsStandardPeriodic L.polarDeterminant.natAbs (fun y ↦ (realDilatedPolarDualIndicator L y : ℂ)) := by
  have hD : ((L.polarDeterminant.natAbs : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne'
  intro y u hu
  have h := isStandardPeriodic_finitePolarDualLatticeIndicator L
    (algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ • y) u hu
  simp only [one_nsmul] at h
  simp only [realDilatedPolarDualIndicator]
  rw [smul_add, ← Nat.cast_smul_eq_nsmul RationalFiniteAdele, smul_smul,
    show algebraMap ℚ RationalFiniteAdele ((L.polarDeterminant.natAbs : ℚ))⁻¹ *
        ((L.polarDeterminant.natAbs : ℕ) : RationalFiniteAdele) = 1 by
      rw [← map_natCast (algebraMap ℚ RationalFiniteAdele), ← map_mul, inv_mul_cancel₀ hD,
        map_one], one_smul]
  exact h

/-- The dilated dual test `Ψ(·/D)` as a member of the real Gaussian core at width `b / D²`. -/
def polarGaussianDualDilatedCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) :
    realGaussianCore L (b * ((L.polarDeterminant.natAbs : ℝ))⁻¹ ^ 2) :=
  ⟨fun x ↦ realShiftedGaussian L (b * ((L.polarDeterminant.natAbs : ℝ))⁻¹ ^ 2) 0
      (rationalAdeleVectorRealPart n x) *
      realDilatedPolarDualIndicator L (rationalAdeleVectorFinitePart n x),
    Submodule.subset_span ⟨0, 1, L.polarDeterminant.natAbs, realDilatedPolarDualIndicator L, one_ne_zero,
      Int.natAbs_ne_zero.mpr L.polarDeterminant_pos.ne',
      isStandardCarried_realDilatedPolarDualIndicator L,
      isStandardPeriodic_realDilatedPolarDualIndicator L, rfl⟩⟩

/-- The dilated dual core is the dual core composed with the dilation by `D⁻¹`. -/
theorem polarGaussianDualDilatedCore_val (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (x : Fin n → RationalAdele) :
    (polarGaussianDualDilatedCore L b).val x =
      (polarGaussianDualCore L b).val
        (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ x) := by
  change realShiftedGaussian L (b * ((L.polarDeterminant.natAbs : ℝ))⁻¹ ^ 2) 0
      (rationalAdeleVectorRealPart n x) *
      realDilatedPolarDualIndicator L (rationalAdeleVectorFinitePart n x) =
    realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n
        (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ x)) *
      realFinitePolarDualLatticeIndicator L (rationalAdeleVectorFinitePart n
        (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ x))
  rw [rationalAdeleVectorRealPart_rationalDilation, rationalAdeleVectorFinitePart_rationalDilation,
    realShiftedGaussian_smul]
  push_cast
  rfl

theorem polarGaussianDualDilatedCore_nonneg (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (x : Fin n → RationalAdele) : 0 ≤ (polarGaussianDualDilatedCore L b).val x := by
  rw [polarGaussianDualDilatedCore_val]
  exact polarGaussianDualCore_nonneg L b _

theorem measurable_ofReal_polarGaussianDualDilatedCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) :
    Measurable (fun y ↦ ENNReal.ofReal ((polarGaussianDualDilatedCore L b).val y)) := by
  have hD : ((L.polarDeterminant.natAbs : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by
    exact_mod_cast Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne')
  have hfun : (fun y ↦ ENNReal.ofReal ((polarGaussianDualDilatedCore L b).val y)) =
      (rationalAdeleVectorPolarGaussianDualTestENNReal L b) ∘
        (fun y ↦ rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ y) := by
    funext y
    simp only [Function.comp_apply, polarGaussianDualDilatedCore_val,
      rationalAdeleVectorPolarGaussianDualTestENNReal_eq_ofReal]
  rw [hfun]
  exact (measurable_rationalAdeleVectorPolarGaussianDualTestENNReal L b).comp
    (PositiveDefiniteIntegralLattice.measurePreserving_rationalAdeleCoordinate_rationalDilation n _ hD).measurable

end IntegralFiniteAdelePhase

/-- The theta–Eisenstein comparison at integer norms only: `τ(Spin_V) = 1` follows from the shell
identities at integral represented norms for the standard core (width `a`) and for the dilated
dual core `Ψ(·/D)` (`D = |polarDeterminant L|`, width `a⁻¹`). These are exactly the integer-norm
shells where the core theorem applies. -/
theorem spinTamagawaNumberENNReal_eq_one_of_integerShellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
            (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ y)))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (fun y ↦ (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
          (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ y))
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  have hD : ((L.polarDeterminant.natAbs : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne'
  refine L.spinTamagawaNumberENNReal_eq_one_of_supportedShellIdentities hr hrank inst hP hconv ha hC
    hΦ (fun b hb ↦ ?_)
  refine (L.shellIdentity_iff_dilate hr inst hP hconv
    (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val b hD
    rationalIdeleClassUnitLogCutoff).1 (hΨ _ ?_)
  obtain ⟨k, hk⟩ := hb
  refine ⟨k, ?_⟩
  rw [RepresentedNonzeroRationalNorm.dilate_coe, hk]
  push_cast
  ring

/-- The integer-norm form in core terms: `τ(Spin_V) = 1` from the shell identities at integral norms
for the two core members `polarGaussianLatticeCore L a` and `polarGaussianDualDilatedCore L a⁻¹` --
exactly the inputs of the core theorem `representedNormTheta_mul_spinTamagawa_eq_core` with
`τ(Spin_{W_b}) = 1`. -/
theorem spinTamagawaNumberENNReal_eq_one_of_integerCoreShellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    (hΦ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal ((IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a).val
        (algebraMap ℚ RationalAdele b.1)))
    (hΨ : ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      b.1 ∈ (algebraMap ℤ ℚ).range →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal
            ((IntegralFiniteAdelePhase.polarGaussianDualDilatedCore L a⁻¹).val y))
          rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity
        (IntegralFiniteAdelePhase.polarGaussianDualDilatedCore L a⁻¹).val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  have hval : (IntegralFiniteAdelePhase.polarGaussianDualDilatedCore L a⁻¹).val =
      fun y ↦ (IntegralFiniteAdelePhase.polarGaussianDualCore L a⁻¹).val
        (rationalAdeleVectorRationalDilation ((L.polarDeterminant.natAbs : ℚ))⁻¹ y) :=
    funext (IntegralFiniteAdelePhase.polarGaussianDualDilatedCore_val L a⁻¹)
  refine L.spinTamagawaNumberENNReal_eq_one_of_integerShellIdentities hr hrank inst hP hconv ha hC
    hΦ (fun b hb ↦ ?_)
  have h := hΨ b hb
  rw [hval] at h
  exact h

end PositiveDefiniteIntegralLattice
