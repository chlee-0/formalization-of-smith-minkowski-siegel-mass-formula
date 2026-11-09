import SMSFormula.RationalAdeleVectorComplexGaussianTheta
import SMSFormula.RationalAdeleVectorPeriodicGaussianReparametrized
import SMSFormula.RationalFiniteAdeleQuadraticGaussRectangularQuotient

/-!
# Rational boundary parameters for finite quadratic Gauss reciprocity

For a nonzero real parameter `t`, the direct Landsberg--Schaar route applies
the right-half-plane matrix theta identity at

`rho - t⁻¹ * I`,  `rho > 0`.

This file isolates the exact reciprocal parameter.  Its real part remains a
positive scale tending to zero; after removing the limiting phase `t`, its
imaginary error divided by that scale is exactly `-rho*t`.  These facts let
the reparameterized oscillatory Abel theorem apply without selecting an
inverse for the real-part function.
-/

noncomputable section

open Filter Matrix Topology RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- The right-half-plane parameter approaching the rational imaginary
boundary `-t⁻¹ I`. -/
def rationalGaussBoundaryParameter (t ρ : ℝ) : ℂ :=
  (ρ : ℂ) - (t⁻¹ : ℂ) * Complex.I

/-- Real part of the reciprocal rational boundary parameter. -/
def rationalGaussDualRealScale (t ρ : ℝ) : ℝ :=
  ρ / (ρ ^ 2 + t⁻¹ ^ 2)

/-- Difference between the reciprocal parameter's imaginary part and its
limiting value `t`. -/
def rationalGaussDualImaginaryError (t ρ : ℝ) : ℝ :=
  t⁻¹ / (ρ ^ 2 + t⁻¹ ^ 2) - t

@[simp]
theorem rationalGaussBoundaryParameter_re (t ρ : ℝ) :
    (rationalGaussBoundaryParameter t ρ).re = ρ := by
  simp [rationalGaussBoundaryParameter]

theorem rationalGaussBoundaryParameter_ne_zero
    {t : ℝ} (ht : t ≠ 0) (ρ : ℝ) :
    rationalGaussBoundaryParameter t ρ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [rationalGaussBoundaryParameter, ht] at him

/-- Exact decomposition of the reciprocal boundary parameter into its small
positive real scale, limiting phase, and imaginary error. -/
theorem rationalGaussBoundaryParameter_inv
    (t ρ : ℝ) :
    (rationalGaussBoundaryParameter t ρ)⁻¹ =
      (rationalGaussDualRealScale t ρ : ℂ) +
        ((t + rationalGaussDualImaginaryError t ρ : ℝ) : ℂ) * Complex.I := by
  have hnorm :
      Complex.normSq (rationalGaussBoundaryParameter t ρ) =
        ρ ^ 2 + t⁻¹ ^ 2 := by
    rw [Complex.normSq_apply]
    simp [rationalGaussBoundaryParameter]
    ring
  apply Complex.ext
  · rw [Complex.inv_re]
    rw [hnorm]
    simp only [rationalGaussBoundaryParameter_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero]
    norm_num
    simp [rationalGaussDualRealScale, inv_pow]
  · rw [Complex.inv_im]
    rw [hnorm]
    have him : (rationalGaussBoundaryParameter t ρ).im = -t⁻¹ := by
      simp [rationalGaussBoundaryParameter]
    rw [him]
    simp only [neg_neg, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, zero_add]
    norm_num
    unfold rationalGaussDualImaginaryError
    ring

theorem rationalGaussDualRealScale_pos
    {t ρ : ℝ} (ht : t ≠ 0) (hρ : 0 < ρ) :
    0 < rationalGaussDualRealScale t ρ := by
  unfold rationalGaussDualRealScale
  exact div_pos hρ (add_pos_of_nonneg_of_pos (sq_nonneg ρ)
    (sq_pos_of_ne_zero (inv_ne_zero ht)))

/-- The reciprocal imaginary error is exactly little-oh relative to its real
scale; this pointwise quotient is the key cancellation. -/
theorem rationalGaussDualImaginaryError_div_realScale
    {t : ℝ} (ht : t ≠ 0) (ρ : ℝ) :
    rationalGaussDualImaginaryError t ρ /
        rationalGaussDualRealScale t ρ = -ρ * t := by
  unfold rationalGaussDualImaginaryError rationalGaussDualRealScale
  by_cases hρ : ρ = 0
  · simp [hρ]
  · field_simp [ht, hρ]
    ring

theorem tendsto_rationalGaussDualRealScale_nhdsGT_zero
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (rationalGaussDualRealScale t)
      (𝓝[>] 0) (𝓝[>] 0) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
  have hnum : Tendsto (fun ρ : ℝ ↦ ρ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.mono_left hle
  have hden :
      Tendsto (fun ρ : ℝ ↦ ρ ^ 2 + t⁻¹ ^ 2) (𝓝[>] 0)
        (𝓝 (t⁻¹ ^ 2)) := by
    simpa using (hnum.pow 2).add tendsto_const_nhds
  have hzero : Tendsto (rationalGaussDualRealScale t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [rationalGaussDualRealScale, zero_div] using
      hnum.div hden (pow_ne_zero 2 (inv_ne_zero ht))
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      rationalGaussDualRealScale t ρ ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact rationalGaussDualRealScale_pos ht hρ
  exact tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩

theorem tendsto_rationalGaussDualImaginaryError_div_realScale
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto
      (fun ρ ↦ rationalGaussDualImaginaryError t ρ /
        rationalGaussDualRealScale t ρ)
      (𝓝[>] 0) (𝓝 0) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
  have hlinear : Tendsto (fun ρ : ℝ ↦ -ρ * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuousAt_id.neg.mul_const t).mono_left hle
  apply hlinear.congr'
  exact Filter.Eventually.of_forall fun ρ ↦
    (rationalGaussDualImaginaryError_div_realScale ht ρ).symm

/-! ## Literal finite phases on integer coordinates -/

private theorem finiteAdelicQuadraticFormValue_integerDiagonal
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (z : Fin n → ℤ) :
    V.finiteAdelicQuadraticFormValue
        (fun i ↦ (integerToIntegralFiniteAdele (z i) : RationalFiniteAdele)) =
      algebraMap ℚ RationalFiniteAdele
        (V.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ))) := by
  simp [RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue,
    RationalQuadraticSpaceMatrix.finiteAdelicFormMatrix,
    RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
    RationalQuadraticSpaceMatrix.quadraticForm,
    Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVec,
    dotProduct, map_sum]

private theorem nativeRationalQuadraticForm_intCast_eq_half_polar
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (z : Fin n → ℤ) :
    ((V.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) : ℚ) : ℝ) =
      (2 : ℝ)⁻¹ * integerVectorMatrixQuadraticValue V.realPolarMatrix z := by
  have hcast :
      ((V.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) : ℚ) : ℝ) =
        V.realQuadraticFormValue (integerVectorReal z) := by
    simp [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm,
      RationalQuadraticSpaceMatrix.realQuadraticFormValue,
      RationalQuadraticSpaceMatrix.realFormMatrix,
      Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVec,
      dotProduct, integerVectorReal]
  rw [hcast]
  have hpolar : V.realPolarMatrix = (2 : ℝ) • V.realFormMatrix := by
    ext i j
    simp [RationalQuadraticSpaceMatrix.realPolarMatrix,
      RationalQuadraticSpaceMatrix.realFormMatrix,
      RationalQuadraticSpaceMatrix.polarMatrix]
  rw [hpolar]
  simp only [RationalQuadraticSpaceMatrix.realQuadraticFormValue,
    integerVectorMatrixQuadraticValue, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  ring

/-- On the canonical standard residue cube, the actual finite-adelic phase
is exactly the real quadratic oscillation for the polar matrix `C = 2F`.
This is an identity of the existing characters, not a Gauss-sum value. -/
theorem rationalFiniteAdeleIntegralQuadraticPhaseOnResidues_intCast_eq_oscillation
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : Fin n → ℤ) :
    rationalFiniteAdeleIntegralQuadraticPhaseOnResidues L t
        (fun i ↦ (z i : ZMod t.den)) =
      quadraticOscillation
        L.rationalQuadraticSpaceMatrix.realPolarMatrix (t : ℝ) z := by
  rw [rationalFiniteAdeleIntegralQuadraticPhaseOnResidues_intCast]
  change
    (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
        (fun i ↦
          (integerToIntegralFiniteAdele (z i) : RationalFiniteAdele)) : ℂ) = _
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase
  rw [finiteAdelicQuadraticFormValue_integerDiagonal, ← map_mul]
  rw [rationalFiniteAdeleFourierChar_algebraMap]
  rw [Circle.coe_inv, Real.fourierChar_apply, quadraticOscillation,
    ← Complex.exp_neg]
  congr 1
  rw [Rat.cast_mul,
    nativeRationalQuadraticForm_intCast_eq_half_polar]
  push_cast
  ring

private theorem finitePolarDualEquivIntegralCoordinates_symm_intCast
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    (((finitePolarDualEquivIntegralCoordinates L).symm
        (fun i ↦ integerToIntegralFiniteAdele (z i)) :
          FinitePolarDualAdeleVector L) : Fin n → RationalFiniteAdele) =
      fun i ↦ algebraMap ℚ RationalFiniteAdele
        ((L.rationalQuadraticSpaceMatrix.polarMatrix⁻¹.mulVec
          (fun j ↦ (z j : ℚ))) i) := by
  let V := L.rationalQuadraticSpaceMatrix
  let q : Fin n → ℚ :=
    V.polarMatrix⁻¹.mulVec (fun j ↦ (z j : ℚ))
  let y : FinitePolarDualAdeleVector L :=
    (finitePolarDualEquivIntegralCoordinates L).symm
      (fun i ↦ integerToIntegralFiniteAdele (z i))
  have hCq : V.polarMatrix.mulVec q = fun i ↦ (z i : ℚ) := by
    dsimp [q]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero)]
    exact Matrix.one_mulVec _
  change y.1 = fun i ↦ algebraMap ℚ RationalFiniteAdele (q i)
  apply V.finiteAdelicPolarMatrixLinearEquiv.injective
  have hy := (finitePolarDualEquivIntegralCoordinates L).apply_symm_apply
    (fun i ↦ integerToIntegralFiniteAdele (z i))
  rw [V.finiteAdelicPolarMatrixLinearEquiv_apply]
  change V.finiteAdelicPolarMatrix.mulVec y.1 =
    V.finiteAdelicPolarMatrix.mulVec
      (fun i ↦ algebraMap ℚ RationalFiniteAdele (q i))
  rw [show V.finiteAdelicPolarMatrix.mulVec y.1 =
      fun i ↦ algebraMap ℚ RationalFiniteAdele (z i : ℚ) by
    funext i
    exact congrArg Subtype.val (congrFun hy i)]
  funext i
  change algebraMap ℚ RationalFiniteAdele (z i : ℚ) = _
  rw [show V.finiteAdelicPolarMatrix.mulVec
      (fun i ↦ algebraMap ℚ RationalFiniteAdele (q i)) i =
      algebraMap ℚ RationalFiniteAdele (V.polarMatrix.mulVec q i) by
    simp [RationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix,
      Matrix.mulVec, dotProduct, map_sum]]
  rw [hCq]

private theorem nativeRationalQuadraticForm_polar_inv_intCast_eq_half
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (z : Fin n → ℤ) :
    let q : Fin n → ℚ :=
      V.polarMatrix⁻¹.mulVec (fun j ↦ (z j : ℚ))
    ((V.nativeRationalQuadraticForm q : ℚ) : ℝ) =
      (2 : ℝ)⁻¹ *
        integerVectorMatrixQuadraticValue V.realPolarMatrix⁻¹ z := by
  let q : Fin n → ℚ :=
    V.polarMatrix⁻¹.mulVec (fun j ↦ (z j : ℚ))
  dsimp only
  have hCqRat : V.polarMatrix.mulVec q = fun i ↦ (z i : ℚ) := by
    dsimp [q]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero)]
    exact Matrix.one_mulVec _
  have hCq :
      V.realPolarMatrix.mulVec (rationalRealVector n q) =
        integerVectorReal z := by
    rw [realPolarMatrix_mulVec_rationalRealVector, hCqRat]
    funext i
    norm_num [rationalRealVector, integerVectorReal]
  have hinv :
      V.realPolarMatrix⁻¹.mulVec (integerVectorReal z) =
        rationalRealVector n q := by
    rw [← hCq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr V.realPolarMatrix_det_ne_zero),
      Matrix.one_mulVec]
  have hcast :
      ((V.nativeRationalQuadraticForm q : ℚ) : ℝ) =
        V.realQuadraticFormValue (rationalRealVector n q) := by
    simp [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm,
      RationalQuadraticSpaceMatrix.realQuadraticFormValue,
      RationalQuadraticSpaceMatrix.realFormMatrix,
      Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVec,
      dotProduct, rationalRealVector]
  rw [hcast]
  have hpolar : V.realPolarMatrix = (2 : ℝ) • V.realFormMatrix := by
    ext i j
    simp [RationalQuadraticSpaceMatrix.realPolarMatrix,
      RationalQuadraticSpaceMatrix.realFormMatrix,
      RationalQuadraticSpaceMatrix.polarMatrix]
  have hform :
      V.realQuadraticFormValue (rationalRealVector n q) =
        (2 : ℝ)⁻¹ * dotProduct (rationalRealVector n q)
          (V.realPolarMatrix.mulVec (rationalRealVector n q)) := by
    rw [hpolar]
    simp only [RationalQuadraticSpaceMatrix.realQuadraticFormValue,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  rw [hform, hCq]
  unfold integerVectorMatrixQuadraticValue
  rw [hinv, dotProduct_comm]

/-- On the rectangular presentation of the polar-dual quotient, the
finite-adelic phase is exactly the real quadratic oscillation for `C⁻¹`.
The statement includes the discriminant-sized overcount. -/
theorem rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues_intCast_eq_oscillation
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (z : Fin n → ℤ) :
    rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues L t
        (fun i ↦ (z i : ZMod (t.den * L.polarDeterminant.natAbs))) =
      quadraticOscillation
        L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ (t : ℝ) z := by
  let V := L.rationalQuadraticSpaceMatrix
  let q : Fin n → ℚ :=
    V.polarMatrix⁻¹.mulVec (fun j ↦ (z j : ℚ))
  let y : FinitePolarDualAdeleVector L :=
    (finitePolarDualEquivIntegralCoordinates L).symm
      (fun i ↦ integerToIntegralFiniteAdele (z i))
  rw [rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues_intCast]
  change (V.rationalFiniteAdeleQuadraticPhase t y.1 : ℂ) = _
  rw [finitePolarDualEquivIntegralCoordinates_symm_intCast]
  have hvalue :
      V.finiteAdelicQuadraticFormValue
          (fun i ↦ algebraMap ℚ RationalFiniteAdele (q i)) =
        algebraMap ℚ RationalFiniteAdele (V.nativeRationalQuadraticForm q) := by
    simp [RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue,
      RationalQuadraticSpaceMatrix.finiteAdelicFormMatrix,
      RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm,
      Matrix.toQuadraticMap', Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVec,
      dotProduct, map_sum]
  unfold RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase
  rw [hvalue, ← map_mul]
  rw [rationalFiniteAdeleFourierChar_algebraMap]
  rw [Circle.coe_inv, Real.fourierChar_apply, quadraticOscillation,
    ← Complex.exp_neg]
  congr 1
  rw [Rat.cast_mul,
    nativeRationalQuadraticForm_polar_inv_intCast_eq_half]
  push_cast
  ring

/-! ## The two rational boundary Abel limits -/

/-- Approaching `-ⁱ/t` from the right half-plane turns the `C`-theta series
into the literal standard finite Gauss integral at the rational parameter
`-t⁻¹`.  Summability precedes the limit and the residue weight is the
existing finite-adelic character. -/
theorem tendsto_normalized_rationalGaussBoundaryTheta_eq_standardGauss
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    Tendsto
      (fun ρ : ℝ ↦
        (Real.sqrt
          (ρ ^ n *
            L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            shiftedMatrixGaussianSummand
              L.rationalQuadraticSpaceMatrix.realPolarMatrix
              (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z)
      (𝓝[>] 0)
      (𝓝
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (-t⁻¹))) := by
  let s : ℚ := -t⁻¹
  letI : NeZero s.den := ⟨s.den_nz⟩
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  let weight : (Fin n → ZMod s.den) → ℂ :=
    rationalFiniteAdeleIntegralQuadraticPhaseOnResidues L s
  have hbase := tendsto_periodicShiftedMatrixGaussian_along
    C L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef weight
      (fun ρ : ℝ ↦ ρ) (fun _ : ℝ ↦ 0)
      tendsto_id (by simp)
  have hidentified :
      Tendsto
        (fun ρ : ℝ ↦
          (Real.sqrt (ρ ^ n * C.det) : ℂ) *
            ∑' z : Fin n → ℤ,
              shiftedMatrixGaussianSummand C
                (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z)
        (𝓝[>] 0)
        (𝓝 ((((s.den : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
    apply hbase.congr'
    apply Filter.Eventually.of_forall
    intro ρ
    change
      (Real.sqrt (ρ ^ n * C.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            weight (fun i ↦ (z i : ZMod s.den)) *
              shiftedMatrixGaussianSummand C
                ((ρ : ℂ) + (0 : ℂ) * Complex.I) 0 z =
        (Real.sqrt (ρ ^ n * C.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            shiftedMatrixGaussianSummand C
              (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z
    congr 1
    apply tsum_congr
    intro z
    change
      weight (fun i ↦ (z i : ZMod s.den)) *
          shiftedMatrixGaussianSummand C
            (((ρ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0 z =
        shiftedMatrixGaussianSummand C
          (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z
    rw [show weight (fun i ↦ (z i : ZMod s.den)) =
        quadraticOscillation C (s : ℝ) z by
      exact
        rationalFiniteAdeleIntegralQuadraticPhaseOnResidues_intCast_eq_oscillation
          L s z]
    rw [show shiftedMatrixGaussianSummand C
        (((ρ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) 0 z =
        centeredMatrixGaussianSummand C ρ 0 z by
      rw [shiftedMatrixGaussianSummand, centeredMatrixGaussianSummand]
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Pi.zero_apply,
        sub_zero, Finset.sum_const_zero, mul_zero]
      rfl]
    rw [quadraticOscillation_mul_centeredGaussian_eq_shifted]
    congr 2
    simp [s, rationalGaussBoundaryParameter]
    rw [sub_eq_add_neg]
  simpa only [C, weight, s,
    rationalFiniteAdeleQuadraticGaussIntegral_eq_residueSum] using
      hidentified

private theorem polarDeterminant_mul_rectangularResidueAverage_eq_dualGauss
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (t : ℚ) (hn : n ≠ 0) :
    (L.polarDeterminant.natAbs : ℂ) *
        (((((t.den * L.polarDeterminant.natAbs : ℕ) : ℝ) ^ n : ℂ)⁻¹) *
          ∑ z,
            rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues
              L t z) =
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral
        t := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_rectangularResidueSum
      L t hn]
    have hden : (t.den : ℂ) ≠ 0 := by exact_mod_cast t.den_nz
    have hdisc : (L.polarDeterminant.natAbs : ℂ) ≠ 0 := by
      exact_mod_cast Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)
    push_cast
    simp only [pow_succ]
    field_simp
    rw [mul_pow]
    field_simp

/-- The reciprocal boundary theta for `C⁻¹`, with its
discriminant overcount restored, tends to the polar-dual finite
Gauss integral.  The small imaginary error is controlled relative to the
reciprocal real scale, not the external parameter `ρ`. -/
theorem tendsto_polarDeterminant_mul_normalized_rationalGaussBoundaryInvTheta_eq_dualGauss
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : n ≠ 0)
    {t : ℚ} (ht : t ≠ 0) :
    Tendsto
      (fun ρ : ℝ ↦
        (L.polarDeterminant.natAbs : ℂ) *
          ((Real.sqrt
            ((rationalGaussDualRealScale (t : ℝ) ρ) ^ n *
              L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.det) : ℂ) *
            ∑' z : Fin n → ℤ,
              shiftedMatrixGaussianSummand
                L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
                ((rationalGaussBoundaryParameter (t : ℝ) ρ)⁻¹) 0 z))
      (𝓝[>] 0)
      (𝓝
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral
          t)) := by
  let m : ℕ := t.den * L.polarDeterminant.natAbs
  letI : NeZero m :=
    ⟨mul_ne_zero t.den_nz
      (Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos))⟩
  let S := L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
  let weight : (Fin n → ZMod m) → ℂ :=
    rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues L t
  have hbase := tendsto_periodicShiftedMatrixGaussian_along
    S L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv weight
      (rationalGaussDualRealScale (t : ℝ))
      (rationalGaussDualImaginaryError (t : ℝ))
      (tendsto_rationalGaussDualRealScale_nhdsGT_zero (by exact_mod_cast ht))
      (tendsto_rationalGaussDualImaginaryError_div_realScale
        (by exact_mod_cast ht))
  have hidentified :
      Tendsto
        (fun ρ : ℝ ↦
          (Real.sqrt
            ((rationalGaussDualRealScale (t : ℝ) ρ) ^ n * S.det) : ℂ) *
            ∑' z : Fin n → ℤ,
              shiftedMatrixGaussianSummand S
                ((rationalGaussBoundaryParameter (t : ℝ) ρ)⁻¹) 0 z)
        (𝓝[>] 0)
        (𝓝 (((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r))) := by
    apply hbase.congr'
    apply Filter.Eventually.of_forall
    intro ρ
    change
      (Real.sqrt
        ((rationalGaussDualRealScale (t : ℝ) ρ) ^ n * S.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            weight (fun i ↦ (z i : ZMod m)) *
              shiftedMatrixGaussianSummand S
                ((rationalGaussDualRealScale (t : ℝ) ρ : ℂ) +
                  (rationalGaussDualImaginaryError (t : ℝ) ρ : ℂ) *
                    Complex.I) 0 z =
        (Real.sqrt
          ((rationalGaussDualRealScale (t : ℝ) ρ) ^ n * S.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            shiftedMatrixGaussianSummand S
              ((rationalGaussBoundaryParameter (t : ℝ) ρ)⁻¹) 0 z
    congr 1
    apply tsum_congr
    intro z
    rw [show weight (fun i ↦ (z i : ZMod m)) =
        quadraticOscillation S (t : ℝ) z by
      exact
        rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues_intCast_eq_oscillation
          L t z]
    rw [show shiftedMatrixGaussianSummand S
        ((rationalGaussDualRealScale (t : ℝ) ρ : ℂ) +
          (rationalGaussDualImaginaryError (t : ℝ) ρ : ℂ) *
            Complex.I) 0 z =
        quadraticOscillation S
            (rationalGaussDualImaginaryError (t : ℝ) ρ) z *
          centeredMatrixGaussianSummand S
            (rationalGaussDualRealScale (t : ℝ) ρ) 0 z by
      exact (quadraticOscillation_mul_centeredGaussian_eq_shifted
        S (rationalGaussDualRealScale (t : ℝ) ρ)
          (rationalGaussDualImaginaryError (t : ℝ) ρ) z).symm]
    rw [← mul_assoc]
    rw [show quadraticOscillation S (t : ℝ) z *
        quadraticOscillation S
            (rationalGaussDualImaginaryError (t : ℝ) ρ) z =
        quadraticOscillation S
          ((t : ℝ) + rationalGaussDualImaginaryError (t : ℝ) ρ) z by
      unfold quadraticOscillation
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring]
    rw [quadraticOscillation_mul_centeredGaussian_eq_shifted]
    rw [rationalGaussBoundaryParameter_inv]
  have hscaled := hidentified.const_mul (L.polarDeterminant.natAbs : ℂ)
  simpa only [S, weight, m,
    polarDeterminant_mul_rectangularResidueAverage_eq_dualGauss L t hn] using hscaled

end PositiveDefiniteIntegralLattice
