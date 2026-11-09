import SMSFormula.AffineLocalPhaseBound
import SMSFormula.RationalFiniteAdeleHaarScaling
import SMSFormula.FiniteFactorIdentification

/-!
# The shifted carrier: the two frequencies reconciled by moving the scale into the matrix

Translating a coset carrier `v + r Zhat^n` back to the standard one by `x = v + r y` would make the
quadratic frequency `t r^2` and the linear frequency `t r`, which are different, so the affine bound
-- stated at a single frequency -- would not apply directly.

The scale `r` need not go into the frequency at all: it goes into the matrix.  Writing the shifted
form out,

```text
Q_C(v + r y) = Q_(r^2 C)(y) + (2 r C v) . y + Q_C(v),
```

the frequency `t` is untouched, the quadratic matrix becomes `r^2 C` -- still the diagonal image of
an integer matrix -- the linear datum becomes `2 r C v`, and the constant `t Q_C(v)` is discarded by
the modulus.  So the affine bound applies verbatim, at the same conductor of the same frequency `t`.

What the linear datum costs is integrality of `r v`, and nothing else: `2 r C v = 2 C (r v)`, so an
integral matrix and an integral `r v` suffice.  That is a constraint on the coset, but one that can
always be arranged, since a compact open carrier has a bounded denominator and the decomposition
into cosets of `r Zhat^n` may be refined to any multiple of it.

What it costs in the constant is `|det(r^2 gram)|^n = (r^(2n) |polarDeterminant L|)^n`, a fixed number: the
conductor `m` still enters only as `(m^n)^(-1)`, so the summability against the totient multiplicity
above rank four is untouched.  This is exactly why the scale had to go into the matrix: had it gone
into the frequency, the conductor variable would have been reparametrized.

Scope.  Nothing here performs the ambient change of variables -- no carrier indicator is
integrated, no compact open set is decomposed into cosets, and the finite Haar scaling `r^(-n)` that
such a substitution produces is not applied.  The statement proved is about the local integral of
the shifted phase, which is what that substitution yields.  Injectivity of the residue character is
a hypothesis, and the bound is an upper bound.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

section Affine

open MeasureTheory SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## The bound at an arbitrary integral model -/

/-- The affine bound at an arbitrary integral model: the lattice's own form matrix played no role
beyond being the diagonal image of a symmetric nonsingular integer matrix, so the bound holds at any
such matrix with its own determinant as the constant. -/
theorem norm_sq_integral_scaledAffine_integralModel_le (m : ℕ) [NeZero m]
    {H : Matrix (Fin n) (Fin n) ℤ} (hsymm : H.IsSymm) (hdet : H.det ≠ 0)
    {l : Fin n → RationalFiniteAdele} (hl : ∀ i, l i ∈ integralFiniteAdeleSubring)
    {c : RationalFiniteAdele} (hc : c ∈ integralFiniteAdeleSubring)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, complexFiniteChar (scaledAffine t (integralModelMatrix H) l c x)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * (((H + H).det.natAbs : ℝ)) ^ n := by
  have hm : m ≠ 0 := NeZero.ne m
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [integral_scaledAffine_eq_residueChar_sum m (integralModelMatrix_mem H) hl hc htm]
  have hsum := norm_sq_sum_char_reducedMatrix_le (n := n) m hm hinj hsymm hdet
    (reducedVector m hm l hl) (ringResidueOf m hm ⟨c, hc⟩)
  rw [norm_smul, mul_pow]
  have hnormsmul : ‖((m ^ n : ℝ))⁻¹‖ ^ 2 = (((m : ℝ) ^ n)⁻¹) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnormsmul]
  have hstep : (((m : ℝ) ^ n)⁻¹) ^ 2 *
      ‖∑ w : Fin n → ZMod m, residueChar m hm htm
        (affineQuadratic (reducedMatrix m hm (integralModelMatrix H)
          (integralModelMatrix_mem H)) (reducedVector m hm l hl)
          (ringResidueOf m hm ⟨c, hc⟩) w)‖ ^ 2 ≤
      (((m : ℝ) ^ n)⁻¹) ^ 2 * ((m : ℝ) ^ n * (((H + H).det.natAbs : ℝ)) ^ n) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-! ## The shifted vector and the affine data it produces -/

/-- The shift: an arbitrary finite-adelic vector `v` plus `r` times an integral vector -- the
general point of the coset `v + r Zhat^n`. -/
noncomputable def shiftedCoord (v : Fin n → RationalFiniteAdele) (r : ℕ)
    (y : Fin n → IntegralFiniteAdele) : Fin n → RationalFiniteAdele :=
  v + (r : RationalFiniteAdele) • coordCoe y

/-- The linear datum the shift produces: `2 r C v`, which is `2 C (r v)`. -/
noncomputable def shiftLinear (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (v : Fin n → RationalFiniteAdele) (r : ℕ) : Fin n → RationalFiniteAdele :=
  (2 * (r : RationalFiniteAdele)) • Matrix.mulVec C v

/-- Scaling the matrix scales the form. -/
theorem dotQuadratic_smul {R : Type*} [CommRing R] (rho : R)
    (C : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    dotQuadratic (rho • C) x = rho * dotQuadratic C x := by
  simp only [dotQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The shifted form, expanded: the scale goes into the matrix and the linear datum, never into the
frequency.  Symmetry is what merges the two cross terms. -/
theorem dotQuadratic_shifted {R : Type*} [CommRing R] {C : Matrix (Fin n) (Fin n) R}
    (hC : C.IsSymm) (v w : Fin n → R) (rho : R) :
    dotQuadratic C (v + rho • w) =
      dotQuadratic (rho ^ 2 • C) w +
        dotProduct ((2 * rho) • Matrix.mulVec C v) w + dotQuadratic C v := by
  have hcross : dotProduct v (Matrix.mulVec C w) = dotProduct w (Matrix.mulVec C v) :=
    dotProduct_mulVec_comm_of_isSymm hC v w
  have hcomm : dotProduct (Matrix.mulVec C v) w = dotProduct w (Matrix.mulVec C v) :=
    dotProduct_comm _ _
  simp only [dotQuadratic, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.smul_mulVec,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hcomm]
  rw [hcross]
  ring

/-! ## Integrality of the linear datum -/

/-- The linear datum is integral as soon as `r v` is: `2 r C v = 2 C (r v)`, a finite sum of
products of integral elements. -/
theorem shiftLinear_mem_integral {C : Matrix (Fin n) (Fin n) RationalFiniteAdele}
    (hC : ∀ i j, C i j ∈ integralFiniteAdeleSubring) {v : Fin n → RationalFiniteAdele} {r : ℕ}
    (hrv : ∀ j, (r : RationalFiniteAdele) * v j ∈ integralFiniteAdeleSubring) (i : Fin n) :
    shiftLinear C v r i ∈ integralFiniteAdeleSubring := by
  have htwo : (2 : RationalFiniteAdele) ∈ integralFiniteAdeleSubring := by simp
  have hsum : shiftLinear C v r i =
      ∑ j, (2 : RationalFiniteAdele) * (C i j * ((r : RationalFiniteAdele) * v j)) := by
    simp only [shiftLinear, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsum]
  exact Subring.sum_mem _ fun j _ ↦
    Subring.mul_mem _ htwo (Subring.mul_mem _ (hC i j) (hrv j))

/-! ## The scaled integral model -/

/-- Scaling an integer matrix commutes with the diagonal image. -/
theorem integralModelMatrix_nsmul_sq (H : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    integralModelMatrix (((r : ℤ) ^ 2) • H) =
      ((r : RationalFiniteAdele) ^ 2) • integralModelMatrix H := by
  refine Matrix.ext fun i j ↦ ?_
  show algebraMap ℤ RationalFiniteAdele (((r : ℤ) ^ 2) * H i j) =
    ((r : RationalFiniteAdele) ^ 2) * algebraMap ℤ RationalFiniteAdele (H i j)
  rw [map_mul]
  congr 1
  push_cast
  ring

/-- The scaled matrix is still symmetric. -/
theorem isSymm_zsmul {H : Matrix (Fin n) (Fin n) ℤ} (hsymm : H.IsSymm) (z : ℤ) :
    (z • H).IsSymm := by
  show Matrix.transpose (z • H) = z • H
  rw [Matrix.transpose_smul, hsymm.eq]

/-- And still nonsingular at a nonzero scale. -/
theorem det_zsmul_ne_zero {H : Matrix (Fin n) (Fin n) ℤ} (hdet : H.det ≠ 0) {z : ℤ} (hz : z ≠ 0) :
    (z • H).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hz) hdet

/-- The constant the scaled model produces: `|det(r^2 gram)| = r^(2n) |polarDeterminant L|`. -/
theorem det_zsmul_add_self_natAbs (L : PositiveDefiniteIntegralLattice n) (r : ℕ) :
    ((((r : ℤ) ^ 2) • L.pairingMatrix + ((r : ℤ) ^ 2) • L.pairingMatrix).det.natAbs) =
      r ^ (2 * n) * L.polarDeterminant.natAbs := by
  have hadd : (((r : ℤ) ^ 2) • L.pairingMatrix + ((r : ℤ) ^ 2) • L.pairingMatrix) =
      ((r : ℤ) ^ 2) • L.polarGramMatrix := by
    rw [polarGramMatrix_eq_pairingMatrix_add_self L, smul_add]
  rw [hadd, Matrix.det_smul, show L.polarGramMatrix.det = L.polarDeterminant from rfl, Int.natAbs_mul]
  congr 1
  rw [← pow_mul, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin]

/-! ## The bound on the shifted local integral -/

/-- The shifted local phase is an affine phase at the same frequency, plus a constant. -/
theorem scaledQuadratic_shiftedCoord (L : PositiveDefiniteIntegralLattice n) (t : RationalFiniteAdele)
    (v : Fin n → RationalFiniteAdele) (r : ℕ) (y : Fin n → IntegralFiniteAdele) :
    t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y) =
      scaledAffine t (integralModelMatrix (((r : ℤ) ^ 2) • L.pairingMatrix))
          (shiftLinear (integralModelMatrix L.pairingMatrix) v r) 0 y +
        t * dotQuadratic (integralModelMatrix L.pairingMatrix) v := by
  have hsymm : (integralModelMatrix L.pairingMatrix).IsSymm := by
    refine Matrix.ext fun i j ↦ ?_
    show algebraMap ℤ RationalFiniteAdele (L.pairingMatrix j i) =
      algebraMap ℤ RationalFiniteAdele (L.pairingMatrix i j)
    rw [L.form_symm.apply j i]
  rw [show shiftedCoord v r y = v + (r : RationalFiniteAdele) • coordCoe y from rfl,
    dotQuadratic_shifted hsymm v (coordCoe y) (r : RationalFiniteAdele),
    integralModelMatrix_nsmul_sq]
  show _ = t * (dotQuadratic (((r : RationalFiniteAdele) ^ 2) • integralModelMatrix L.pairingMatrix)
      (coordCoe y) +
      dotProduct (shiftLinear (integralModelMatrix L.pairingMatrix) v r) (coordCoe y) + 0) + _
  simp only [shiftLinear]
  ring

/-- The payoff: the local integral of the shifted phase obeys the same conductor bound, with a
fixed constant.  The frequency, and hence its conductor, is untouched; the scale `r` lives entirely
in the matrix and the linear datum. -/
theorem norm_sq_integral_shiftedPhase_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (r : ℕ) (hr : r ≠ 0) (v : Fin n → RationalFiniteAdele)
    (hrv : ∀ j, (r : RationalFiniteAdele) * v j ∈ integralFiniteAdeleSubring)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ y, complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y))
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2 ≤
      (((m : ℝ)) ^ n)⁻¹ * (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n := by
  have hdetF : L.pairingMatrix.det ≠ 0 := by
    have := L.pairingDeterminant_pos
    simpa [PositiveDefiniteIntegralLattice.pairingDeterminant] using ne_of_gt this
  have hz : ((r : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 hr)
  rw [show (∫ y, complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y))
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)) =
      ∫ y, complexFiniteChar
        (scaledAffine t (integralModelMatrix (((r : ℤ) ^ 2) • L.pairingMatrix))
            (shiftLinear (integralModelMatrix L.pairingMatrix) v r) 0 y +
          t * dotQuadratic (integralModelMatrix L.pairingMatrix) v)
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) from by
      simp only [scaledQuadratic_shiftedCoord L t v r],
    norm_integral_complexFiniteChar_add_const]
  have hkey := norm_sq_integral_scaledAffine_integralModel_le (n := n) m
    (isSymm_zsmul L.form_symm _) (det_zsmul_ne_zero hdetF hz)
    (shiftLinear_mem_integral (integralModelMatrix_mem L.pairingMatrix) hrv)
    (Subring.zero_mem _) htm hinj
  rw [det_zsmul_add_self_natAbs L r] at hkey
  exact hkey

end Affine

section Coset

open MeasureTheory Matrix RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The coset change of variables -/

local instance coordinateAddHaarMeasure_isAddLeftInvariant (e : ℕ) :
    Measure.IsAddLeftInvariant (rationalFiniteAdeleCoordinateAddHaarMeasure e) := by
  letI : Measure.IsAddHaarMeasure rationalFiniteAdeleAddHaarMeasure :=
    rationalFiniteAdeleAddHaarMeasure_isAddHaarMeasure
  refine ⟨fun z => ?_⟩
  change Measure.map (fun x => z + x)
      (Measure.pi fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure) =
    Measure.pi fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure
  exact (measurePreserving_pi
    (fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure)
    (fun _ : Fin e => rationalFiniteAdeleAddHaarMeasure)
    (fun i => measurePreserving_add_left rationalFiniteAdeleAddHaarMeasure (z i))).map_eq

/-- The substitution is invertible: `v + r ((x - v)/r) = x`, because `r` is a unit in the finite
adeles. -/
theorem shift_coordScale_sub (v x : Fin n → RationalFiniteAdele) {r : ℕ} (hr : r ≠ 0) :
    v + (r : RationalFiniteAdele) •
        rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v) = x := by
  have hrq : ((r : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hcast : (r : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((r : ℚ)) := by
    norm_num
  funext i
  show v i + (r : RationalFiniteAdele) *
    (algebraMap ℚ RationalFiniteAdele ((r : ℚ))⁻¹ * (x i - v i)) = x i
  rw [hcast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hrq, map_one, one_mul]
  ring

/-- The coset indicator, as the standard integral-vector indicator pulled back along the
substitution: it is `1` exactly on `v + r Zhat^n`. -/
noncomputable def cosetIndicator (v : Fin n → RationalFiniteAdele) (r : ℕ)
    (x : Fin n → RationalFiniteAdele) : ℂ :=
  rationalFiniteAdeleVectorIntegralIndicator
    (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v))

/-- It is one on the coset, so the carrier is not empty. -/
theorem cosetIndicator_shiftedCoord (v : Fin n → RationalFiniteAdele) {r : ℕ} (hr : r ≠ 0)
    (y : Fin n → IntegralFiniteAdele) : cosetIndicator v r (shiftedCoord v r y) = 1 := by
  have hrq : ((r : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hcast : (r : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((r : ℚ)) := by
    norm_num
  have hval : rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹
      (shiftedCoord v r y - v) = coordCoe y := by
    funext i
    show algebraMap ℚ RationalFiniteAdele ((r : ℚ))⁻¹ *
      (v i + (r : RationalFiniteAdele) * ((y i : RationalFiniteAdele)) - v i) = _
    rw [show v i + (r : RationalFiniteAdele) * ((y i : RationalFiniteAdele)) - v i =
      (r : RationalFiniteAdele) * ((y i : RationalFiniteAdele)) from by ring, hcast,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ hrq, map_one, one_mul]
    rfl
  rw [cosetIndicator, hval]
  exact rationalFiniteAdeleVectorIntegralIndicator_of_mem fun i ↦ (y i).property

/-- The shifted phase is measurable -- the character is continuous and the form a finite sum of
products. -/
theorem measurable_shiftedPhase (C : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    (t : RationalFiniteAdele) (v : Fin n → RationalFiniteAdele) (r : ℕ) :
    Measurable (fun y : Fin n → RationalFiniteAdele ↦
      complexFiniteChar (t * dotQuadratic C (v + (r : RationalFiniteAdele) • y))) := by
  have hc : Continuous (fun y : Fin n → RationalFiniteAdele ↦
      rationalFiniteAdeleFourierChar
        (t * dotQuadratic C (v + (r : RationalFiniteAdele) • y))) := by
    apply continuous_rationalFiniteAdeleFourierChar.comp
    unfold dotQuadratic Matrix.mulVec dotProduct
    fun_prop
  exact hc.subtype_val.measurable

/-- The coset change of variables: the ambient integral of the frequency phase against the coset
indicator is `r^(-n)` times the local integral of the shifted phase.  Translation invariance and the
existing finite Haar scaling supply the two steps; the integral-vector bridge supplies the third.
The frequency `t` never moves. -/
theorem integral_cosetPhase_eq_shiftedLocal (L : PositiveDefiniteIntegralLattice n) (t : RationalFiniteAdele)
    (v : Fin n → RationalFiniteAdele) {r : ℕ} (hr : r ≠ 0) :
    (∫ x, cosetIndicator v r x *
        complexFiniteChar (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) =
      ((r : ℂ))⁻¹ ^ n *
        ∫ y, complexFiniteChar
            (t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y))
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hq : ((r : ℚ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hr)
  set C := integralModelMatrix L.pairingMatrix with hC
  set F : (Fin n → RationalFiniteAdele) → ℂ := fun y ↦
    complexFiniteChar (t * dotQuadratic C (v + (r : RationalFiniteAdele) • y)) *
      rationalFiniteAdeleVectorIntegralIndicator y with hF
  have hpt : ∀ x : Fin n → RationalFiniteAdele,
      cosetIndicator v r x * complexFiniteChar (t * dotQuadratic C x) =
        F (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v)) := by
    intro x
    rw [hF]
    show _ = complexFiniteChar (t * dotQuadratic C
        (v + (r : RationalFiniteAdele) •
          rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v))) *
      rationalFiniteAdeleVectorIntegralIndicator
        (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v))
    rw [shift_coordScale_sub v x hr, cosetIndicator]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    show (∫ x, F (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ (x - v))
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)) =
      ∫ x, F (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) from
      integral_sub_right_eq_self
        (fun x ↦ F (rationalFiniteAdeleCoordinateScale ((r : ℚ))⁻¹ x)) v,
    integral_rationalFiniteAdeleCoordinateScale_inv n hr hq F,
    hF, integral_ambient_weighted_eq_local _ (measurable_shiftedPhase C t v r)]
  rfl

/-- The payoff: the finite factor of a coset carrier obeys a conductor bound of the same shape --
`(m^n)^(-1/2)` times a constant depending only on the scale, the rank and the discriminant.  The
frequency and its conductor are untouched, so this is exactly the shape the conductor partition
consumes. -/
theorem norm_integral_cosetPhase_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    {r : ℕ} (hr : r ≠ 0) (v : Fin n → RationalFiniteAdele)
    (hrv : ∀ j, (r : RationalFiniteAdele) * v j ∈ integralFiniteAdeleSubring)
    {t : RationalFiniteAdele}
    (htm : t * (m : RationalFiniteAdele) ∈ integralFiniteAdeleSubring)
    (hinj : Function.Injective (residueChar m (NeZero.ne m) htm)) :
    ‖∫ x, cosetIndicator v r x *
        complexFiniteChar (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n)‖ ≤
      ((r : ℝ))⁻¹ ^ n *
        Real.sqrt ((((m : ℝ)) ^ n)⁻¹ * (((r ^ (2 * n) * L.polarDeterminant.natAbs : ℕ) : ℝ)) ^ n) := by
  rw [integral_cosetPhase_eq_shiftedLocal L t v hr, norm_mul]
  have hconst : ‖((r : ℂ))⁻¹ ^ n‖ = ((r : ℝ))⁻¹ ^ n := by
    rw [norm_pow, norm_inv, Complex.norm_natCast]
  rw [hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsq := norm_sq_integral_shiftedPhase_le L m r hr v hrv htm hinj
  calc ‖∫ y, complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y))
        ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖
      = Real.sqrt (‖∫ y, complexFiniteChar
          (t * dotQuadratic (integralModelMatrix L.pairingMatrix) (shiftedCoord v r y))
          ∂(integralFiniteAdeleCoordinateAddHaarMeasure n)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

end Coset

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
