import SMSFormula.RationalLatticeDiscriminantTheta
import SMSFormula.UpperHalfPlaneWeightTwoConstantTerm
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Invariant vectors of the discriminant representation vanish at the origin

Let `L` be a positive definite integral lattice of rank four with discriminant group
`A = L^#/L` (`PolarDiscriminantGroup`).  Let `c : A → ℂ` be invariant under the transposed theta
operators:

* `c(a) e(q(a)) = c(a)` (the `T`-operator is diagonal with entries `e(q(a))`);
* `c(a) = -√det(S⁻¹) Σ_{a₀} c(a₀) e(-B(a₀, a))` (the `S`-operator, with the signature-four sign).

Then `c(0) = 0` (`polarDeterminant_apply_zero_eq_zero_of_invariant`).  This is the statement
`Pe₀ = 0`, in the form "every invariant vector has zero origin
component".

Proof: `f(τ) = Σ_a c(a) θ_a(τ)` satisfies `f(τ + 1) = f(τ)` (T-law) and `f(-1/τ) = τ² f(τ)`
(S-law; `((-iτ)^{1/2})⁴ = -τ²` in rank four).  Its constant term is `c(0)`, since the only vector of
dual norm zero is `0` and every nonzero dual norm is at least `1/(2 det S)` (the adjugate is
integral).  A termwise primitive exists, so the period argument
(`SMSFormula.WeightTwoConstantTerm.constTerm_eq_zero`) gives `c(0) = 0`.  No contour integral and
no finite-level factorization is used.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-! ## The dual norm: nonnegativity and the integral lower bound -/

theorem integerVectorReal_ne_zero {u : Fin n → ℤ} (hu : u ≠ 0) : integerVectorReal u ≠ 0 := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [integerVectorReal, Pi.zero_apply] at this
  exact_mod_cast this

@[simp]
theorem integerVectorReal_zero : integerVectorReal (0 : Fin n → ℤ) = 0 := by
  funext i; simp [integerVectorReal]

theorem dotProduct_realPolarMatrix_inv_pos {u : Fin n → ℤ} (hu : u ≠ 0) :
    0 < integerVectorReal u ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ
      integerVectorReal u := by
  have h := (L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv).dotProduct_mulVec_pos
    (integerVectorReal_ne_zero hu)
  simpa using h

theorem polarDualNorm_nonneg (u : Fin n → ℤ) : 0 ≤ L.polarDualNorm u := by
  by_cases hu : u = 0
  · subst hu
    simp [polarDualNorm]
  · unfold polarDualNorm
    exact div_nonneg (L.dotProduct_realPolarMatrix_inv_pos hu).le (by norm_num)

theorem realPolarMatrix_det_pos : 0 < L.rationalQuadraticSpaceMatrix.realPolarMatrix.det :=
  L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.det_pos

/-- The integral lower bound: every nonzero dual norm is at least `1/(2 det S)`. -/
theorem polarDualNorm_ge {u : Fin n → ℤ} (hu : u ≠ 0) :
    1 / (2 * L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) ≤ L.polarDualNorm u := by
  set S := L.rationalQuadraticSpaceMatrix.realPolarMatrix with hSdef
  set x := integerVectorReal u
  have hdet : 0 < S.det := L.realPolarMatrix_det_pos
  have hSinv : S⁻¹ = (S.det)⁻¹ • S.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hadj : S.adjugate = L.polarGramMatrix.adjugate.map (Int.cast : ℤ → ℝ) := by
    rw [hSdef, L.realPolarMatrix_eq_map_polarGramMatrix]
    exact ((Int.castRingHom ℝ).map_adjugate L.polarGramMatrix).symm
  set k : ℤ := u ⬝ᵥ (L.polarGramMatrix.adjugate *ᵥ u) with hkdef
  have hk : x ⬝ᵥ S.adjugate *ᵥ x = (k : ℝ) := by
    rw [hadj, hkdef]
    simp [x, integerVectorReal, dotProduct, Matrix.mulVec]
  have hpos : 0 < x ⬝ᵥ S⁻¹ *ᵥ x := L.dotProduct_realPolarMatrix_inv_pos hu
  have hx : x ⬝ᵥ S⁻¹ *ᵥ x = (S.det)⁻¹ * k := by
    rw [hSinv, Matrix.smul_mulVec, dotProduct_smul, hk, smul_eq_mul]
  have hk0 : (0 : ℝ) < k := by
    rw [hx] at hpos
    exact (mul_pos_iff_of_pos_left (inv_pos.2 hdet)).1 hpos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Int.cast_pos.1 hk0 : (0 : ℤ) < k)
  change 1 / (2 * S.det) ≤ (x ⬝ᵥ S⁻¹ *ᵥ x) / 2
  rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (S.det)⁻¹ * k * (2 * S.det) = 2 * k := by field_simp
  nlinarith

/-! ## The real majorant -/

/-- The majorant `exp(-2π y q(S⁻¹u))`. -/
def polarThetaMajorant (y : ℝ) (u : Fin n → ℤ) : ℝ :=
  Real.exp (-2 * Real.pi * y * L.polarDualNorm u)

theorem summable_polarThetaMajorant {y : ℝ} (hy : 0 < y) : Summable (L.polarThetaMajorant y) := by
  have h := (summable_shiftedMatrixGaussianSummand_zero_fintype
    L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv hy).norm
  refine h.congr fun u ↦ ?_
  rw [shiftedMatrixGaussianSummand, Complex.norm_exp, polarThetaMajorant, polarDualNorm]
  congr 1
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  simp [Complex.mul_re]
  ring

theorem norm_exp_polarDualNorm (τ : ℂ) (u : Fin n → ℤ) :
    ‖exp (2 * Real.pi * I * τ * (L.polarDualNorm u : ℂ))‖ = L.polarThetaMajorant τ.im u := by
  rw [Complex.norm_exp, polarThetaMajorant]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem polarThetaMajorant_anti {y y' : ℝ} (h : y ≤ y') (u : Fin n → ℤ) :
    L.polarThetaMajorant y' u ≤ L.polarThetaMajorant y u := by
  unfold polarThetaMajorant
  apply Real.exp_le_exp.2
  have := L.polarDualNorm_nonneg u
  have hpi := Real.pi_pos
  nlinarith [mul_nonneg (mul_nonneg hpi.le this) (sub_nonneg.2 h)]

/-! ## The theta combination as one series -/

/-- The theta combination `f(τ) = Σ_a c(a) θ_a(τ)`. -/
def polarThetaCombination (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ) : ℂ :=
  ∑ a, c a * L.polarClassTheta τ a

/-- The coefficient bound `Σ_a ‖c a‖`. -/
def polarCoeffBound (c : L.PolarDiscriminantGroup → ℂ) : ℝ := ∑ a, ‖c a‖

theorem norm_le_polarCoeffBound (c : L.PolarDiscriminantGroup → ℂ) (a : L.PolarDiscriminantGroup) :
    ‖c a‖ ≤ L.polarCoeffBound c :=
  Finset.single_le_sum (f := fun a ↦ ‖c a‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)

/-- The summand `c([u]) e(τ q(S⁻¹u))`. -/
def polarCombinationSummand (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ) (u : Fin n → ℤ) : ℂ :=
  c (u : L.PolarDiscriminantGroup) * exp (2 * Real.pi * I * τ * (L.polarDualNorm u : ℂ))

theorem norm_polarCombinationSummand_le (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ)
    (u : Fin n → ℤ) :
    ‖L.polarCombinationSummand c τ u‖ ≤ L.polarCoeffBound c * L.polarThetaMajorant τ.im u := by
  rw [polarCombinationSummand, norm_mul, L.norm_exp_polarDualNorm]
  exact mul_le_mul_of_nonneg_right (L.norm_le_polarCoeffBound c _)
    (Real.exp_pos _).le

theorem summable_polarCombinationSummand (c : L.PolarDiscriminantGroup → ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) : Summable (L.polarCombinationSummand c τ) :=
  Summable.of_norm_bounded ((L.summable_polarThetaMajorant hτ).mul_left _)
    (L.norm_polarCombinationSummand_le c τ)

/-- The theta combination is the single series `Σ_u c([u]) e(τ q(S⁻¹u))`. -/
theorem polarThetaCombination_eq_tsum (c : L.PolarDiscriminantGroup → ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    L.polarThetaCombination c τ = ∑' u, L.polarCombinationSummand c τ u := by
  have hsum := L.summable_polarCombinationSummand c hτ
  let e := Equiv.sigmaFiberEquiv (fun u : Fin n → ℤ ↦ (u : L.PolarDiscriminantGroup))
  rw [← e.tsum_eq]
  refine (((hsum.comp_injective e.injective).tsum_sigma).trans ?_).symm
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  unfold polarClassTheta
  rw [← tsum_mul_left]
  refine tsum_congr fun ⟨u, hu⟩ ↦ ?_
  subst hu
  rfl

/-! ## The T- and S-laws of the combination -/

theorem polarThetaCombination_add_one (c : L.PolarDiscriminantGroup → ℂ)
    (hT : ∀ a, c a * L.polarDiscNormChar a = c a) (τ : ℂ) :
    L.polarThetaCombination c (τ + 1) = L.polarThetaCombination c τ := by
  unfold polarThetaCombination
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [L.polarClassTheta_add_one, ← mul_assoc, hT a]

theorem cpow_half_pow_four (b : ℂ) : (b ^ (1 / 2 : ℂ)) ^ 4 = b ^ 2 := by
  have h : (b ^ ((2 : ℕ)⁻¹ : ℂ)) ^ 2 = b := Complex.cpow_nat_inv_pow b (by norm_num)
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  push_cast at h ⊢
  rw [h]

theorem polarThetaCombination_neg_inv (L : PositiveDefiniteIntegralLattice 4) (c : L.PolarDiscriminantGroup → ℂ)
    (hS : ∀ a, c a = -(Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) *
      ∑ a₀, c a₀ * L.polarDiscPairingChar a₀ a) {τ : ℂ} (hτ : 0 < τ.im) :
    L.polarThetaCombination c (-τ⁻¹) = τ ^ 2 * L.polarThetaCombination c τ := by
  unfold polarThetaCombination
  simp only [L.polarClassTheta_neg_inv hτ, cpow_half_pow_four]
  set K := (Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ)
  have hlhs : ∑ a₀, c a₀ * ((-I * τ) ^ 2 * K * ∑ a, L.polarDiscPairingChar a₀ a *
        L.polarClassTheta τ a) =
      (-I * τ) ^ 2 * K * ∑ a, (∑ a₀, c a₀ * L.polarDiscPairingChar a₀ a) *
        L.polarClassTheta τ a := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun a₀ _ ↦ ?_
    ring
  rw [hlhs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hS a]
  have hI : (-I * τ) ^ 2 = -τ ^ 2 := by
    rw [mul_pow, neg_sq, I_sq]; ring
  rw [hI]
  ring

/-! ## The analytic inputs of the period argument -/

theorem isOpen_imGt (y : ℝ) : IsOpen {τ : ℂ | y < τ.im} := isOpen_lt continuous_const continuous_im

theorem isPreconnected_imGt (y : ℝ) : IsPreconnected {τ : ℂ | y < τ.im} :=
  (convex_halfSpace_gt Complex.imLm.isLinear y).isPreconnected

theorem continuousOn_polarThetaCombination (c : L.PolarDiscriminantGroup → ℂ) :
    ContinuousOn (L.polarThetaCombination c) upperHalfSet := by
  intro τ hτ
  have hτ' : 0 < τ.im := hτ
  set t := {z : ℂ | τ.im / 2 < z.im}
  have hτt : τ ∈ t := by change τ.im / 2 < τ.im; linarith
  have hcont : ContinuousOn (fun z ↦ ∑' u, L.polarCombinationSummand c z u) t := by
    refine continuousOn_tsum (u := fun u ↦ L.polarCoeffBound c * L.polarThetaMajorant (τ.im / 2) u)
      (fun u ↦ ?_) ((L.summable_polarThetaMajorant (by linarith)).mul_left _) fun u z hz ↦ ?_
    · exact (continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_id).mul continuous_const))).continuousOn
    · refine (L.norm_polarCombinationSummand_le c z u).trans ?_
      exact mul_le_mul_of_nonneg_left (L.polarThetaMajorant_anti (le_of_lt hz) u)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have heq : Set.EqOn (L.polarThetaCombination c) (fun z ↦ ∑' u, L.polarCombinationSummand c z u) t :=
    fun z hz ↦ L.polarThetaCombination_eq_tsum c (by change τ.im / 2 < z.im at hz; linarith)
  exact ((hcont.congr heq).continuousAt ((isOpen_imGt _).mem_nhds hτt)).continuousWithinAt

/-- The primitive summand: `c([u]) e(τ q)/(2πi q)` for `u ≠ 0`, and `0` at `u = 0`. -/
def polarPrimitiveSummand (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ) (u : Fin n → ℤ) : ℂ :=
  if u = 0 then 0 else
    L.polarCombinationSummand c τ u / (2 * Real.pi * I * (L.polarDualNorm u : ℂ))

/-- Its derivative: the combination summand off the origin. -/
def polarPrimitiveDerivSummand (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ) (u : Fin n → ℤ) : ℂ :=
  if u = 0 then 0 else L.polarCombinationSummand c τ u

theorem polarDualNorm_ne_zero {u : Fin n → ℤ} (hu : u ≠ 0) : (L.polarDualNorm u : ℂ) ≠ 0 := by
  have h := L.polarDualNorm_ge hu
  have hdet := L.realPolarMatrix_det_pos
  have : 0 < L.polarDualNorm u := lt_of_lt_of_le (by positivity) h
  exact_mod_cast this.ne'

theorem hasDerivAt_polarPrimitiveSummand (c : L.PolarDiscriminantGroup → ℂ) (u : Fin n → ℤ)
    (τ : ℂ) :
    HasDerivAt (fun z ↦ L.polarPrimitiveSummand c z u) (L.polarPrimitiveDerivSummand c τ u) τ := by
  unfold polarPrimitiveSummand polarPrimitiveDerivSummand
  by_cases hu : u = 0
  · simp only [hu, if_true]
    exact hasDerivAt_const _ _
  simp only [hu, if_false]
  have hN := L.polarDualNorm_ne_zero hu
  have hk : (2 * Real.pi * I * (L.polarDualNorm u : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hN, this, I_ne_zero]
  have hlin : HasDerivAt (fun z : ℂ ↦ 2 * Real.pi * I * z * (L.polarDualNorm u : ℂ))
      (2 * Real.pi * I * (L.polarDualNorm u : ℂ)) τ := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using
      (hasDerivAt_id τ).const_mul (2 * Real.pi * I * (L.polarDualNorm u : ℂ))
  have hexp := (hlin.cexp.const_mul (c (u : L.PolarDiscriminantGroup))).div_const
    (2 * Real.pi * I * (L.polarDualNorm u : ℂ))
  convert hexp using 1
  unfold polarCombinationSummand
  field_simp

theorem norm_polarPrimitiveDerivSummand_le (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ)
    (u : Fin n → ℤ) :
    ‖L.polarPrimitiveDerivSummand c τ u‖ ≤ L.polarCoeffBound c * L.polarThetaMajorant τ.im u := by
  unfold polarPrimitiveDerivSummand
  split_ifs
  · rw [norm_zero]; exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Real.exp_pos _).le
  · exact L.norm_polarCombinationSummand_le c τ u

theorem norm_polarPrimitiveSummand_le (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ)
    (u : Fin n → ℤ) :
    ‖L.polarPrimitiveSummand c τ u‖ ≤
      (2 * L.rationalQuadraticSpaceMatrix.realPolarMatrix.det / (2 * Real.pi)) *
        (L.polarCoeffBound c * L.polarThetaMajorant τ.im u) := by
  have hdet := L.realPolarMatrix_det_pos
  have hB : 0 ≤ L.polarCoeffBound c * L.polarThetaMajorant τ.im u :=
    mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Real.exp_pos _).le
  unfold polarPrimitiveSummand
  split_ifs with hu
  · rw [norm_zero]; exact mul_nonneg (by positivity) hB
  have hge := L.polarDualNorm_ge hu
  have hNpos : 0 < L.polarDualNorm u := lt_of_lt_of_le (by positivity) hge
  rw [norm_div]
  have hden : ‖2 * (Real.pi : ℂ) * I * (L.polarDualNorm u : ℂ)‖ = 2 * Real.pi * L.polarDualNorm u := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hNpos]
    norm_num
  rw [hden, div_le_iff₀ (by positivity)]
  refine (L.norm_polarCombinationSummand_le c τ u).trans ?_
  have h1 : 1 ≤ (2 * L.rationalQuadraticSpaceMatrix.realPolarMatrix.det / (2 * Real.pi)) *
      (2 * Real.pi * L.polarDualNorm u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hge
    nlinarith [Real.pi_pos]
  nlinarith

/-- The primitive `G(τ) = c(0) τ + Σ_{u ≠ 0} c([u]) e(τ q)/(2πi q)`. -/
def polarThetaPrimitive (c : L.PolarDiscriminantGroup → ℂ) (τ : ℂ) : ℂ :=
  c 0 * τ + ∑' u, L.polarPrimitiveSummand c τ u

theorem tsum_polarCombinationSummand_eq (c : L.PolarDiscriminantGroup → ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ∑' u, L.polarCombinationSummand c τ u = c 0 + ∑' u, L.polarPrimitiveDerivSummand c τ u := by
  have hsum := L.summable_polarCombinationSummand c hτ
  have hsplit : L.polarCombinationSummand c τ =
      fun u ↦ (if u = 0 then c 0 else 0) + L.polarPrimitiveDerivSummand c τ u := by
    funext u
    unfold polarPrimitiveDerivSummand
    by_cases hu : u = 0
    · subst hu
      simp [polarCombinationSummand, polarDualNorm]
    · simp [hu]
  have hsumD : Summable (L.polarPrimitiveDerivSummand c τ) :=
    Summable.of_norm_bounded ((L.summable_polarThetaMajorant hτ).mul_left _)
      (L.norm_polarPrimitiveDerivSummand_le c τ)
  rw [hsplit, (summable_of_ne_finset_zero (s := {0}) (fun u hu ↦ by
      simp only [Finset.mem_singleton] at hu; simp [hu])).tsum_add hsumD, tsum_ite_eq]

theorem hasDerivAt_polarThetaPrimitive (c : L.PolarDiscriminantGroup → ℂ) {τ : ℂ}
    (hτ : τ ∈ upperHalfSet) :
    HasDerivAt (L.polarThetaPrimitive c) (L.polarThetaCombination c τ) τ := by
  have hτ' : 0 < τ.im := hτ
  set t := {z : ℂ | τ.im / 2 < z.im}
  have hτt : τ ∈ t := by change τ.im / 2 < τ.im; linarith
  have hy : 0 < τ.im / 2 := by linarith
  have htsum : HasDerivAt (fun z ↦ ∑' u, L.polarPrimitiveSummand c z u)
      (∑' u, L.polarPrimitiveDerivSummand c τ u) τ := by
    refine hasDerivAt_tsum_of_isPreconnected
      (u := fun u ↦ L.polarCoeffBound c * L.polarThetaMajorant (τ.im / 2) u)
      ((L.summable_polarThetaMajorant hy).mul_left _) (isOpen_imGt _) (isPreconnected_imGt _)
      (fun u z _ ↦ L.hasDerivAt_polarPrimitiveSummand c u z) (fun u z hz ↦ ?_) hτt ?_ hτt
    · refine (L.norm_polarPrimitiveDerivSummand_le c z u).trans ?_
      exact mul_le_mul_of_nonneg_left (L.polarThetaMajorant_anti (le_of_lt hz) u)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    · exact Summable.of_norm_bounded
        (((L.summable_polarThetaMajorant hτ').mul_left _).mul_left _)
        (L.norm_polarPrimitiveSummand_le c τ)
  have h := ((hasDerivAt_id τ).const_mul (c 0)).add htsum
  rw [L.polarThetaCombination_eq_tsum c hτ', L.tsum_polarCombinationSummand_eq c hτ']
  simpa [polarThetaPrimitive] using h

/-- The theta combination tends to `c(0)` uniformly as `Im τ → ∞`. -/
theorem polarThetaCombination_tendsto (c : L.PolarDiscriminantGroup → ℂ) :
    ∀ ε > 0, ∃ Y : ℝ, ∀ τ ∈ upperHalfSet, Y < τ.im →
      ‖L.polarThetaCombination c τ - c 0‖ ≤ ε := by
  intro ε hε
  set δ := 1 / (2 * L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) with hδ
  have hdet := L.realPolarMatrix_det_pos
  have hδ0 : 0 < δ := by positivity
  set C := L.polarCoeffBound c * ∑' u, L.polarThetaMajorant 1 u with hC
  have hC0 : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
  -- choose `Y` with `C exp(-2π (Y - 1) δ) ≤ ε`
  have htend : Tendsto (fun Y : ℝ ↦ C * Real.exp (-(2 * Real.pi * δ * (Y - 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ ↦ 2 * Real.pi * δ * (Y - 1)) atTop atTop :=
      (tendsto_id.atTop_add tendsto_const_nhds).const_mul_atTop (by positivity)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  obtain ⟨Y₀, hY₀⟩ := (htend.eventually (ge_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max Y₀ 1, fun τ hτ hY ↦ ?_⟩
  have hτ' : 0 < τ.im := hτ
  have hY1 : 1 ≤ τ.im := le_trans (le_max_right _ _) hY.le
  rw [L.polarThetaCombination_eq_tsum c hτ', L.tsum_polarCombinationSummand_eq c hτ',
    add_sub_cancel_left]
  have hsum1 := L.summable_polarThetaMajorant (y := 1) one_pos
  have hbound : ∀ u, ‖L.polarPrimitiveDerivSummand c τ u‖ ≤
      L.polarCoeffBound c * (Real.exp (-(2 * Real.pi * δ * (τ.im - 1))) *
        L.polarThetaMajorant 1 u) := by
    intro u
    unfold polarPrimitiveDerivSummand
    split_ifs with hu
    · rw [norm_zero]
      exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    refine (L.norm_polarCombinationSummand_le c τ u).trans
      (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    unfold polarThetaMajorant
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hge := L.polarDualNorm_ge hu
    rw [← hδ] at hge
    have hpi := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.2 hY1)) (sub_nonneg.2 hge)]
  have hsumB : Summable fun u ↦ L.polarCoeffBound c *
      (Real.exp (-(2 * Real.pi * δ * (τ.im - 1))) * L.polarThetaMajorant 1 u) :=
    (hsum1.mul_left _).mul_left _
  calc ‖∑' u, L.polarPrimitiveDerivSummand c τ u‖
      ≤ ∑' u, L.polarCoeffBound c *
          (Real.exp (-(2 * Real.pi * δ * (τ.im - 1))) * L.polarThetaMajorant 1 u) :=
        tsum_of_norm_bounded hsumB.hasSum hbound
    _ = C * Real.exp (-(2 * Real.pi * δ * (τ.im - 1))) := by
        rw [tsum_mul_left, tsum_mul_left, hC]; ring
    _ ≤ ε := hY₀ τ.im (le_trans (le_max_left _ _) hY.le)

/-! ## `Pe₀ = 0` -/

/-- The origin component of an invariant vector vanishes (rank four; `Pe₀ = 0`). -/
theorem polarDeterminant_apply_zero_eq_zero_of_invariant (L : PositiveDefiniteIntegralLattice 4)
    (c : L.PolarDiscriminantGroup → ℂ) (hT : ∀ a, c a * L.polarDiscNormChar a = c a)
    (hS : ∀ a, c a = -(Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) *
      ∑ a₀, c a₀ * L.polarDiscPairingChar a₀ a) :
    c 0 = 0 :=
  constTerm_eq_zero (F := L.polarThetaPrimitive c) (f := L.polarThetaCombination c)
    (fun _ hτ ↦ L.hasDerivAt_polarThetaPrimitive c hτ) (L.continuousOn_polarThetaCombination c)
    (fun τ _ ↦ L.polarThetaCombination_add_one c hT τ)
    (fun _ hτ ↦ L.polarThetaCombination_neg_inv c hS hτ) (L.polarThetaCombination_tendsto c)

end PositiveDefiniteIntegralLattice
