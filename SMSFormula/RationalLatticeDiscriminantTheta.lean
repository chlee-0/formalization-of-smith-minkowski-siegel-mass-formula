import SMSFormula.RationalLatticeDualThetaTransformation

/-!
# The discriminant group and the vector theta laws

For an integral lattice with polar (Gram) matrix `S = 2F`, the dual lattice is `L^# = S⁻¹ ℤⁿ` and
the discriminant group `L^#/L` is, in dual coordinates, `A = ℤⁿ / S ℤⁿ`
(`PolarDiscriminantGroup`).  It is finite (`d ℤⁿ ⊆ S ℤⁿ` with `d = |det S|`, by the adjugate).

On `A` the dual norm `q(S⁻¹u) = ½ uᵀS⁻¹u` is well defined modulo `ℤ`, and so is the dual pairing
`u₀ᵀ S⁻¹ u` in each variable.  Hence:

* the class theta `θ_a(τ) = Σ_{u ∈ a} e(τ q(S⁻¹u))` (a sum over the fibre, no representative);
* the T-law `θ_a(τ + 1) = e(q(a)) θ_a(τ)`;
* the S-law `θ_{a₀}(-1/τ) = ((-iτ)^{1/2})ⁿ √det(S⁻¹) Σ_{a ∈ A} e(-B(a₀, a)) θ_a(τ)`, from the full
  dual-lattice inversion law (`polarCosetThetaRep_neg_inv`) grouped by classes.

Representatives are used only inside proofs; every statement is on `A`.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-! ## The discriminant group -/

/-- The integral polar sublattice `S ℤⁿ` of the dual coordinates. -/
def polarGramRange : AddSubgroup (Fin n → ℤ) :=
  (Matrix.mulVecLin L.polarGramMatrix).toAddMonoidHom.range

theorem mem_polarGramRange_iff (u : Fin n → ℤ) :
    u ∈ L.polarGramRange ↔ ∃ y, L.polarGramMatrix *ᵥ y = u := by
  simp [polarGramRange]

/-- The discriminant group `L^#/L ≅ ℤⁿ / S ℤⁿ` (dual coordinates). -/
abbrev PolarDiscriminantGroup : Type := (Fin n → ℤ) ⧸ L.polarGramRange

theorem polarGramMatrix_det_ne_zero : L.polarGramMatrix.det ≠ 0 :=
  (show 0 < L.polarGramMatrix.det from L.polarDeterminant_pos).ne'

theorem det_smul_mem_polarGramRange (w : Fin n → ℤ) :
    L.polarGramMatrix.det • w ∈ L.polarGramRange := by
  refine (L.mem_polarGramRange_iff _).2 ⟨L.polarGramMatrix.adjugate *ᵥ w, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

instance : Finite L.PolarDiscriminantGroup := by
  set d : ℕ := L.polarGramMatrix.det.natAbs with hd
  have hd0 : 0 < d := Int.natAbs_pos.2 L.polarGramMatrix_det_ne_zero
  refine Finite.of_surjective (fun v : Fin n → Fin d ↦
    ((fun i ↦ ((v i : ℕ) : ℤ)) : L.PolarDiscriminantGroup)) ?_
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H z =>
  refine ⟨fun i ↦ ⟨((z i) % (d : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_nonneg (z i) (by exact_mod_cast hd0.ne' : (d : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos (z i) (by exact_mod_cast hd0 : (0 : ℤ) < d)
    omega
  · apply QuotientAddGroup.eq.2
    have hmem : (d : ℤ) • (fun i ↦ z i / (d : ℤ)) ∈ L.polarGramRange := by
      rcases Int.natAbs_eq L.polarGramMatrix.det with h | h
      · rw [hd, ← h]
        exact L.det_smul_mem_polarGramRange _
      · have := L.polarGramRange.neg_mem (L.det_smul_mem_polarGramRange (fun i ↦ z i / (d : ℤ)))
        rw [← neg_smul, hd, show -L.polarGramMatrix.det = (L.polarGramMatrix.det.natAbs : ℤ) by omega]
          at this
        exact this
    convert hmem using 1
    funext i
    have h1 := Int.emod_nonneg (z i) (by exact_mod_cast hd0.ne' : (d : ℤ) ≠ 0)
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv (z i) (d : ℤ)
    linarith

noncomputable instance : Fintype L.PolarDiscriminantGroup := Fintype.ofFinite _

/-! ## Real-matrix identities -/

theorem realPolarMatrix_eq_map_polarGramMatrix :
    L.rationalQuadraticSpaceMatrix.realPolarMatrix = L.polarGramMatrix.map (Int.cast : ℤ → ℝ) := by
  ext i j
  rw [L.polarGramMatrix_eq_two_smul_pairingMatrix, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  simp [RationalQuadraticSpaceMatrix.realPolarMatrix, RationalQuadraticSpaceMatrix.polarMatrix,
    rationalQuadraticSpaceMatrix_pairingMatrix, rationalFormMatrix]

theorem integerVectorReal_polarGramMatrix_mulVec (y : Fin n → ℤ) :
    integerVectorReal (L.polarGramMatrix *ᵥ y) =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ integerVectorReal y := by
  rw [L.realPolarMatrix_eq_map_polarGramMatrix]
  funext i
  simp [integerVectorReal, Matrix.mulVec, dotProduct]

theorem realPolarMatrix_isUnit_det : IsUnit L.rationalQuadraticSpaceMatrix.realPolarMatrix.det :=
  isUnit_iff_ne_zero.2 L.rationalQuadraticSpaceMatrix.realPolarMatrix_det_ne_zero

theorem polarDualReal_add_gram (u y : Fin n → ℤ) :
    L.polarDualReal (u + L.polarGramMatrix *ᵥ y) = L.polarDualReal u + integerVectorReal y := by
  unfold polarDualReal
  have hadd : integerVectorReal (u + L.polarGramMatrix *ᵥ y) =
      integerVectorReal u + integerVectorReal (L.polarGramMatrix *ᵥ y) := by
    funext i; simp [integerVectorReal]
  rw [hadd, Matrix.mulVec_add, L.integerVectorReal_polarGramMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ L.realPolarMatrix_isUnit_det, Matrix.one_mulVec]

/-- `S (S⁻¹ u) = u`. -/
theorem realPolarMatrix_mulVec_polarDualReal (u : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ L.polarDualReal u = integerVectorReal u := by
  unfold polarDualReal
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ L.realPolarMatrix_isUnit_det,
    Matrix.one_mulVec]

/-- The dual norm in the form `½ wᵀ S w` with `w = S⁻¹ u`. -/
theorem polarDualNorm_eq (u : Fin n → ℤ) :
    L.polarDualNorm u = (L.polarDualReal u ⬝ᵥ
      L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ L.polarDualReal u) / 2 := by
  rw [L.realPolarMatrix_mulVec_polarDualReal, polarDualNorm, dotProduct_comm]
  rfl

theorem dotProduct_realPolarMatrix_comm (v w : Fin n → ℝ) :
    v ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ w =
      w ⬝ᵥ L.rationalQuadraticSpaceMatrix.realPolarMatrix *ᵥ v := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (L.rationalQuadraticSpaceMatrix.realPolarMatrix_isSymm).eq, dotProduct_comm]

/-- The dual norm changes by an integer along `S ℤⁿ`. -/
theorem polarDualNorm_add_gram (u y : Fin n → ℤ) :
    L.polarDualNorm (u + L.polarGramMatrix *ᵥ y) =
      L.polarDualNorm u + ((u ⬝ᵥ y + L.quadForm y : ℤ) : ℝ) := by
  rw [L.polarDualNorm_eq, L.polarDualNorm_eq, L.polarDualReal_add_gram]
  set S := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  set w := L.polarDualReal u
  have hw : S *ᵥ w = integerVectorReal u := L.realPolarMatrix_mulVec_polarDualReal u
  have hcross : integerVectorReal y ⬝ᵥ S *ᵥ w = ((u ⬝ᵥ y : ℤ) : ℝ) := by
    rw [hw]
    simp [integerVectorReal, dotProduct, mul_comm]
  have hyy : integerVectorReal y ⬝ᵥ S *ᵥ integerVectorReal y = 2 * ((L.quadForm y : ℤ) : ℝ) := by
    rw [← L.integerVectorReal_polarGramMatrix_mulVec, L.polarGramMatrix_eq_two_smul_pairingMatrix,
      L.quadForm_eq_dotProduct]
    simp [integerVectorReal, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hwy : w ⬝ᵥ S *ᵥ integerVectorReal y = ((u ⬝ᵥ y : ℤ) : ℝ) := by
    rw [L.dotProduct_realPolarMatrix_comm, hcross]
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hcross, hyy, hwy]
  push_cast
  ring

/-- The dual pairing changes by an integer along `S ℤⁿ` in the second variable. -/
theorem polarDualPairing_add_gram_right (u₀ u y : Fin n → ℤ) :
    L.polarDualPairing u₀ (u + L.polarGramMatrix *ᵥ y) = L.polarDualPairing u₀ u + ((u₀ ⬝ᵥ y : ℤ) : ℝ) := by
  unfold polarDualPairing
  have h : L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ integerVectorReal (u + L.polarGramMatrix *ᵥ y) =
      L.polarDualReal (u + L.polarGramMatrix *ᵥ y) := rfl
  rw [h, L.polarDualReal_add_gram, dotProduct_add]
  congr 1
  simp [integerVectorReal, dotProduct]

theorem polarDualPairing_comm (u₀ u : Fin n → ℤ) :
    L.polarDualPairing u₀ u = L.polarDualPairing u u₀ := by
  unfold polarDualPairing
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, (L.realPolarMatrix_inv_isSymm).eq,
    dotProduct_comm]

/-! ## Characters on the discriminant group -/

theorem exp_two_pi_I_intCast (k : ℤ) : exp (2 * Real.pi * I * (k : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨k, by ring⟩

theorem eq_add_gram_of_rel {u v : Fin n → ℤ} (h : -u + v ∈ L.polarGramRange) :
    ∃ y, v = u + L.polarGramMatrix *ᵥ y := by
  obtain ⟨y, hy⟩ := (L.mem_polarGramRange_iff _).1 h
  exact ⟨y, by rw [hy]; abel⟩

/-- `e(q(a))`, the T-eigenvalue of the class `a`. -/
def polarDiscNormChar (a : L.PolarDiscriminantGroup) : ℂ :=
  Quotient.liftOn' a (fun u ↦ exp (2 * Real.pi * I * (L.polarDualNorm u : ℂ))) (by
    intro u v huv
    obtain ⟨y, rfl⟩ := L.eq_add_gram_of_rel (QuotientAddGroup.leftRel_apply.mp huv)
    simp only
    rw [L.polarDualNorm_add_gram]
    push_cast
    rw [mul_add, Complex.exp_add, ← Int.cast_add, exp_two_pi_I_intCast, mul_one])

@[simp]
theorem polarDiscNormChar_coe (u : Fin n → ℤ) :
    L.polarDiscNormChar (u : L.PolarDiscriminantGroup) =
      exp (2 * Real.pi * I * (L.polarDualNorm u : ℂ)) :=
  rfl

theorem exp_neg_polarDualPairing_add_gram_right (u₀ u y : Fin n → ℤ) :
    exp (-(2 * Real.pi * I * (L.polarDualPairing u₀ (u + L.polarGramMatrix *ᵥ y) : ℂ))) =
      exp (-(2 * Real.pi * I * (L.polarDualPairing u₀ u : ℂ))) := by
  rw [L.polarDualPairing_add_gram_right]
  push_cast
  rw [mul_add, neg_add, Complex.exp_add, Complex.exp_neg (2 * Real.pi * I * ((u₀ ⬝ᵥ y : ℤ) : ℂ)),
    exp_two_pi_I_intCast, inv_one, mul_one]

/-- `e(-B(a₀, a))`, the pairing character of the discriminant group. -/
def polarDiscPairingChar (a₀ a : L.PolarDiscriminantGroup) : ℂ :=
  Quotient.liftOn₂' a₀ a (fun u₀ u ↦ exp (-(2 * Real.pi * I * (L.polarDualPairing u₀ u : ℂ)))) (by
    intro u₀ u v₀ v h₀ h
    obtain ⟨y₀, rfl⟩ := L.eq_add_gram_of_rel (QuotientAddGroup.leftRel_apply.mp h₀)
    obtain ⟨y, rfl⟩ := L.eq_add_gram_of_rel (QuotientAddGroup.leftRel_apply.mp h)
    simp only
    rw [L.exp_neg_polarDualPairing_add_gram_right, L.polarDualPairing_comm,
      L.polarDualPairing_comm (u₀ + _), L.exp_neg_polarDualPairing_add_gram_right])

@[simp]
theorem polarDiscPairingChar_coe (u₀ u : Fin n → ℤ) :
    L.polarDiscPairingChar (u₀ : L.PolarDiscriminantGroup) (u : L.PolarDiscriminantGroup) =
      exp (-(2 * Real.pi * I * (L.polarDualPairing u₀ u : ℂ))) :=
  rfl

/-! ## The class theta -/

/-- The class theta `θ_a(τ) = Σ_{u ∈ a} e(τ q(S⁻¹u))`, a sum over the fibre of `a`. -/
def polarClassTheta (τ : ℂ) (a : L.PolarDiscriminantGroup) : ℂ :=
  ∑' u : {u : Fin n → ℤ // (u : L.PolarDiscriminantGroup) = a},
    exp (2 * Real.pi * I * τ * (L.polarDualNorm u.1 : ℂ))

/-- The T-law: `θ_a(τ + 1) = e(q(a)) θ_a(τ)`. -/
theorem polarClassTheta_add_one (τ : ℂ) (a : L.PolarDiscriminantGroup) :
    L.polarClassTheta (τ + 1) a = L.polarDiscNormChar a * L.polarClassTheta τ a := by
  unfold polarClassTheta
  rw [← tsum_mul_left]
  refine tsum_congr fun ⟨u, hu⟩ ↦ ?_
  subst hu
  rw [polarDiscNormChar_coe, ← Complex.exp_add]
  congr 1
  ring

theorem polarGramMatrix_mulVec_injective : Function.Injective (L.polarGramMatrix *ᵥ ·) := by
  intro y y' h
  have hr : integerVectorReal y = integerVectorReal y' := by
    have h1 := congrArg integerVectorReal h
    simp only [L.integerVectorReal_polarGramMatrix_mulVec] at h1
    have h2 := congrArg (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ *ᵥ ·) h1
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ L.realPolarMatrix_isUnit_det,
      Matrix.one_mulVec] using h2
  funext i
  have := congrFun hr i
  simp only [integerVectorReal] at this
  exact_mod_cast this

/-- The fibre of the class of `u₀` is `u₀ + S ℤⁿ`. -/
def polarClassFiberEquiv (u₀ : Fin n → ℤ) :
    (Fin n → ℤ) ≃ {u : Fin n → ℤ // (u : L.PolarDiscriminantGroup) = (u₀ : L.PolarDiscriminantGroup)} :=
  Equiv.ofBijective (fun y ↦ ⟨u₀ + L.polarGramMatrix *ᵥ y, by
      apply QuotientAddGroup.eq.2
      have : -(u₀ + L.polarGramMatrix *ᵥ y) + u₀ = L.polarGramMatrix *ᵥ (-y) := by
        rw [Matrix.mulVec_neg]; abel
      rw [this]
      exact (L.mem_polarGramRange_iff _).2 ⟨-y, rfl⟩⟩)
    ⟨fun y y' h ↦ L.polarGramMatrix_mulVec_injective (add_left_cancel (congrArg Subtype.val h)),
      fun ⟨u, hu⟩ ↦ by
        obtain ⟨y, hy⟩ := L.eq_add_gram_of_rel (QuotientAddGroup.eq.1 hu.symm)
        exact ⟨y, Subtype.ext hy.symm⟩⟩

/-- The class theta of the class of `u₀` is the coset theta with representative `u₀`. -/
theorem polarClassTheta_coe (τ : ℂ) (u₀ : Fin n → ℤ) :
    L.polarClassTheta τ (u₀ : L.PolarDiscriminantGroup) = L.polarCosetThetaRep τ u₀ := by
  unfold polarClassTheta polarCosetThetaRep
  rw [← (L.polarClassFiberEquiv u₀).tsum_eq]
  refine tsum_congr fun y ↦ ?_
  change exp (2 * Real.pi * I * τ * (L.polarDualNorm (u₀ + L.polarGramMatrix *ᵥ y) : ℂ)) = _
  rw [L.polarDualNorm_eq, L.polarDualReal_add_gram, complexCenteredMatrixGaussianSummand]
  have hx : (fun i ↦ (y i : ℝ) - (-L.polarDualReal u₀) i) =
      L.polarDualReal u₀ + integerVectorReal y := by
    funext i; simp [integerVectorReal, add_comm]
  simp only [hx]
  push_cast
  congr 1
  ring

/-! ## Grouping the dual theta by classes, and the S-law -/

theorem summable_polarDualCharThetaSummand {τ : ℂ} (hτ : 0 < τ.im) (u₀ : Fin n → ℤ) :
    Summable (L.polarDualCharThetaSummand τ u₀) := by
  have hS : (L.rationalQuadraticSpaceMatrix.realPolarMatrix).PosDef :=
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef
  have hb : 0 < (-I * τ).re := by simpa using hτ
  have h := summable_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
    (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹) hS.inv hb (-L.polarDualReal u₀)
  have heq : shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
      (-I * τ) (pureImaginaryLinear (-L.polarDualReal u₀)) = L.polarDualCharThetaSummand τ u₀ :=
    funext (L.shiftedMatrixGaussianSummand_inv_eq_polarDualCharThetaSummand τ u₀)
  rwa [heq] at h

/-- The dual theta grouped by classes: `Θ_{u₀}(τ) = Σ_{a ∈ A} e(-B(u₀, a)) θ_a(τ)`. -/
theorem polarDualCharTheta_eq_sum_classes {τ : ℂ} (hτ : 0 < τ.im) (u₀ : Fin n → ℤ) :
    L.polarDualCharTheta τ u₀ =
      ∑ a : L.PolarDiscriminantGroup,
        L.polarDiscPairingChar (u₀ : L.PolarDiscriminantGroup) a * L.polarClassTheta τ a := by
  have hsum := L.summable_polarDualCharThetaSummand hτ u₀
  let e := Equiv.sigmaFiberEquiv (fun u : Fin n → ℤ ↦ (u : L.PolarDiscriminantGroup))
  unfold polarDualCharTheta
  rw [← e.tsum_eq]
  refine ((hsum.comp_injective e.injective).tsum_sigma).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  unfold polarClassTheta
  rw [← tsum_mul_left]
  refine tsum_congr fun ⟨u, hu⟩ ↦ ?_
  subst hu
  change L.polarDualCharThetaSummand τ u₀ u = _
  rw [polarDualCharThetaSummand, polarDiscPairingChar_coe]
  ring

/-- The S-law on the discriminant group:
`θ_{a₀}(-1/τ) = ((-iτ)^{1/2})ⁿ √det(S⁻¹) Σ_{a ∈ A} e(-B(a₀, a)) θ_a(τ)`. -/
theorem polarClassTheta_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (a₀ : L.PolarDiscriminantGroup) :
    L.polarClassTheta (-τ⁻¹) a₀ =
      ((-I * τ) ^ (1 / 2 : ℂ)) ^ n *
          (Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) *
        ∑ a : L.PolarDiscriminantGroup, L.polarDiscPairingChar a₀ a * L.polarClassTheta τ a := by
  induction a₀ using QuotientAddGroup.induction_on with
  | H u₀ =>
  rw [L.polarClassTheta_coe, L.polarCosetThetaRep_neg_inv hτ, L.polarDualCharTheta_eq_sum_classes hτ]

end PositiveDefiniteIntegralLattice
