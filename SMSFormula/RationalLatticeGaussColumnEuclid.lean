import SMSFormula.RationalLatticeGaussColumns

/-!
# Euclidean transport: every Gauss column is a unit vector orthogonal to the invariants


On `ℂ[A]`, `A = L^#/L` the discriminant group, use the Hermitian product `⟨v, w⟩ = Σ_a conj(v_a) w_a`
(`gaussHerm`).  Let `Inv = ker(U - 1) ∩ ker(T₀ - 1)` (`gaussInv`) and `Inv^⊥` its Hermitian orthogonal
complement (`gaussInvPerp`).

* The pairing character `e(-B(a₀, a))` is symmetric, multiplicative, conjugated by `a ↦ -a`, and
  nondegenerate (`eq_zero_of_forall_polarDiscPairingChar_eq_one`: if `u₀ᵀ S⁻¹ eᵢ ∈ ℤ` for all `i`, then
  `u₀ ∈ S ℤⁿ`).  Hence `Σ_a e(-B(b, a)) = |A| [b = 0]` (`sum_polarDiscPairingChar`).
* `⟨Uv, Uw⟩ = κ²|A| ⟨v, w⟩` (`gaussHerm_gaussU_gaussU_eq`).  The identity `U² e₀ = e₀` gives
  `(κ²|A|)² = 1`, so `κ²|A| = 1` (`polarKappa_sq_mul_card`): `U` is unitary, and as a by-product
  `|A| = det S` (`card_polarDeterminantGroup`).  The discriminant group is never counted.
* `T₀` is unitary (unit-modulus diagonal, `gaussHerm_gaussT`).
* Every invariant vector has zero origin component (`Pe₀ = 0`), so `e₀ ∈ Inv^⊥`.
* The Euclidean induction (`isGaussUnitPerp_gaussColumn`): for every coprime pair `(c, d)`,
  `⟨F(c,d), F(c,d)⟩ = 1` and `F(c,d) ∈ Inv^⊥`.  Strong induction on `|c|`: `F(c, d + kc)` is related to
  `F(c, d)` by powers of `T₀` (`gaussColumn_sub_self`), and `F(c, r) = U F(r, -c)`
  (`gaussColumn_neg_inv_of_isCoprime`); both operators preserve the property since they are unitary
  and fix `Inv` pointwise.  No matrix with bottom row `(c, d)` is chosen and no word independence is used.
* `Π₀`, the orthogonal projection onto `ker(T₀ - 1)` (the coordinates with `e(q(a)) = 1`), maps
  `Inv^⊥` into `K = Inv^⊥ ∩ ker(T₀ - 1)` (`gaussBoundaryK`) and is a sup-norm contraction.  `U` has no
  nonzero fixed vector in `K` (`gaussUCLM_eq_self_imp`), which is the hypothesis of the bounded
  cluster lemma.
Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology ComplexConjugate

namespace PositiveDefiniteIntegralLattice

/-! ## The pairing character (any rank) -/

section Pairing

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

theorem polarDualPairing_add_right (u₀ u u' : Fin n → ℤ) :
    L.polarDualPairing u₀ (u + u') = L.polarDualPairing u₀ u + L.polarDualPairing u₀ u' := by
  unfold polarDualPairing
  have h : integerVectorReal (u + u') = integerVectorReal u + integerVectorReal u' := by
    funext i; simp [integerVectorReal]
  rw [h, Matrix.mulVec_add, dotProduct_add]

theorem polarDualPairing_neg_right (u₀ u : Fin n → ℤ) :
    L.polarDualPairing u₀ (-u) = -L.polarDualPairing u₀ u := by
  unfold polarDualPairing
  have h : integerVectorReal (-u) = -integerVectorReal u := by
    funext i; simp [integerVectorReal]
  rw [h, Matrix.mulVec_neg, dotProduct_neg]

theorem polarDiscPairingChar_comm (a₀ a : L.PolarDiscriminantGroup) :
    L.polarDiscPairingChar a₀ a = L.polarDiscPairingChar a a₀ := by
  induction a₀ using QuotientAddGroup.induction_on with
  | H u₀ =>
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [polarDiscPairingChar_coe, polarDiscPairingChar_coe, L.polarDualPairing_comm]

theorem polarDiscPairingChar_zero_left (a : L.PolarDiscriminantGroup) :
    L.polarDiscPairingChar 0 a = 1 := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [← QuotientAddGroup.mk_zero, polarDiscPairingChar_coe]
  simp [polarDualPairing]

theorem polarDiscPairingChar_add_right (a₀ a a' : L.PolarDiscriminantGroup) :
    L.polarDiscPairingChar a₀ (a + a') =
      L.polarDiscPairingChar a₀ a * L.polarDiscPairingChar a₀ a' := by
  induction a₀ using QuotientAddGroup.induction_on with
  | H u₀ =>
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  induction a' using QuotientAddGroup.induction_on with
  | H u' =>
  rw [← QuotientAddGroup.mk_add, polarDiscPairingChar_coe, polarDiscPairingChar_coe,
    polarDiscPairingChar_coe, L.polarDualPairing_add_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_polarDiscPairingChar (a₀ a : L.PolarDiscriminantGroup) :
    conj (L.polarDiscPairingChar a₀ a) = L.polarDiscPairingChar a₀ (-a) := by
  induction a₀ using QuotientAddGroup.induction_on with
  | H u₀ =>
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [← QuotientAddGroup.mk_neg, polarDiscPairingChar_coe, polarDiscPairingChar_coe,
    L.polarDualPairing_neg_right, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_ofNat, conj_ofReal, conj_I]
  push_cast
  ring

/-- The pairing is nondegenerate: `e(-B(a₀, a)) = 1` for every `a` forces `a₀ = 0`. -/
theorem eq_zero_of_forall_polarDiscPairingChar_eq_one {a₀ : L.PolarDiscriminantGroup}
    (h : ∀ a, L.polarDiscPairingChar a₀ a = 1) : a₀ = 0 := by
  induction a₀ using QuotientAddGroup.induction_on with
  | H u₀ =>
  have hint : ∀ i, ∃ k : ℤ, L.polarDualReal u₀ i = k := by
    intro i
    have hi := h ((Pi.single i 1 : Fin n → ℤ) : L.PolarDiscriminantGroup)
    rw [polarDiscPairingChar_coe, Complex.exp_eq_one_iff] at hi
    obtain ⟨k, hk⟩ := hi
    refine ⟨-k, ?_⟩
    have hp : L.polarDualPairing u₀ (Pi.single i 1) = L.polarDualReal u₀ i := by
      rw [L.polarDualPairing_comm]
      unfold polarDualPairing polarDualReal
      have hs : integerVectorReal (Pi.single i (1 : ℤ)) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [integerVectorReal]
        · simp [integerVectorReal, hj]
      rw [hs, single_dotProduct, one_mul]
    rw [hp] at hk
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hc : ((L.polarDualReal u₀ i : ℝ) : ℂ) = ((-k : ℤ) : ℂ) := by
      apply mul_left_cancel₀ hpi
      push_cast
      linear_combination -hk
    exact_mod_cast hc
  choose y hy using hint
  have hu : u₀ = L.polarGramMatrix *ᵥ y := by
    have hr : integerVectorReal u₀ = integerVectorReal (L.polarGramMatrix *ᵥ y) := by
      rw [L.integerVectorReal_polarGramMatrix_mulVec, ← L.realPolarMatrix_mulVec_polarDualReal]
      congr 1
      funext i
      simp [integerVectorReal, hy]
    funext i
    have := congrFun hr i
    simp only [integerVectorReal] at this
    exact_mod_cast this
  rw [QuotientAddGroup.eq_zero_iff]
  exact (L.mem_polarGramRange_iff _).2 ⟨y, hu.symm⟩

/-- Character orthogonality: `Σ_a e(-B(b, a)) = |A| [b = 0]`. -/
theorem sum_polarDiscPairingChar (b : L.PolarDiscriminantGroup) :
    ∑ a, L.polarDiscPairingChar b a =
      if b = 0 then (Fintype.card L.PolarDiscriminantGroup : ℂ) else 0 := by
  split_ifs with hb
  · subst hb
    simp [polarDiscPairingChar_zero_left]
  · obtain ⟨a₁, ha₁⟩ : ∃ a₁, L.polarDiscPairingChar b a₁ ≠ 1 := by
      by_contra hne
      push_neg at hne
      exact hb (L.eq_zero_of_forall_polarDiscPairingChar_eq_one hne)
    have hshift : ∑ a, L.polarDiscPairingChar b a =
        L.polarDiscPairingChar b a₁ * ∑ a, L.polarDiscPairingChar b a := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.addLeft a₁)
        (fun a ↦ L.polarDiscPairingChar b a₁ * L.polarDiscPairingChar b a)
        (fun a ↦ L.polarDiscPairingChar b a)
        (fun a ↦ by
          show _ = L.polarDiscPairingChar b (a₁ + a)
          rw [polarDiscPairingChar_add_right])).symm
    have h1 : (1 - L.polarDiscPairingChar b a₁) * ∑ a, L.polarDiscPairingChar b a = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm ha₁))

theorem sum_conj_mul_polarDiscPairingChar (a b : L.PolarDiscriminantGroup) :
    ∑ a₀, conj (L.polarDiscPairingChar a₀ a) * L.polarDiscPairingChar a₀ b =
      if a = b then (Fintype.card L.PolarDiscriminantGroup : ℂ) else 0 := by
  have h : ∀ a₀, conj (L.polarDiscPairingChar a₀ a) * L.polarDiscPairingChar a₀ b =
      L.polarDiscPairingChar (-a + b) a₀ := by
    intro a₀
    rw [conj_polarDiscPairingChar, ← polarDiscPairingChar_add_right, polarDiscPairingChar_comm]
  simp_rw [h]
  rw [sum_polarDiscPairingChar]
  by_cases hab : a = b
  · rw [if_pos (by rw [hab, neg_add_cancel]), if_pos hab]
  · rw [if_neg (fun h' ↦ hab (neg_add_eq_zero.1 h')), if_neg hab]

theorem norm_polarDiscNormChar (a : L.PolarDiscriminantGroup) : ‖L.polarDiscNormChar a‖ = 1 := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [polarDiscNormChar_coe, show 2 * (Real.pi : ℂ) * I * (L.polarDualNorm u : ℂ) =
      ((2 * Real.pi * L.polarDualNorm u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem conj_mul_polarDiscNormChar (a : L.PolarDiscriminantGroup) :
    conj (L.polarDiscNormChar a) * L.polarDiscNormChar a = 1 := by
  rw [Complex.conj_mul', norm_polarDiscNormChar]
  simp

end Pairing

/-! ## The Hermitian product -/

section Hermitian

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- The Hermitian product `⟨v, w⟩ = Σ_a conj(v_a) w_a` on `ℂ[A]`. -/
def gaussHerm (v w : L.PolarDiscriminantGroup → ℂ) : ℂ := ∑ a, conj (v a) * w a

theorem gaussHerm_add_right (v w w' : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm v (w + w') = L.gaussHerm v w + L.gaussHerm v w' := by
  simp only [gaussHerm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem gaussHerm_smul_right (z : ℂ) (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm v (z • w) = z * L.gaussHerm v w := by
  simp only [gaussHerm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

theorem gaussHerm_zero_right (v : L.PolarDiscriminantGroup → ℂ) : L.gaussHerm v 0 = 0 := by
  simp [gaussHerm]

theorem gaussHerm_self (v : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm v v = ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) := by
  unfold gaussHerm
  push_cast
  exact Finset.sum_congr rfl fun a _ ↦ Complex.conj_mul' (v a)

theorem eq_zero_of_gaussHerm_self_eq_zero {v : L.PolarDiscriminantGroup → ℂ}
    (h : L.gaussHerm v v = 0) : v = 0 := by
  rw [gaussHerm_self] at h
  have h' : ∑ a, ‖v a‖ ^ 2 = 0 := by exact_mod_cast h
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ by positivity)).1 h' a (Finset.mem_univ a)
  simpa using this

/-- A vector of Hermitian norm one has every coordinate of modulus at most one. -/
theorem norm_apply_le_one_of_gaussHerm_self {v : L.PolarDiscriminantGroup → ℂ}
    (h : L.gaussHerm v v = 1) (a : L.PolarDiscriminantGroup) : ‖v a‖ ≤ 1 := by
  rw [gaussHerm_self] at h
  have h' : ∑ b, ‖v b‖ ^ 2 = 1 := by exact_mod_cast h
  have hle : ‖v a‖ ^ 2 ≤ 1 := by
    rw [← h']
    exact Finset.single_le_sum (f := fun b ↦ ‖v b‖ ^ 2) (fun b _ ↦ by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (v a)]

theorem norm_le_one_of_gaussHerm_self {v : L.PolarDiscriminantGroup → ℂ}
    (h : L.gaussHerm v v = 1) : ‖v‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 (L.norm_apply_le_one_of_gaussHerm_self h)

end Hermitian

/-! ## Rank four: unitarity of `U` and `T₀` -/

variable (L : PositiveDefiniteIntegralLattice 4)

theorem gaussU_add (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussU (v + w) = L.gaussU v + L.gaussU w := by
  funext a
  simp only [gaussU, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem gaussU_smul (z : ℂ) (v : L.PolarDiscriminantGroup → ℂ) :
    L.gaussU (z • v) = z • L.gaussU v := by
  funext a
  simp only [gaussU, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  ring

theorem gaussU_zero : L.gaussU 0 = 0 := by
  funext a
  simp [gaussU]

theorem gaussT_add (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussT (v + w) = L.gaussT v + L.gaussT w := by
  funext a
  simp only [gaussT, Pi.add_apply, mul_add]

theorem gaussT_smul (z : ℂ) (v : L.PolarDiscriminantGroup → ℂ) :
    L.gaussT (z • v) = z • L.gaussT v := by
  funext a
  simp only [gaussT, Pi.smul_apply, smul_eq_mul]
  ring

theorem gaussT_zero : L.gaussT 0 = 0 := by
  funext a
  simp [gaussT]

/-- `⟨Uv, Uw⟩ = κ²|A| ⟨v, w⟩`. -/
theorem gaussHerm_gaussU_gaussU_eq (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm (L.gaussU v) (L.gaussU w) =
      ((L.polarKappa ^ 2 * Fintype.card L.PolarDiscriminantGroup : ℝ) : ℂ) * L.gaussHerm v w := by
  unfold gaussHerm gaussU
  have hk : conj (L.polarKappa : ℂ) = L.polarKappa := conj_ofReal _
  have hterm : ∀ a₀, conj (-(L.polarKappa : ℂ) * ∑ a, L.polarDiscPairingChar a₀ a * v a) *
        (-(L.polarKappa : ℂ) * ∑ b, L.polarDiscPairingChar a₀ b * w b) =
      ∑ a, ∑ b, (L.polarKappa : ℂ) ^ 2 * (conj (v a) * w b) *
          (conj (L.polarDiscPairingChar a₀ a) * L.polarDiscPairingChar a₀ b) := by
    intro a₀
    rw [map_mul, map_neg, hk, map_sum,
      show ∀ X Y : ℂ, (-(L.polarKappa : ℂ) * X) * (-(L.polarKappa : ℂ) * Y) =
        (L.polarKappa : ℂ) ^ 2 * (X * Y) from fun X Y ↦ by ring,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [map_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_conj_mul_polarDiscPairingChar]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by rw [if_neg (Ne.symm hb), mul_zero]) (by simp),
    if_pos rfl]
  push_cast
  ring

/-- The normalization `κ²|A| = 1`, from the `U² e₀ = e₀`. -/
theorem polarKappa_sq_mul_card :
    L.polarKappa ^ 2 * (Fintype.card L.PolarDiscriminantGroup : ℝ) = 1 := by
  set lam := L.polarKappa ^ 2 * (Fintype.card L.PolarDiscriminantGroup : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have he : L.gaussHerm L.gaussE0 L.gaussE0 = 1 := by
    unfold gaussHerm gaussE0
    rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp
  have h := L.gaussHerm_gaussU_gaussU_eq (L.gaussU L.gaussE0) (L.gaussU L.gaussE0)
  rw [L.gaussU_gaussU_gaussE0, L.gaussHerm_gaussU_gaussU_eq, he, mul_one] at h
  have h' : lam * lam = 1 := by exact_mod_cast h.symm
  nlinarith

/-- `U` is unitary. -/
theorem gaussHerm_gaussU (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm (L.gaussU v) (L.gaussU w) = L.gaussHerm v w := by
  rw [gaussHerm_gaussU_gaussU_eq, polarKappa_sq_mul_card]
  simp

/-- By-product: `|L^#/L| = det S` (in rank four), without counting. -/
theorem card_polarDeterminantGroup :
    (Fintype.card L.PolarDiscriminantGroup : ℤ) = L.polarGramMatrix.det := by
  have h := L.polarKappa_sq_mul_card
  have hdet := L.realPolarMatrix_det_pos
  rw [polarKappa, Real.sq_sqrt L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv.det_pos.le,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hc : (Fintype.card L.PolarDiscriminantGroup : ℝ) =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix.det := by
    field_simp at h
    linarith
  have hS : L.rationalQuadraticSpaceMatrix.realPolarMatrix.det = ((L.polarGramMatrix.det : ℤ) : ℝ) := by
    rw [L.realPolarMatrix_eq_map_polarGramMatrix]
    exact ((Int.castRingHom ℝ).map_det L.polarGramMatrix).symm
  rw [hS] at hc
  exact_mod_cast hc

/-- `T₀` is unitary. -/
theorem gaussHerm_gaussT (v w : L.PolarDiscriminantGroup → ℂ) :
    L.gaussHerm (L.gaussT v) (L.gaussT w) = L.gaussHerm v w := by
  unfold gaussHerm gaussT
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_mul]
  linear_combination conj (v a) * w a * L.conj_mul_polarDiscNormChar a

/-! ## The invariants and their Hermitian complement -/

/-- The invariant subspace `Inv = ker(U - 1) ∩ ker(T₀ - 1)`. -/
def gaussInv : Submodule ℂ (L.PolarDiscriminantGroup → ℂ) where
  carrier := {w | L.gaussU w = w ∧ L.gaussT w = w}
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by rw [gaussU_add, hv1, hw1], by rw [gaussT_add, hv2, hw2]⟩
  zero_mem' := ⟨L.gaussU_zero, L.gaussT_zero⟩
  smul_mem' := by
    rintro z w ⟨h1, h2⟩
    exact ⟨by rw [gaussU_smul, h1], by rw [gaussT_smul, h2]⟩

theorem mem_gaussInv {w : L.PolarDiscriminantGroup → ℂ} :
    w ∈ L.gaussInv ↔ L.gaussU w = w ∧ L.gaussT w = w :=
  Iff.rfl

/-- The Hermitian orthogonal complement `Inv^⊥`. -/
def gaussInvPerp : Submodule ℂ (L.PolarDiscriminantGroup → ℂ) where
  carrier := {v | ∀ w ∈ L.gaussInv, L.gaussHerm w v = 0}
  add_mem' := by
    intro v v' hv hv' w hw
    rw [gaussHerm_add_right, hv w hw, hv' w hw, add_zero]
  zero_mem' := fun w _ ↦ L.gaussHerm_zero_right w
  smul_mem' := by
    intro z v hv w hw
    rw [gaussHerm_smul_right, hv w hw, mul_zero]

theorem mem_gaussInvPerp {v : L.PolarDiscriminantGroup → ℂ} :
    v ∈ L.gaussInvPerp ↔ ∀ w ∈ L.gaussInv, L.gaussHerm w v = 0 :=
  Iff.rfl

/-- The `T₀`-fixed subspace `ker(T₀ - 1)`. -/
def gaussTFixed : Submodule ℂ (L.PolarDiscriminantGroup → ℂ) where
  carrier := {v | L.gaussT v = v}
  add_mem' := by
    intro v w hv hw
    change L.gaussT (v + w) = v + w
    rw [gaussT_add, hv, hw]
  zero_mem' := L.gaussT_zero
  smul_mem' := by
    intro z v hv
    change L.gaussT (z • v) = z • v
    rw [gaussT_smul, hv]

theorem mem_gaussTFixed {v : L.PolarDiscriminantGroup → ℂ} :
    v ∈ L.gaussTFixed ↔ L.gaussT v = v :=
  Iff.rfl

/-- The boundary subspace `K = Inv^⊥ ∩ ker(T₀ - 1)` of the bounded cluster lemma. -/
def gaussBoundaryK : Submodule ℂ (L.PolarDiscriminantGroup → ℂ) := L.gaussInvPerp ⊓ L.gaussTFixed

/-- `U` has no nonzero fixed vector in `K`. -/
theorem eq_zero_of_mem_gaussBoundaryK {w : L.PolarDiscriminantGroup → ℂ}
    (hw : w ∈ L.gaussBoundaryK) (hU : L.gaussU w = w) : w = 0 :=
  L.eq_zero_of_gaussHerm_self_eq_zero (hw.1 w ⟨hU, hw.2⟩)

/-- Every invariant vector has zero origin component (the `Pe₀ = 0`). -/
theorem gaussInv_apply_zero {w : L.PolarDiscriminantGroup → ℂ} (hw : w ∈ L.gaussInv) : w 0 = 0 := by
  refine L.polarDeterminant_apply_zero_eq_zero_of_invariant w (fun a ↦ ?_) (fun a ↦ ?_)
  · have h := congrFun hw.2 a
    rw [gaussT] at h
    rw [mul_comm]
    exact h
  · have h := congrFun hw.1 a
    rw [gaussU] at h
    calc w a = -(L.polarKappa : ℂ) * ∑ b, L.polarDiscPairingChar a b * w b := h.symm
      _ = _ := by
        simp only [polarKappa]
        congr 1
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [polarDiscPairingChar_comm, mul_comm]

theorem gaussHerm_gaussE0_self : L.gaussHerm L.gaussE0 L.gaussE0 = 1 := by
  unfold gaussHerm gaussE0
  rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp

/-- `e₀ ∈ Inv^⊥`. -/
theorem gaussE0_mem_gaussInvPerp : L.gaussE0 ∈ L.gaussInvPerp := by
  intro w hw
  unfold gaussHerm gaussE0
  rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp [L.gaussInv_apply_zero hw]

/-! ## The Euclidean induction -/

/-- The transported property: Hermitian norm one and orthogonality to the invariants. -/
def IsGaussUnitPerp (v : L.PolarDiscriminantGroup → ℂ) : Prop :=
  L.gaussHerm v v = 1 ∧ v ∈ L.gaussInvPerp

theorem isGaussUnitPerp_gaussE0 : L.IsGaussUnitPerp L.gaussE0 :=
  ⟨L.gaussHerm_gaussE0_self, L.gaussE0_mem_gaussInvPerp⟩

theorem isGaussUnitPerp_gaussU_iff (v : L.PolarDiscriminantGroup → ℂ) :
    L.IsGaussUnitPerp (L.gaussU v) ↔ L.IsGaussUnitPerp v := by
  have hw : ∀ w ∈ L.gaussInv, L.gaussHerm w (L.gaussU v) = L.gaussHerm w v := by
    intro w hw
    conv_lhs => rw [← hw.1]
    exact L.gaussHerm_gaussU w v
  unfold IsGaussUnitPerp
  rw [gaussHerm_gaussU, mem_gaussInvPerp, mem_gaussInvPerp]
  refine and_congr_right fun _ ↦ ⟨fun h w hw' ↦ ?_, fun h w hw' ↦ ?_⟩
  · rw [← hw w hw']; exact h w hw'
  · rw [hw w hw']; exact h w hw'

theorem isGaussUnitPerp_gaussT_iff (v : L.PolarDiscriminantGroup → ℂ) :
    L.IsGaussUnitPerp (L.gaussT v) ↔ L.IsGaussUnitPerp v := by
  have hw : ∀ w ∈ L.gaussInv, L.gaussHerm w (L.gaussT v) = L.gaussHerm w v := by
    intro w hw
    conv_lhs => rw [← hw.2]
    exact L.gaussHerm_gaussT w v
  unfold IsGaussUnitPerp
  rw [gaussHerm_gaussT, mem_gaussInvPerp, mem_gaussInvPerp]
  refine and_congr_right fun _ ↦ ⟨fun h w hw' ↦ ?_, fun h w hw' ↦ ?_⟩
  · rw [← hw w hw']; exact h w hw'
  · rw [hw w hw']; exact h w hw'

/-- The property is constant along `d ↦ d + kc` (powers of `T₀`). -/
theorem isGaussUnitPerp_gaussColumn_add_mul (c x k : ℤ) :
    L.IsGaussUnitPerp (L.gaussColumn c (x + c * k)) ↔ L.IsGaussUnitPerp (L.gaussColumn c x) := by
  refine Int.induction_on k (by simp) (fun k ih ↦ ?_) (fun k ih ↦ ?_)
  · rw [← ih]
    have h := L.gaussColumn_sub_self c (x + c * ((k : ℤ) + 1))
    rw [show x + c * ((k : ℤ) + 1) - c = x + c * (k : ℤ) by ring] at h
    rw [h, isGaussUnitPerp_gaussT_iff]
  · rw [← ih]
    have h := L.gaussColumn_sub_self c (x + c * -(k : ℤ))
    rw [show x + c * -(k : ℤ) - c = x + c * (-(k : ℤ) - 1) by ring] at h
    rw [h, isGaussUnitPerp_gaussT_iff]

theorem isGaussUnitPerp_gaussColumn_aux (k : ℕ) :
    ∀ c d : ℤ, c.natAbs = k → IsCoprime c d → L.IsGaussUnitPerp (L.gaussColumn c d) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c d hk h
  by_cases hc : c = 0
  · subst hc
    rw [gaussColumn_zero]
    exact L.isGaussUnitPerp_gaussE0
  have hd : d = d % c + c * (d / c) := (Int.emod_add_mul_ediv d c).symm
  have hcr : IsCoprime (d % c) (-c) := by
    have h1 : IsCoprime c (d + c * (-(d / c))) := h.add_mul_left_right _
    rw [show d + c * (-(d / c)) = d % c by linear_combination -(Int.emod_add_mul_ediv d c)] at h1
    exact h1.symm.neg_right
  have hlt : (d % c).natAbs < k := by
    have h0 : 0 ≤ d % c := Int.emod_nonneg d hc
    have h1 : d % c < |c| := Int.emod_lt_abs d hc
    have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h0 h1
    rwa [Int.natAbs_abs, hk] at this
  have hIH := ih _ hlt (d % c) (-c) rfl hcr
  have hS := L.gaussColumn_neg_inv_of_isCoprime hcr
  rw [neg_neg] at hS
  rw [hd, L.isGaussUnitPerp_gaussColumn_add_mul, hS, L.isGaussUnitPerp_gaussU_iff]
  exact hIH

/-- The Euclidean induction: for coprime `(c, d)`, `F(c,d)` has Hermitian norm one and
lies in `Inv^⊥`. -/
theorem isGaussUnitPerp_gaussColumn {c d : ℤ} (h : IsCoprime c d) :
    L.IsGaussUnitPerp (L.gaussColumn c d) :=
  L.isGaussUnitPerp_gaussColumn_aux _ c d rfl h

theorem gaussHerm_gaussColumn_self {c d : ℤ} (h : IsCoprime c d) :
    L.gaussHerm (L.gaussColumn c d) (L.gaussColumn c d) = 1 :=
  (L.isGaussUnitPerp_gaussColumn h).1

theorem gaussColumn_mem_gaussInvPerp {c d : ℤ} (h : IsCoprime c d) :
    L.gaussColumn c d ∈ L.gaussInvPerp :=
  (L.isGaussUnitPerp_gaussColumn h).2

/-- Every coordinate of a coprime column has modulus at most one. -/
theorem norm_gaussColumn_apply_le {c d : ℤ} (h : IsCoprime c d) (a : L.PolarDiscriminantGroup) :
    ‖L.gaussColumn c d a‖ ≤ 1 :=
  L.norm_apply_le_one_of_gaussHerm_self (L.gaussHerm_gaussColumn_self h) a

theorem norm_gaussColumn_le {c d : ℤ} (h : IsCoprime c d) : ‖L.gaussColumn c d‖ ≤ 1 :=
  L.norm_le_one_of_gaussHerm_self (L.gaussHerm_gaussColumn_self h)

/-! ## The zero-frequency projection `Π₀` -/

/-- `Π₀`: the orthogonal projection onto `ker(T₀ - 1)`, i.e. onto the coordinates with `e(q(a)) = 1`. -/
def gaussPi0 (v : L.PolarDiscriminantGroup → ℂ) (a : L.PolarDiscriminantGroup) : ℂ :=
  if L.polarDiscNormChar a = 1 then v a else 0

theorem gaussPi0_mem_gaussTFixed (v : L.PolarDiscriminantGroup → ℂ) :
    L.gaussPi0 v ∈ L.gaussTFixed := by
  rw [mem_gaussTFixed]
  funext a
  unfold gaussT gaussPi0
  split_ifs with h
  · rw [h, one_mul]
  · rw [mul_zero]

/-- A `T₀`-fixed vector is supported on the coordinates with `e(q(a)) = 1`. -/
theorem apply_eq_zero_of_mem_gaussTFixed {w : L.PolarDiscriminantGroup → ℂ} (hw : L.gaussT w = w)
    {a : L.PolarDiscriminantGroup} (ha : L.polarDiscNormChar a ≠ 1) : w a = 0 := by
  have h := congrFun hw a
  rw [gaussT] at h
  have h' : (L.polarDiscNormChar a - 1) * w a = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 ha)

theorem gaussHerm_gaussPi0 {w : L.PolarDiscriminantGroup → ℂ} (hw : w ∈ L.gaussInv)
    (v : L.PolarDiscriminantGroup → ℂ) : L.gaussHerm w (L.gaussPi0 v) = L.gaussHerm w v := by
  unfold gaussHerm gaussPi0
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  split_ifs with ha
  · rfl
  · rw [L.apply_eq_zero_of_mem_gaussTFixed hw.2 ha, map_zero, zero_mul, zero_mul]

theorem gaussPi0_mem_gaussInvPerp {v : L.PolarDiscriminantGroup → ℂ} (hv : v ∈ L.gaussInvPerp) :
    L.gaussPi0 v ∈ L.gaussInvPerp := by
  intro w hw
  rw [L.gaussHerm_gaussPi0 hw]
  exact hv w hw

/-- `Π₀` maps `Inv^⊥` into `K = Inv^⊥ ∩ ker(T₀ - 1)`. -/
theorem gaussPi0_mem_gaussBoundaryK {v : L.PolarDiscriminantGroup → ℂ} (hv : v ∈ L.gaussInvPerp) :
    L.gaussPi0 v ∈ L.gaussBoundaryK :=
  ⟨L.gaussPi0_mem_gaussInvPerp hv, L.gaussPi0_mem_gaussTFixed v⟩

theorem norm_gaussPi0_apply_le (v : L.PolarDiscriminantGroup → ℂ) (a : L.PolarDiscriminantGroup) :
    ‖L.gaussPi0 v a‖ ≤ ‖v a‖ := by
  unfold gaussPi0
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

/-- `Π₀` is a sup-norm contraction. -/
theorem norm_gaussPi0_le (v : L.PolarDiscriminantGroup → ℂ) : ‖L.gaussPi0 v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a ↦
    (L.norm_gaussPi0_apply_le v a).trans (norm_le_pi_norm v a)

/-- The column bound for lemma 6: `Π₀ F(c,d) ∈ K` and `‖Π₀ F(c,d)‖ ≤ 1` for coprime `(c, d)`. -/
theorem gaussPi0_gaussColumn_mem_gaussBoundaryK {c d : ℤ} (h : IsCoprime c d) :
    L.gaussPi0 (L.gaussColumn c d) ∈ L.gaussBoundaryK :=
  L.gaussPi0_mem_gaussBoundaryK (L.gaussColumn_mem_gaussInvPerp h)

theorem norm_gaussPi0_gaussColumn_le {c d : ℤ} (h : IsCoprime c d) :
    ‖L.gaussPi0 (L.gaussColumn c d)‖ ≤ 1 :=
  (L.norm_gaussPi0_le _).trans (L.norm_gaussColumn_le h)

/-! ## `U` as a continuous linear operator, in the form of the bounded cluster lemma -/

/-- `U` as a linear map. -/
def gaussULinear : (L.PolarDiscriminantGroup → ℂ) →ₗ[ℂ] (L.PolarDiscriminantGroup → ℂ) where
  toFun := L.gaussU
  map_add' := L.gaussU_add
  map_smul' := L.gaussU_smul

/-- `U` as a continuous linear operator on the finite-dimensional space `ℂ[A]`. -/
def gaussUCLM : (L.PolarDiscriminantGroup → ℂ) →L[ℂ] (L.PolarDiscriminantGroup → ℂ) :=
  LinearMap.toContinuousLinearMap L.gaussULinear

@[simp]
theorem gaussUCLM_apply (v : L.PolarDiscriminantGroup → ℂ) : L.gaussUCLM v = L.gaussU v :=
  rfl

/-- The no-fixed-vector hypothesis of the bounded cluster lemma, for `K = Inv^⊥ ∩ ker(T₀ - 1)`. -/
theorem gaussUCLM_eq_self_imp :
    ∀ w ∈ L.gaussBoundaryK, L.gaussUCLM w = w → w = 0 :=
  fun _ hw hU ↦ L.eq_zero_of_mem_gaussBoundaryK hw hU

end PositiveDefiniteIntegralLattice
