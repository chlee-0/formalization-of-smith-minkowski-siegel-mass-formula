import SMSFormula.AdelicGaussianQuaternionBootstrap

/-!
# The diagonal block bootstrap for the rank-three Spin base case

For positive integers `a, b, c` let `T = ⟨a, b, c⟩` and `U = T ⊥ ⟨abc⟩` (`blockLattice`).  The explicit matrix

`R_x = [[x₄, −x₃/a, x₂/a, x₁], [x₃/b, x₄, −x₁/b, x₂], [−x₂/c, x₁/c, x₄, x₃], [−x₁/(bc), −x₂/(ac), −x₃/(ab), x₄]]`

satisfies `R_xᵀ F_U R_x = λ_x F_U` with `λ_x = q_U(x)/(abc)` and `R_x e₄ = x` (`blockSimilitude_*`).  Hence
* `U ≅ λ_x · U` for every nonzero rational `x`, and
* `x^⊥ ≅ λ_x · T`.

`DiagonalSpinProductFormula` is the natural product formula `τ(Spin_U) = τ(Spin_T)²` for these block lattices.
It is proved downstream in `AdelicSpinDiagonalBlockLocalData`; this module only packages the bootstrap consequences.
It already implies the needed similarity invariance:
the block lattice of `k T` (`k = pq`, `λ_x = p/q`) is isometric to `U`, so `τ(Spin_{kT})² = τ(Spin_U) = τ(Spin_T)²`.
`rankThreeSpinTamagawaOne_of_diagonalProductFormula`: the product formula gives `τ(Spin) = 1` for every ternary lattice
(every ternary lattice is rationally isometric to some `⟨a, b, c⟩`, isometry invariance).  Nothing is chosen in any
statement.
-/

noncomputable section

open scoped ENNReal Matrix
open QuadraticMap Matrix

namespace PositiveDefiniteIntegralLattice

/-! ## The block similitude -/

section Similitude

variable (a b c : ℚ)

/-- The block form `⟨a, b, c, abc⟩`. -/
def blockForm : QuadraticForm ℚ (Fin 4 → ℚ) := weightedSumSquares ℚ ![a, b, c, a * b * c]

/-- The multiplier `λ_x = q_U(x)/(abc)`. -/
def blockMultiplier (x : Fin 4 → ℚ) : ℚ := blockForm a b c x / (a * b * c)

/-- The block similitude `R_x`. -/
def blockSimilitude (x : Fin 4 → ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![x 3, -x 2 / a, x 1 / a, x 0;
    x 2 / b, x 3, -x 0 / b, x 1;
    -x 1 / c, x 0 / c, x 3, x 2;
    -x 0 / (b * c), -x 1 / (a * c), -x 2 / (a * b), x 3]

theorem blockForm_apply (v : Fin 4 → ℚ) :
    blockForm a b c v = a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 + a * b * c * v 3 ^ 2 := by
  simp only [blockForm, weightedSumSquares_apply, Fin.sum_univ_four, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem blockSimilitude_mulVec_last (x : Fin 4 → ℚ) : blockSimilitude a b c x *ᵥ Pi.single 3 1 = x := by
  funext i
  fin_cases i <;> simp [blockSimilitude, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

set_option maxHeartbeats 1600000 in
/-- The similitude identity: `q_U(R_x v) = λ_x q_U(v)`. -/
theorem blockForm_blockSimilitude (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (x v : Fin 4 → ℚ) :
    blockForm a b c (blockSimilitude a b c x *ᵥ v) = blockMultiplier a b c x * blockForm a b c v := by
  rw [blockMultiplier, blockForm_apply, blockForm_apply, blockForm_apply]
  simp [blockSimilitude, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  field_simp
  ring

/-- The block form is positive definite for positive coefficients. -/
theorem blockForm_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {v : Fin 4 → ℚ} (hv : v ≠ 0) :
    0 < blockForm a b c v := by
  rw [blockForm_apply]
  by_contra hle
  push_neg at hle
  apply hv
  have h0 : 0 ≤ a * v 0 ^ 2 := by positivity
  have h1 : 0 ≤ b * v 1 ^ 2 := by positivity
  have h2 : 0 ≤ c * v 2 ^ 2 := by positivity
  have h3 : 0 ≤ a * b * c * v 3 ^ 2 := by positivity
  have e0 : v 0 = 0 := by
    have : a * v 0 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left ha.ne')
  have e1 : v 1 = 0 := by
    have : b * v 1 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left hb.ne')
  have e2 : v 2 = 0 := by
    have : c * v 2 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left hc.ne')
  have e3 : v 3 = 0 := by
    have : a * b * c * v 3 ^ 2 = 0 := by linarith
    have habc : a * b * c ≠ 0 := by positivity
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_left habc)
  funext i
  fin_cases i <;> simp [e0, e1, e2, e3]

theorem blockMultiplier_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {x : Fin 4 → ℚ} (hx : x ≠ 0) :
    0 < blockMultiplier a b c x :=
  div_pos (blockForm_pos a b c ha hb hc hx) (by positivity)

/-- `R_x` is injective for nonzero `x`. -/
theorem blockSimilitude_injective (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {x : Fin 4 → ℚ} (hx : x ≠ 0) :
    Function.Injective (blockSimilitude a b c x).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hv0
  have h := blockForm_blockSimilitude a b c ha.ne' hb.ne' hc.ne' x v
  have hv' : blockSimilitude a b c x *ᵥ v = 0 := hv
  rw [hv', map_zero] at h
  have hpos := mul_pos (blockMultiplier_pos a b c ha hb hc hx) (blockForm_pos a b c ha hb hc hv0)
  linarith

/-- The ambient similitude as an isometry `λ_x · q_U ≅ q_U`. -/
def blockSimilitudeIsometry (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {x : Fin 4 → ℚ} (hx : x ≠ 0) :
    (blockMultiplier a b c x • blockForm a b c).IsometryEquiv (blockForm a b c) where
  toLinearEquiv := LinearEquiv.ofInjectiveEndo _ (blockSimilitude_injective a b c ha hb hc hx)
  map_app' v := by
    change blockForm a b c (blockSimilitude a b c x *ᵥ v) = blockMultiplier a b c x • blockForm a b c v
    rw [blockForm_blockSimilitude a b c ha.ne' hb.ne' hc.ne', smul_eq_mul]

theorem blockSimilitudeIsometry_apply_last (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {x : Fin 4 → ℚ}
    (hx : x ≠ 0) : blockSimilitudeIsometry a b c ha hb hc hx (Pi.single 3 1) = x :=
  blockSimilitude_mulVec_last a b c x

theorem smul_blockForm_associated_last (μ : ℚ) (v : Fin 4 → ℚ) :
    (μ • blockForm a b c).associated (Pi.single 3 1) v = μ * (a * b * c) * v 3 := by
  rw [QuadraticMap.associated_apply, QuadraticMap.smul_apply, QuadraticMap.smul_apply,
    QuadraticMap.smul_apply, blockForm_apply, blockForm_apply, blockForm_apply]
  simp [smul_eq_mul]
  ring

theorem mem_anisotropicOrthogonal_last_iff {μ : ℚ} (hμ : μ ≠ 0) (habc : a * b * c ≠ 0) (v : Fin 4 → ℚ) :
    v ∈ (μ • blockForm a b c).anisotropicOrthogonal (Pi.single 3 1) ↔ v 3 = 0 := by
  rw [QuadraticMap.mem_anisotropicOrthogonal_iff]
  change (μ • blockForm a b c).associated (Pi.single 3 1) v = 0 ↔ _
  rw [smul_blockForm_associated_last]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero hμ habc)
  · intro h
    rw [h, mul_zero]

/-- The complement of the last basis vector in `μ · ⟨a, b, c, abc⟩` is `μ · ⟨a, b, c⟩`. -/
def blockLastComplementIsometry {μ : ℚ} (hμ : μ ≠ 0) (habc : a * b * c ≠ 0) :
    ((μ • blockForm a b c).orthogonalRestriction (Pi.single 3 1)).IsometryEquiv
      (μ • weightedSumSquares ℚ ![a, b, c]) where
  toFun v := ![(v : Fin 4 → ℚ) 0, (v : Fin 4 → ℚ) 1, (v : Fin 4 → ℚ) 2]
  invFun w := ⟨![w 0, w 1, w 2, 0], (mem_anisotropicOrthogonal_last_iff a b c hμ habc _).2 rfl⟩
  left_inv v := by
    obtain ⟨v, hv⟩ := v
    have h3 : v 3 = 0 := (mem_anisotropicOrthogonal_last_iff a b c hμ habc v).1 hv
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [h3]
  right_inv w := by
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    funext i
    fin_cases i <;> rfl
  map_smul' r v := by
    funext i
    fin_cases i <;> rfl
  map_app' v := by
    obtain ⟨v, hv⟩ := v
    have h3 : v 3 = 0 := (mem_anisotropicOrthogonal_last_iff a b c hμ habc v).1 hv
    change μ • weightedSumSquares ℚ ![a, b, c] ![v 0, v 1, v 2] = μ • blockForm a b c v
    rw [blockForm_apply, weightedSumSquares_apply, Fin.sum_univ_three, h3]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, smul_eq_mul]
    ring

end Similitude

/-! ## The diagonal and block lattices -/

theorem diag3_pos {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, 0 < (![a, b, c] : Fin 3 → ℤ) i := by
  intro i
  fin_cases i <;> simpa

theorem block4_pos {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, 0 < (![a, b, c, a * b * c] : Fin 4 → ℤ) i := by
  intro i
  fin_cases i <;> simp <;> positivity

/-- The diagonal ternary lattice `⟨a, b, c⟩`. -/
def diagLattice3 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : PositiveDefiniteIntegralLattice 3 :=
  ofPosDiagonal ![a, b, c] (diag3_pos ha hb hc)

/-- The block lattice `⟨a, b, c⟩ ⊥ ⟨abc⟩`. -/
def blockLattice {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : PositiveDefiniteIntegralLattice 4 :=
  ofPosDiagonal ![a, b, c, a * b * c] (block4_pos ha hb hc)

theorem diagLattice3_quadraticForm {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.quadraticForm =
      weightedSumSquares ℚ ![(a : ℚ), b, c] := by
  rw [diagLattice3, ofPosDiagonal_quadraticForm]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem blockLattice_quadraticForm {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (blockLattice ha hb hc).rationalQuadraticSpaceMatrix.quadraticForm = blockForm a b c := by
  rw [blockLattice, ofPosDiagonal_quadraticForm, blockForm]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The diagonal product formula `τ(Spin_{⟨a,b,c⟩ ⊥ ⟨abc⟩}) = τ(Spin_{⟨a,b,c⟩})²` (proved as
`PositiveDefiniteIntegralLattice.diagonalSpinProductFormula`;
`Spin(U) ≅ Spin(T) × Spin(T)` through the central idempotents `(1 ± e₁e₂e₃e₄/abc)/2`). -/
def DiagonalSpinProductFormula : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (instT : Fintype (diagLattice3 ha hb hc).ConcreteProperRationalDoubleCosetSet) (PT : ℝ) (hPT : 0 < PT)
    (hT : massLocalInverseProductTendsTo (diagLattice3 ha hb hc) PT)
    (instU : Fintype (blockLattice ha hb hc).ConcreteProperRationalDoubleCosetSet) (PU : ℝ) (hPU : 0 < PU)
    (hU : massLocalInverseProductTendsTo (blockLattice ha hb hc) PU),
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (blockLattice ha hb hc) (by norm_num) instU hPU
        hU).spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (diagLattice3 ha hb hc) le_rfl instT hPT
          hT).spinTamagawaNumberENNReal *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (diagLattice3 ha hb hc) le_rfl instT hPT
          hT).spinTamagawaNumberENNReal

/-- The block lattice of `⟨ka, kb, kc⟩` is rationally isometric to `k · ⟨a, b, c, abc⟩`. -/
def blockFormScaleIsometry (a b c k : ℚ) (hk : k ≠ 0) :
    (blockForm (k * a) (k * b) (k * c)).IsometryEquiv (k • blockForm a b c) where
  toFun v := ![v 0, v 1, v 2, k * v 3]
  invFun w := ![w 0, w 1, w 2, k⁻¹ * w 3]
  left_inv v := by
    funext i
    fin_cases i <;> simp [hk]
  right_inv w := by
    funext i
    fin_cases i <;> simp [hk]
  map_add' v w := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' r v := by
    funext i
    fin_cases i <;> simp [mul_left_comm]
  map_app' v := by
    change k • blockForm a b c ![v 0, v 1, v 2, k * v 3] = blockForm (k * a) (k * b) (k * c) v
    rw [blockForm_apply, blockForm_apply, smul_eq_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-! ## The closure of the bootstrap -/

/-- An equality of quadratic forms as an isometry. -/
def isometryEquivOfEq {M : Type*} [AddCommGroup M] [Module ℚ M] {Q₁ Q₂ : QuadraticForm ℚ M} (h : Q₁ = Q₂) :
    Q₁.IsometryEquiv Q₂ :=
  h ▸ QuadraticMap.IsometryEquiv.refl Q₁

theorem diagLattice3_smul_quadraticForm {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {k : ℕ}
    (hk : 0 < k) :
    ((diagLattice3 ha hb hc).smulLattice k hk).rationalQuadraticSpaceMatrix.quadraticForm =
      (diagLattice3 (mul_pos (by exact_mod_cast hk : (0 : ℤ) < k) ha)
        (mul_pos (by exact_mod_cast hk : (0 : ℤ) < k) hb)
        (mul_pos (by exact_mod_cast hk : (0 : ℤ) < k) hc)).rationalQuadraticSpaceMatrix.quadraticForm := by
  rw [smulLattice_quadraticForm, diagLattice3_quadraticForm, diagLattice3_quadraticForm,
    smul_weightedSumSquares_three]
  push_cast
  rfl

/-- The complement factors (pure algebra): for `x ≠ 0` there is an integer `k > 0` with `x^⊥ ≅ k T` and
`k · q_U ≅ q_U`. -/
theorem exists_blockComplement_isometry_smulLattice {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {x : Fin 4 → ℚ} (hx0 : x ≠ 0) :
    ∃ (k : ℕ) (hk : 0 < k),
      Nonempty (((blockLattice ha hb hc).rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction
        x).IsometryEquiv ((diagLattice3 ha hb hc).smulLattice k hk).rationalQuadraticSpaceMatrix.quadraticForm) ∧
      Nonempty (((k : ℚ) • blockForm (a : ℚ) b c).IsometryEquiv (blockForm (a : ℚ) b c)) := by
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc
  have habc : (a : ℚ) * b * c ≠ 0 := by positivity
  let lam := blockMultiplier (a : ℚ) b c x
  have hlam : 0 < lam := blockMultiplier_pos (a : ℚ) b c haq hbq hcq hx0
  let eS := blockSimilitudeIsometry (a : ℚ) b c haq hbq hcq hx0
  have heS : eS (Pi.single 3 1) = x := blockSimilitudeIsometry_apply_last (a : ℚ) b c haq hbq hcq hx0
  have hk : 0 < lam.num.toNat * lam.den := mul_pos (by have := Rat.num_pos.2 hlam; omega) lam.den_pos
  have hkq : (((lam.num.toNat * lam.den : ℕ)) : ℚ) = (lam.num : ℚ) * (lam.den : ℚ) := by
    have h0 : 0 ≤ lam.num := (Rat.num_pos.2 hlam).le
    have h1 : ((lam.num.toNat : ℕ) : ℚ) = (lam.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h0
    rw [Nat.cast_mul, h1]
  refine ⟨lam.num.toNat * lam.den, hk, ?_, ?_⟩
  · have e1 := eS.orthogonalRestrictionMap (Pi.single 3 1)
    rw [heS] at e1
    have e2 := blockLastComplementIsometry (a : ℚ) b c hlam.ne' habc
    have e3 := (smulRatIsometry (weightedSumSquares ℚ ![(a : ℚ), b, c]) lam.num lam.den lam.den_ne_zero).symm
    rw [Rat.num_div_den] at e3
    rw [smulLattice_quadraticForm, diagLattice3_quadraticForm, hkq]
    change Nonempty (((blockLattice ha hb hc).rationalQuadraticSpaceMatrix.quadraticForm.orthogonalRestriction
      x).IsometryEquiv _)
    rw [blockLattice_quadraticForm]
    exact ⟨(e1.symm.trans e2).trans e3⟩
  · have e4 := smulRatIsometry (blockForm (a : ℚ) b c) lam.num lam.den lam.den_ne_zero
    rw [Rat.num_div_den] at e4
    rw [hkq]
    exact ⟨e4.trans eS⟩

set_option maxHeartbeats 1600000 in
/-- Similarity for the occurring factors: if `k · q_U ≅ q_U`, the product formula gives `τ(Spin_{kT}) = τ(Spin_T)`. -/
theorem spinTamagawaNumberENNReal_smulLattice_eq_of_productFormula (hprod : DiagonalSpinProductFormula)
    {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {k : ℕ} (hk : 0 < k)
    (eK : ((k : ℚ) • blockForm (a : ℚ) b c).IsometryEquiv (blockForm (a : ℚ) b c))
    (instT : Fintype (diagLattice3 ha hb hc).ConcreteProperRationalDoubleCosetSet) {PT : ℝ} (hPT : 0 < PT)
    (hT : massLocalInverseProductTendsTo (diagLattice3 ha hb hc) PT)
    (instk : Fintype ((diagLattice3 ha hb hc).smulLattice k hk).ConcreteProperRationalDoubleCosetSet)
    {Pk : ℝ} (hPk : 0 < Pk)
    (hk' : massLocalInverseProductTendsTo ((diagLattice3 ha hb hc).smulLattice k hk) Pk) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice ((diagLattice3 ha hb hc).smulLattice k hk) le_rfl instk hPk
        hk').spinTamagawaNumberENNReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (diagLattice3 ha hb hc) le_rfl instT hPT
        hT).spinTamagawaNumberENNReal := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  let instU : Fintype (blockLattice ha hb hc).ConcreteProperRationalDoubleCosetSet :=
    (blockLattice ha hb hc).concreteProperRationalDoubleCosetSetFintype
  obtain ⟨PU, hPU, hU⟩ :=
    (blockLattice ha hb hc).exists_pos_massLocalInverseProductTendsTo (by norm_num)
  let instTk : Fintype (diagLattice3 (mul_pos hkz ha) (mul_pos hkz hb)
      (mul_pos hkz hc)).ConcreteProperRationalDoubleCosetSet :=
    (diagLattice3 (mul_pos hkz ha) (mul_pos hkz hb) (mul_pos hkz hc)).concreteProperRationalDoubleCosetSetFintype
  let instUk : Fintype (blockLattice (mul_pos hkz ha) (mul_pos hkz hb)
      (mul_pos hkz hc)).ConcreteProperRationalDoubleCosetSet :=
    (blockLattice (mul_pos hkz ha) (mul_pos hkz hb) (mul_pos hkz hc)).concreteProperRationalDoubleCosetSetFintype
  obtain ⟨PTk, hPTk, hTk⟩ := (diagLattice3 (mul_pos hkz ha) (mul_pos hkz hb)
    (mul_pos hkz hc)).exists_pos_massLocalInverseProductTendsTo le_rfl
  obtain ⟨PUk, hPUk, hUk⟩ := (blockLattice (mul_pos hkz ha) (mul_pos hkz hb)
    (mul_pos hkz hc)).exists_pos_massLocalInverseProductTendsTo (by norm_num)
  have h1 := RationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_eq_of_rationalIsometry _ _
    (isometryEquivOfEq (diagLattice3_smul_quadraticForm ha hb hc hk)) (by norm_num)
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice ((diagLattice3 ha hb hc).smulLattice k hk) le_rfl instk hPk
      hk')
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      (diagLattice3 (mul_pos hkz ha) (mul_pos hkz hb) (mul_pos hkz hc)) le_rfl instTk hPTk hTk)
  have eUk : (blockLattice (mul_pos hkz ha) (mul_pos hkz hb)
      (mul_pos hkz hc)).rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (blockLattice ha hb hc).rationalQuadraticSpaceMatrix.quadraticForm := by
    rw [blockLattice_quadraticForm, blockLattice_quadraticForm]
    push_cast
    exact (blockFormScaleIsometry (a : ℚ) b c k (by exact_mod_cast hk.ne')).trans eK
  have h2 := RationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_eq_of_rationalIsometry _ _ eUk
    (by norm_num)
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      (blockLattice (mul_pos hkz ha) (mul_pos hkz hb) (mul_pos hkz hc)) (by norm_num) instUk hPUk hUk)
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (blockLattice ha hb hc) (by norm_num) instU hPU hU)
  have h3 := hprod _ _ _ (mul_pos hkz ha) (mul_pos hkz hb) (mul_pos hkz hc) instTk PTk hPTk hTk instUk PUk hPUk hUk
  have h4 := hprod a b c ha hb hc instT PT hPT hT instU PU hPU hU
  rw [h3, h4] at h2
  rw [← _root_.sq, ← _root_.sq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast] at h2
  rw [h1]
  exact (ENNReal.rpow_left_injective (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)) h2

set_option maxHeartbeats 1600000 in
/-- The closure: the diagonal product formula gives `τ(Spin_{⟨a,b,c⟩}) = 1`. -/
theorem spinTamagawaNumberENNReal_diagLattice3_eq_one (hprod : DiagonalSpinProductFormula) {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (instT : Fintype (diagLattice3 ha hb hc).ConcreteProperRationalDoubleCosetSet) {PT : ℝ} (hPT : 0 < PT)
    (hT : massLocalInverseProductTendsTo (diagLattice3 ha hb hc) PT) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (diagLattice3 ha hb hc) le_rfl instT hPT
      hT).spinTamagawaNumberENNReal = 1 := by
  classical
  let instU : Fintype (blockLattice ha hb hc).ConcreteProperRationalDoubleCosetSet :=
    (blockLattice ha hb hc).concreteProperRationalDoubleCosetSetFintype
  obtain ⟨PU, hPU, hU⟩ :=
    (blockLattice ha hb hc).exists_pos_massLocalInverseProductTendsTo (by norm_num)
  have ht0 := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice (diagLattice3 ha hb hc) le_rfl instT hPT
    hT).spinTamagawaNumberENNReal_ne_zero
  have htop := (diagLattice3 ha hb hc).spinTamagawaNumberENNReal_ne_top_of_standardTheta (r := 1) le_rfl instT
    hPT hT
  have hUsq := hprod a b c ha hb hc instT PT hPT hT instU PU hPU hU
  have hUt := (blockLattice ha hb hc).spinTamagawaNumberENNReal_eq_of_complementSpinTamagawa_rankFour instU hPU hU
    htop fun x hx LW eW instL PL hPL0 hL ↦ by
      have hx0 : x ≠ 0 := fun h ↦ hx (by rw [h, map_zero])
      obtain ⟨k, hk, ⟨ecomp⟩, ⟨eK⟩⟩ := exists_blockComplement_isometry_smulLattice ha hb hc hx0
      let instk : Fintype ((diagLattice3 ha hb hc).smulLattice k hk).ConcreteProperRationalDoubleCosetSet :=
        ((diagLattice3 ha hb hc).smulLattice k hk).concreteProperRationalDoubleCosetSetFintype
      obtain ⟨Pk, hPk, hk'⟩ :=
        ((diagLattice3 ha hb hc).smulLattice k hk).exists_pos_massLocalInverseProductTendsTo
          le_rfl
      rw [RationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_eq_of_rationalIsometry _ _
        (eW.trans ecomp) (by norm_num) _
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice ((diagLattice3 ha hb hc).smulLattice k hk) le_rfl instk
          hPk hk')]
      exact spinTamagawaNumberENNReal_smulLattice_eq_of_productFormula hprod ha hb hc hk eK instT hPT hT instk
        hPk hk'
  exact ENNReal.eq_one_of_mul_self_eq_self ht0 htop (hUsq.symm.trans hUt)

/-- The rank-three base case from the diagonal product formula: every ternary lattice is rationally isometric to a
positive diagonal `⟨a, b, c⟩` (proof-internal diagonalization), and isometry invariance transports `τ = 1`. -/
theorem rankThreeSpinTamagawaOne_of_diagonalProductFormula (hprod : DiagonalSpinProductFormula) :
    RankThreeSpinTamagawaOne := by
  intro T inst P hP hconv
  obtain ⟨w, hw, ⟨eT⟩⟩ := RationalQuadraticSpaceMatrix.exists_pos_weightedSumSquares_isometryEquiv
    T.rationalQuadraticSpaceMatrix.quadraticForm fun x hx ↦
      T.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos hx
  -- integral diagonal entries `w_i den_i²`
  obtain ⟨e₀⟩ := nonempty_ofPosRatDiagonal_isometryEquiv w hw
  set A : Fin 3 → ℤ := fun i ↦ (w i).num * ((w i).den : ℤ) with hAdef
  have hA : ∀ i, 0 < A i := fun i ↦ num_mul_den_pos (hw i)
  set T₀ := diagLattice3 (hA 0) (hA 1) (hA 2) with hT₀def
  have hT₀form : T₀.rationalQuadraticSpaceMatrix.quadraticForm =
      (ofPosRatDiagonal w hw).rationalQuadraticSpaceMatrix.quadraticForm := by
    rw [diagLattice3_quadraticForm, ofPosRatDiagonal, ofPosDiagonal_quadraticForm]
    congr 1
    funext i
    fin_cases i <;> rfl
  have eTT₀ : T.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      T₀.rationalQuadraticSpaceMatrix.quadraticForm := by
    rw [hT₀form]
    exact eT.trans e₀.symm
  let inst₀ : Fintype T₀.ConcreteProperRationalDoubleCosetSet := T₀.concreteProperRationalDoubleCosetSetFintype
  obtain ⟨P₀, hP₀, hconv₀⟩ := T₀.exists_pos_massLocalInverseProductTendsTo le_rfl
  rw [RationalQuadraticSpaceMatrix.spinTamagawaNumberENNReal_eq_of_rationalIsometry _ _ eTT₀
    (by norm_num) _ (cliffordSpinCandidateRawOnoTamagawaDataOfLattice T₀ le_rfl inst₀ hP₀ hconv₀)]
  exact spinTamagawaNumberENNReal_diagLattice3_eq_one hprod (hA 0) (hA 1) (hA 2) inst₀ hP₀ hconv₀

end PositiveDefiniteIntegralLattice
