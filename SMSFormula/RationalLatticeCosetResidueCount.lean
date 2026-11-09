import SMSFormula.RationalLatticeGaussColumnExplicit

/-!
# Coset residue counts and their reduction to the counts at good levels

For an integral lattice of rank `n + 1` with polar matrix `S = 2F` (`D = det S`), a vector `u ∈ ℤⁿ⁺¹` and
`λ ∈ ℤ`, the coset residue count is

`R_m(u, λ) = m⁻ⁿ #{z mod m : q(z) + uᵀz ≡ λ}`   (`cosetResidueCount`).

* It is multiplicative over coprime levels (Chinese remainder theorem, as for the counts).
* Completing the square without denominators: with `w = adj(S) u`,
  `q(Dz + w) = D² (q(z) + uᵀz) + q(w)` (`quadForm_det_smul_add_adjugate`).  Hence at every level `m`
  prime to `D`, `z ↦ Dz + w` is a bijection and
  `R_m(u, λ) = r_m(q(w) + D²λ)`   (`cosetResidueCount_eq_normalizedResidueCount`),
  the standard count at the fixed integer target `q(w) + D²λ = D² (q(ν) + λ)` (`ν = S⁻¹u`).
No representative of the class is chosen beyond the supplied `u`; the target is independent of the
level.  Nothing is chosen.
-/

noncomputable section

open Matrix Finset

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Integer identities -/

/-- `q(x + y) = q(x) + xᵀ S y + q(y)`. -/
theorem quadForm_add_gram (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℤ) :
    L.quadForm (x + y) = L.quadForm x + x ⬝ᵥ (L.polarGramMatrix *ᵥ y) + L.quadForm y := by
  simp only [quadForm_eq_dotProduct, polarGramMatrix, Matrix.add_mulVec, Matrix.mulVec_add,
    dotProduct_add, add_dotProduct]
  have h : y ⬝ᵥ L.pairingMatrix *ᵥ x = x ⬝ᵥ L.pairingMatrixᵀ *ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [h]
  ring

/-- Completing the square without denominators: `q(Dz + w) = D² (q(z) + uᵀz) + q(w)`, `w = adj(S) u`. -/
theorem quadForm_det_smul_add_adjugate (L : PositiveDefiniteIntegralLattice n) (u z : Fin n → ℤ) :
    L.quadForm (L.polarGramMatrix.det • z + L.polarGramMatrix.adjugate *ᵥ u) =
      L.polarGramMatrix.det ^ 2 * (L.quadForm z + u ⬝ᵥ z) + L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) := by
  rw [L.quadForm_add_gram, L.quadForm_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_comm z u]
  simp only [smul_eq_mul]
  ring

/-! ## The reduced coset polynomial -/

theorem zmodCosetPoly_map (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {m₁ m₂ : ℕ}
    (f : ZMod m₁ →+* ZMod m₂) (z : Fin n → ZMod m₁) :
    f (L.zmodCosetPoly u m₁ z) = L.zmodCosetPoly u m₂ (fun i => f (z i)) := by
  simp only [zmodCosetPoly, map_add, L.zmodQuadForm_map f z, map_sum, map_mul, map_intCast]

/-- The coset polynomial at the lift of a residue vector. -/
theorem zmodCosetPoly_eq_intCast (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) [NeZero m]
    (z : Fin n → ZMod m) :
    L.zmodCosetPoly u m z =
      ((u ⬝ᵥ (fun i ↦ ((z i).val : ℤ)) + L.quadForm (fun i ↦ ((z i).val : ℤ)) : ℤ) : ZMod m) := by
  rw [← L.zmodCosetPoly_intCast]
  congr 1
  funext i
  simp

/-! ## The coset residue count -/

/-- The coset residue count `R_m(u, λ) = m⁻ⁿ #{z mod m : q(z) + uᵀz ≡ λ}` in rank `n + 1`. -/
def cosetResidueCount (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ) (m : ℕ) : ℝ :=
  ((m : ℝ) ^ n)⁻¹ *
    (Nat.card {z : Fin (n + 1) → ZMod m // L.zmodCosetPoly u m z = ((lam : ℤ) : ZMod m)} : ℝ)

/-- The coset solution set at a coprime composite level is the product of the two solution sets. -/
def cosetSolutionCRTEquiv (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {m₁ m₂ : ℕ}
    (h : Nat.Coprime m₁ m₂) (lam : ℤ) :
    {z : Fin n → ZMod (m₁ * m₂) //
        L.zmodCosetPoly u (m₁ * m₂) z = ((lam : ℤ) : ZMod (m₁ * m₂))} ≃
      {z : Fin n → ZMod m₁ // L.zmodCosetPoly u m₁ z = ((lam : ℤ) : ZMod m₁)} ×
        {z : Fin n → ZMod m₂ // L.zmodCosetPoly u m₂ z = ((lam : ℤ) : ZMod m₂)} := by
  have hf : ∀ z : Fin n → ZMod (m₁ * m₂),
      (L.zmodCosetPoly u (m₁ * m₂) z = ((lam : ℤ) : ZMod (m₁ * m₂))) ↔
        (L.zmodCosetPoly u m₁ (residueCoordinateCRT (n := n) h z).1 = ((lam : ℤ) : ZMod m₁) ∧
          L.zmodCosetPoly u m₂ (residueCoordinateCRT (n := n) h z).2 = ((lam : ℤ) : ZMod m₂)) := by
    intro z
    set e := ZMod.chineseRemainder h with he
    set f₁ : ZMod (m₁ * m₂) →+* ZMod m₁ :=
      (RingHom.fst (ZMod m₁) (ZMod m₂)).comp (e : ZMod (m₁ * m₂) →+* ZMod m₁ × ZMod m₂) with hf₁
    set f₂ : ZMod (m₁ * m₂) →+* ZMod m₂ :=
      (RingHom.snd (ZMod m₁) (ZMod m₂)).comp (e : ZMod (m₁ * m₂) →+* ZMod m₁ × ZMod m₂) with hf₂
    have h1 : L.zmodCosetPoly u m₁ (residueCoordinateCRT (n := n) h z).1 =
        f₁ (L.zmodCosetPoly u (m₁ * m₂) z) := by
      rw [L.zmodCosetPoly_map u f₁ z]
      rfl
    have h2 : L.zmodCosetPoly u m₂ (residueCoordinateCRT (n := n) h z).2 =
        f₂ (L.zmodCosetPoly u (m₁ * m₂) z) := by
      rw [L.zmodCosetPoly_map u f₂ z]
      rfl
    rw [h1, h2]
    constructor
    · intro hz
      rw [hz]
      exact ⟨by simp [hf₁], by simp [hf₂]⟩
    · rintro ⟨ha, hb⟩
      have hcast : e (((lam : ℤ) : ZMod (m₁ * m₂))) = (((lam : ℤ) : ZMod m₁), ((lam : ℤ) : ZMod m₂)) := by
        rw [map_intCast]
        rfl
      have hpair : e (L.zmodCosetPoly u (m₁ * m₂) z) = e (((lam : ℤ) : ZMod (m₁ * m₂))) := by
        rw [hcast]
        exact Prod.ext ha hb
      exact e.injective hpair
  exact (Equiv.subtypeEquiv (residueCoordinateCRT (n := n) h) hf).trans Equiv.subtypeProdEquivProd

/-- The coset residue count is multiplicative over coprime levels. -/
theorem cosetResidueCount_mul_of_coprime (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ)
    {m₁ m₂ : ℕ} (h : m₁.Coprime m₂) (lam : ℤ) :
    L.cosetResidueCount u lam (m₁ * m₂) =
      L.cosetResidueCount u lam m₁ * L.cosetResidueCount u lam m₂ := by
  unfold cosetResidueCount
  rw [Nat.card_congr (L.cosetSolutionCRTEquiv u h lam), Nat.card_prod]
  push_cast
  rw [mul_pow, mul_inv]
  ring

theorem cosetResidueCount_one (L : PositiveDefiniteIntegralLattice (n + 1)) (u : Fin (n + 1) → ℤ) (lam : ℤ) :
    L.cosetResidueCount u lam 1 = 1 := by
  unfold cosetResidueCount
  haveI : Unique {z : Fin (n + 1) → ZMod 1 // L.zmodCosetPoly u 1 z = ((lam : ℤ) : ZMod 1)} := by
    refine ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩, fun a => ?_⟩
    exact Subtype.ext (Subsingleton.elim _ _)
  simp

/-! ## Good levels: reduction to the standard counts -/

/-- The fixed integer target `q(adj(S) u) + D² λ`. -/
def cosetStandardTarget (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (lam : ℤ) : ℤ :=
  L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) + L.polarGramMatrix.det ^ 2 * lam

/-- The reduced form of completing the square. -/
theorem zmodQuadForm_det_smul_add (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) [NeZero m]
    (z : Fin n → ZMod m) :
    L.zmodQuadForm m ((L.polarGramMatrix.det : ZMod m) • z +
        fun i ↦ (((L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod m)) =
      (L.polarGramMatrix.det : ZMod m) ^ 2 * L.zmodCosetPoly u m z +
        ((L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) : ℤ) : ZMod m) := by
  set zl : Fin n → ℤ := fun i ↦ ((z i).val : ℤ) with hzl
  have hz : z = fun i ↦ ((zl i : ℤ) : ZMod m) := by
    funext i; simp [hzl]
  have hcast : (L.polarGramMatrix.det : ZMod m) • z + (fun i ↦ (((L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod m)) =
      fun i ↦ (((L.polarGramMatrix.det • zl + L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod m) := by
    rw [hz]
    funext i
    simp
  rw [hcast, zmodQuadForm_intCast, L.quadForm_det_smul_add_adjugate, hz, zmodCosetPoly_intCast]
  push_cast
  ring

/-- At a level prime to `D` the coset count is the standard count at `q(adj(S) u) + D² λ`. -/
theorem cosetResidueCount_eq_normalizedResidueCount (L : PositiveDefiniteIntegralLattice (n + 1))
    (u : Fin (n + 1) → ℤ) (lam : ℤ) {m : ℕ} [NeZero m]
    (hm : Nat.Coprime L.polarGramMatrix.det.natAbs m) :
    L.cosetResidueCount u lam m = L.normalizedResidueCount (L.cosetStandardTarget u lam) m := by
  have hDpos : 0 < L.polarGramMatrix.det := L.polarDeterminant_pos
  have hDcast : ((L.polarGramMatrix.det : ℤ) : ZMod m) = ((L.polarGramMatrix.det.natAbs : ℕ) : ZMod m) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hDpos.le]
  set U : (ZMod m)ˣ := ZMod.unitOfCoprime L.polarGramMatrix.det.natAbs hm with hU
  have hUval : (U : ZMod m) = ((L.polarGramMatrix.det : ℤ) : ZMod m) := by rw [hDcast]; rfl
  have hunit : IsUnit (((L.polarGramMatrix.det : ℤ) : ZMod m) ^ 2) := by
    rw [← hUval]; exact (U.isUnit).pow 2
  set w : Fin (n + 1) → ZMod m := fun i ↦ (((L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod m) with hw
  let e : (Fin (n + 1) → ZMod m) ≃ (Fin (n + 1) → ZMod m) :=
    { toFun := fun z ↦ ((L.polarGramMatrix.det : ℤ) : ZMod m) • z + w
      invFun := fun y ↦ ((U⁻¹ : (ZMod m)ˣ) : ZMod m) • (y - w)
      left_inv := fun z ↦ by
        simp only [add_sub_cancel_right, smul_smul, ← hUval, Units.inv_mul, one_smul]
      right_inv := fun y ↦ by
        simp only [smul_smul, ← hUval, Units.mul_inv, one_smul, sub_add_cancel] }
  have hiff : ∀ z, (L.zmodCosetPoly u m z = ((lam : ℤ) : ZMod m)) ↔
      (L.zmodQuadForm m (e z) = ((L.cosetStandardTarget u lam : ℤ) : ZMod m)) := by
    intro z
    change _ ↔ L.zmodQuadForm m (((L.polarGramMatrix.det : ℤ) : ZMod m) • z + w) = _
    rw [hw, L.zmodQuadForm_det_smul_add u m z, cosetStandardTarget, Int.cast_add, Int.cast_mul,
      Int.cast_pow, add_comm (((L.polarGramMatrix.det : ℤ) : ZMod m) ^ 2 * _), add_right_inj]
    constructor
    · intro h; rw [h]
    · intro h; exact hunit.mul_left_cancel h
  unfold cosetResidueCount normalizedResidueCount
  rw [Nat.card_congr (Equiv.subtypeEquiv
    (p := fun z ↦ L.zmodCosetPoly u m z = ((lam : ℤ) : ZMod m))
    (q := fun y ↦ L.zmodQuadForm m y = ((L.cosetStandardTarget u lam : ℤ) : ZMod m)) e hiff)]

end PositiveDefiniteIntegralLattice
