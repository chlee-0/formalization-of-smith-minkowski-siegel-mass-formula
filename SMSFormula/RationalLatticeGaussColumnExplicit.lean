import SMSFormula.RationalLatticeGaussColumnEuclid
import SMSFormula.RationalAdeleGaussRamanujanCoefficient

/-!
# The explicit Gauss-sum form of the columns

For `c ≥ 1`, an integer `d` and a class `[u]` of the discriminant group (`u ∈ ℤ⁴`, `ν = S⁻¹u`),

`F(c, d)_{[u]} = -κ c⁻² e(-(d/c) q(ν)) G_u(c, d)`   (`gaussColumn_explicit`),

where `κ = √det S⁻¹` and `G_u(c, d) = Σ_{z mod c} e(-d P_u(z)/c)` is the coset Gauss sum of the integral
polynomial `P_u(z) = q(z) + uᵀz` (`cosetGaussSum`).  Since `q(ν + z) = q(ν) + P_u(z)`, this is the answer's
`F(c,d)_ν = -(√D c²)⁻¹ Σ_{x ∈ L/cL} e(-(d/c) q(x + ν))`.

Proof, from the definition of the column by residues `r mod m`, `m = 2c²|det S|`:
* the class-`[u]` residues are `ū + S̄ y` (`y mod m`), with fibres of size `#ker S̄`
  (`sum_comp_eq_card_ker_smul`); the phase at `u + S y` is `e(-(d/c) q(ν)) e(-d P_u(y)/c)` by the
  `polarDualNorm_add_gram`;
* reduction `(ℤ/m)⁴ → (ℤ/c)⁴` has fibres of size `#ker π` with `#ker π · c⁴ = m⁴`;
* at `d = 0` the same identity counts the class residues, and summing over the classes gives
  `#ker S̄ = |A|`; finally `κ²|A| = 1` (`polarKappa_sq_mul_card`).
The cardinality of `A` is never computed.

Consequently the row coefficient `B_{c,[u]}(q(ν) + λ) = c⁻² Σ*_{a mod c} F(c,a)_{[u]} e((q(ν) + λ) a/c)` equals
`-κ A^{cos}_c(u, λ)` with the coset Gauss–Ramanujan coefficient
`A^{cos}_c(u, λ) = c⁻⁴ Σ*_{a mod c} e(λa/c) G_u(c, a)` (`gaussRowCoefficient_eq`).  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Finset

namespace PositiveDefiniteIntegralLattice

/-! ## Uniform fibres -/

/-- A sum through an additive homomorphism of finite groups, of a function vanishing off its range, is
`#ker` times the full sum. -/
theorem sum_comp_eq_card_ker_smul {G H M : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [AddCommMonoid M] (φ : G →+ H) (f : H → M)
    (hf : ∀ h, h ∉ Set.range φ → f h = 0) :
    ∑ g, f (φ g) = (univ.filter fun g ↦ φ g = 0).card • ∑ h, f h := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := univ) (fun _ _ ↦ mem_univ _), Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [Finset.sum_congr rfl (fun g hg ↦ by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const]
  by_cases hh : h ∈ Set.range φ
  · rw [AddMonoidHom.card_fiber_eq_of_mem_range φ hh ⟨0, map_zero φ⟩]
  · rw [hf h hh, smul_zero, smul_zero]

/-! ## The coset polynomial and its Gauss sum (any rank) -/

section Coset

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- The coset polynomial `P_u(z) = q(z) + uᵀz` reduced modulo `c`. -/
def zmodCosetPoly (u : Fin n → ℤ) (c : ℕ) (z : Fin n → ZMod c) : ZMod c :=
  L.zmodQuadForm c z + ∑ i, ((u i : ℤ) : ZMod c) * z i

theorem zmodCosetPoly_intCast (u : Fin n → ℤ) (c : ℕ) (z : Fin n → ℤ) :
    L.zmodCosetPoly u c (fun i ↦ ((z i : ℤ) : ZMod c)) = ((u ⬝ᵥ z + L.quadForm z : ℤ) : ZMod c) := by
  rw [zmodCosetPoly, zmodQuadForm_intCast]
  push_cast [dotProduct]
  ring

/-- The coset Gauss sum `G_u(c, d) = Σ_{z mod c} e(-d P_u(z)/c)`. -/
def cosetGaussSum (u : Fin n → ℤ) (c : ℕ) [NeZero c] (d : ℤ) : ℂ :=
  ∑ z : Fin n → ZMod c, ZMod.stdAddChar (-((d : ZMod c) * L.zmodCosetPoly u c z))

theorem cosetGaussSum_zero (u : Fin n → ℤ) (c : ℕ) [NeZero c] :
    L.cosetGaussSum u c 0 = (c : ℂ) ^ n := by
  simp [cosetGaussSum, Fintype.card_pi, ZMod.card]

/-- The dual phase along the polar sublattice: `e(-(d/c) q(ν + z)) = e(-(d/c) q(ν)) e(-d P_u(z)/c)`. -/
theorem polarDualPhase_add_gram_eq (c : ℕ) [NeZero c] (d : ℤ) (u z : Fin n → ℤ) :
    L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) (u + L.polarGramMatrix *ᵥ z) =
      L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) u *
        ZMod.stdAddChar (-((d : ZMod c) * L.zmodCosetPoly u c (fun i ↦ ((z i : ℤ) : ZMod c)))) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  unfold polarDualPhase
  rw [L.polarDualNorm_add_gram, zmodCosetPoly_intCast,
    show -((d : ZMod c) * (((u ⬝ᵥ z + L.quadForm z : ℤ)) : ZMod c)) =
      ((-(d * (u ⬝ᵥ z + L.quadForm z)) : ℤ) : ZMod c) by push_cast; ring,
    ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The coset Gauss–Ramanujan coefficient `A^{cos}_c(u, λ) = c⁻ⁿ Σ*_{a mod c} e(λa/c) G_u(c, a)`. -/
def cosetGaussRamanujanCoefficient (u : Fin n → ℤ) (lam : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  ((c : ℂ) ^ n)⁻¹ * ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
    ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a

end Coset

/-! ## The explicit column (rank four) -/

variable (L : PositiveDefiniteIntegralLattice 4)

/-- The reduction `(ℤ/m)ᵏ → (ℤ/c)ᵏ` for `c ∣ m`. -/
def zmodPiCast {k m c : ℕ} (h : c ∣ m) : (Fin k → ZMod m) →+ (Fin k → ZMod c) :=
  AddMonoidHom.compLeft (ZMod.castHom h (ZMod c)).toAddMonoidHom (Fin k)

theorem zmodPiCast_surjective {k m c : ℕ} (h : c ∣ m) :
    Function.Surjective (zmodPiCast (k := k) h) :=
  (ZMod.castHom_surjective h).comp_left

/-- The polar matrix `S̄` acting on `(ℤ/m)⁴`. -/
def zmodGramHom (m : ℕ) : (Fin 4 → ZMod m) →+ (Fin 4 → ZMod m) :=
  (L.polarGramMatrix.map (Int.castRingHom (ZMod m))).mulVecLin.toAddMonoidHom

theorem zmodGramHom_apply (m : ℕ) (y : Fin 4 → ZMod m) :
    L.zmodGramHom m y = L.polarGramMatrix.map (Int.castRingHom (ZMod m)) *ᵥ y :=
  rfl

theorem intCast_polarGramMatrix_mulVec (m : ℕ) (z : Fin 4 → ℤ) :
    (fun i ↦ (((L.polarGramMatrix *ᵥ z) i : ℤ) : ZMod m)) =
      L.polarGramMatrix.map (Int.castRingHom (ZMod m)) *ᵥ (fun i ↦ ((z i : ℤ) : ZMod m)) := by
  have h := RingHom.map_mulVec (Int.castRingHom (ZMod m)) L.polarGramMatrix z
  funext i
  simpa using h i

theorem c_dvd_gaussColumnLevel (c : ℕ) : c ∣ L.gaussColumnLevel (c : ℤ) := by
  unfold gaussColumnLevel
  rw [Int.natAbs_natCast]
  exact Dvd.intro (2 * c * L.polarGramMatrix.det.natAbs) (by ring)

theorem intCast_residueLift {k m : ℕ} [NeZero m] (y : Fin k → ZMod m) :
    (fun i ↦ ((residueLift y i : ℤ) : ZMod m)) = y := by
  funext i
  simp [residueLift]

theorem intCast_residueLift_eq_zmodPiCast {k m c : ℕ} [NeZero m] (h : c ∣ m) (y : Fin k → ZMod m) :
    (fun i ↦ ((residueLift y i : ℤ) : ZMod c)) = zmodPiCast h y := by
  funext i
  show ((((y i).val : ℕ) : ℤ) : ZMod c) = ((y i).cast : ZMod c)
  rw [ZMod.cast_eq_val, Int.cast_natCast]

theorem polarDualPhase_zero (u : Fin 4 → ℤ) (c : ℤ) : L.polarDualPhase (-((0 : ℤ) : ℚ) / c) u = 1 := by
  simp [polarDualPhase]

/-- The fibre identity: `#ker S̄ · Σ_r w_{c,d,[u]}(r) = e(-(d/c) q(ν)) · #ker π · G_u(c, d)`. -/
theorem card_ker_mul_sum_gaussColumnWeight (c : ℕ) [NeZero c] (d : ℤ) (u : Fin 4 → ℤ) :
    haveI : NeZero (L.gaussColumnLevel (c : ℤ)) :=
      ⟨L.gaussColumnLevel_ne_zero (by exact_mod_cast NeZero.ne c)⟩
    ((univ.filter fun y ↦ L.zmodGramHom (L.gaussColumnLevel (c : ℤ)) y = 0).card : ℂ) *
        ∑ r, L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) r =
      L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) u *
        (((univ.filter fun y ↦ zmodPiCast (k := 4) (L.c_dvd_gaussColumnLevel c) y = 0).card : ℂ) *
          L.cosetGaussSum u c d) := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  haveI : NeZero (L.gaussColumnLevel (c : ℤ)) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  set m := L.gaussColumnLevel (c : ℤ) with hm
  set ubar : Fin 4 → ZMod m := fun i ↦ ((u i : ℤ) : ZMod m) with hubar
  -- the class residues are `ū + S̄ y`
  have hf : ∀ r', r' ∉ Set.range (L.zmodGramHom m) →
      L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) (ubar + r') = 0 := by
    intro r' hr'
    unfold gaussColumnWeight
    rw [if_neg]
    intro hcl
    apply hr'
    obtain ⟨y₀, hy₀⟩ := L.eq_add_gram_of_rel (QuotientAddGroup.eq.1 hcl.symm)
    refine ⟨fun i ↦ ((y₀ i : ℤ) : ZMod m), ?_⟩
    rw [zmodGramHom_apply, ← intCast_polarGramMatrix_mulVec]
    have hcast := congrArg (fun v : Fin 4 → ℤ ↦ fun i ↦ ((v i : ℤ) : ZMod m)) hy₀
    simp only [intCast_residueLift] at hcast
    funext i
    have hi := congrFun hcast i
    simp only [Pi.add_apply, Int.cast_add, hubar] at hi
    exact (add_left_cancel hi).symm
  have h1 := sum_comp_eq_card_ker_smul (L.zmodGramHom m)
    (fun r' ↦ L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) (ubar + r')) hf
  have htrans : ∑ r', L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) (ubar + r') =
      ∑ r, L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) r :=
    Fintype.sum_equiv (Equiv.addLeft ubar) _ _ fun _ ↦ rfl
  rw [htrans] at h1
  -- the weight along `ū + S̄ y`
  have hw : ∀ y, L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) (ubar + L.zmodGramHom m y) =
      L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) u *
        ZMod.stdAddChar (-((d : ZMod c) *
          L.zmodCosetPoly u c (zmodPiCast (L.c_dvd_gaussColumnLevel c) y))) := by
    intro y
    have hrep : ubar + L.zmodGramHom m y =
        fun i ↦ (((u + L.polarGramMatrix *ᵥ residueLift y) i : ℤ) : ZMod m) := by
      rw [zmodGramHom_apply]
      conv_lhs => rw [← intCast_residueLift y]
      rw [← intCast_polarGramMatrix_mulVec]
      funext i
      simp only [hubar, Pi.add_apply, Int.cast_add]
    have hcl : ((u + L.polarGramMatrix *ᵥ residueLift y : Fin 4 → ℤ) : L.PolarDiscriminantGroup) =
        (u : L.PolarDiscriminantGroup) := by
      rw [QuotientAddGroup.mk_add, add_eq_left, QuotientAddGroup.eq_zero_iff]
      exact (L.mem_polarGramRange_iff _).2 ⟨_, rfl⟩
    rw [hrep, L.gaussColumnWeight_intCast hc, if_pos hcl, L.polarDualPhase_add_gram_eq c,
      intCast_residueLift_eq_zmodPiCast]
  simp_rw [hw] at h1
  have h2 := sum_comp_eq_card_ker_smul (zmodPiCast (L.c_dvd_gaussColumnLevel c))
    (fun w ↦ ZMod.stdAddChar (-((d : ZMod c) * L.zmodCosetPoly u c w)))
    (fun h hh ↦ absurd (zmodPiCast_surjective _ h) hh)
  rw [← Finset.mul_sum, h2] at h1
  rw [← nsmul_eq_mul, ← h1, cosetGaussSum, nsmul_eq_mul, mul_left_comm]

/-- `#ker π · cᵏ = mᵏ`. -/
theorem card_ker_zmodPiCast_mul {k m c : ℕ} [NeZero m] [NeZero c] (h : c ∣ m) :
    (univ.filter fun y ↦ zmodPiCast (k := k) h y = 0).card * c ^ k = m ^ k := by
  have := sum_comp_eq_card_ker_smul (zmodPiCast (k := k) h) (fun _ ↦ (1 : ℕ))
    (fun w hw ↦ absurd (zmodPiCast_surjective h w) hw)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact this.symm

/-- Counting the class residues: `#ker S̄ · #{r mod m : r ∈ a} = m⁴`. -/
theorem card_ker_zmodGramHom_mul_classCount (c : ℕ) [NeZero c] (a : L.PolarDiscriminantGroup) :
    haveI : NeZero (L.gaussColumnLevel (c : ℤ)) :=
      ⟨L.gaussColumnLevel_ne_zero (by exact_mod_cast NeZero.ne c)⟩
    ((univ.filter fun y ↦ L.zmodGramHom (L.gaussColumnLevel (c : ℤ)) y = 0).card : ℂ) *
        ∑ r, L.gaussColumnWeight (c : ℤ) 0 a r = ((L.gaussColumnLevel (c : ℤ) : ℕ) : ℂ) ^ 4 := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  haveI : NeZero (L.gaussColumnLevel (c : ℤ)) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [L.card_ker_mul_sum_gaussColumnWeight c 0 u, L.polarDualPhase_zero, L.cosetGaussSum_zero, one_mul]
  exact_mod_cast card_ker_zmodPiCast_mul (k := 4) (L.c_dvd_gaussColumnLevel c)

theorem sum_classes_gaussColumnWeight_zero (c : ℕ) [NeZero c] :
    haveI : NeZero (L.gaussColumnLevel (c : ℤ)) :=
      ⟨L.gaussColumnLevel_ne_zero (by exact_mod_cast NeZero.ne c)⟩
    ∑ a : L.PolarDiscriminantGroup, ∑ r, L.gaussColumnWeight (c : ℤ) 0 a r =
      ((L.gaussColumnLevel (c : ℤ) : ℕ) : ℂ) ^ 4 := by
  haveI : NeZero (L.gaussColumnLevel (c : ℤ)) :=
    ⟨L.gaussColumnLevel_ne_zero (by exact_mod_cast NeZero.ne c)⟩
  rw [Finset.sum_comm]
  have h : ∀ r : Fin 4 → ZMod (L.gaussColumnLevel (c : ℤ)),
      ∑ a : L.PolarDiscriminantGroup, L.gaussColumnWeight (c : ℤ) 0 a r = 1 := by
    intro r
    unfold gaussColumnWeight
    rw [Finset.sum_ite_eq, if_pos (mem_univ _), L.polarDualPhase_zero]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- `#ker S̄ = |A|`. -/
theorem card_ker_zmodGramHom (c : ℕ) [NeZero c] :
    haveI : NeZero (L.gaussColumnLevel (c : ℤ)) :=
      ⟨L.gaussColumnLevel_ne_zero (by exact_mod_cast NeZero.ne c)⟩
    ((univ.filter fun y ↦ L.zmodGramHom (L.gaussColumnLevel (c : ℤ)) y = 0).card : ℂ) =
      Fintype.card L.PolarDiscriminantGroup := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  haveI : NeZero (L.gaussColumnLevel (c : ℤ)) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  have hm : ((L.gaussColumnLevel (c : ℤ) : ℕ) : ℂ) ^ 4 ≠ 0 :=
    pow_ne_zero 4 (by exact_mod_cast L.gaussColumnLevel_ne_zero hc)
  have hsum := congrArg (fun x ↦ ((univ.filter fun y ↦
    L.zmodGramHom (L.gaussColumnLevel (c : ℤ)) y = 0).card : ℂ) * x)
    (L.sum_classes_gaussColumnWeight_zero c)
  simp only [Finset.mul_sum, L.card_ker_zmodGramHom_mul_classCount c, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  exact (mul_right_cancel₀ hm hsum).symm

/-- The explicit column (2.1): `F(c, d)_{[u]} = -κ c⁻² e(-(d/c) q(ν)) G_u(c, d)`. -/
theorem gaussColumn_explicit (c : ℕ) [NeZero c] (d : ℤ) (u : Fin 4 → ℤ) :
    L.gaussColumn (c : ℤ) d (u : L.PolarDiscriminantGroup) =
      -(L.polarKappa : ℂ) * ((c : ℂ) ^ 2)⁻¹ * L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) u *
        L.cosetGaussSum u c d := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  haveI : NeZero (L.gaussColumnLevel (c : ℤ)) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  set m := L.gaussColumnLevel (c : ℤ) with hmdef
  set K₁ := (univ.filter fun y ↦ L.zmodGramHom m y = 0).card with hK₁
  set K₂ := (univ.filter fun y ↦ zmodPiCast (k := 4) (L.c_dvd_gaussColumnLevel c) y = 0).card with hK₂
  set W := ∑ r, L.gaussColumnWeight (c : ℤ) d (u : L.PolarDiscriminantGroup) r with hW
  set P := L.polarDualPhase (-(d : ℚ) / ((c : ℤ) : ℚ)) u with hP
  set G := L.cosetGaussSum u c d with hG
  have hmain : (K₁ : ℂ) * W = P * ((K₂ : ℂ) * G) := L.card_ker_mul_sum_gaussColumnWeight c d u
  have hA : (K₁ : ℂ) = Fintype.card L.PolarDiscriminantGroup := L.card_ker_zmodGramHom c
  have hK : (K₂ : ℂ) * (c : ℂ) ^ 4 = (m : ℂ) ^ 4 := by
    exact_mod_cast card_ker_zmodPiCast_mul (k := 4) (L.c_dvd_gaussColumnLevel c)
  have hκ : (L.polarKappa : ℂ) ^ 2 * (Fintype.card L.PolarDiscriminantGroup : ℂ) = 1 := by
    exact_mod_cast L.polarKappa_sq_mul_card
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast L.gaussColumnLevel_ne_zero hc
  have hk0 : (L.polarKappa : ℂ) ≠ 0 := by exact_mod_cast L.polarKappa_pos.ne'
  have hWexp : W = (L.polarKappa : ℂ) ^ 2 * ((m : ℂ) ^ 4 / (c : ℂ) ^ 4) * P * G := by
    have hK' : (K₂ : ℂ) = (m : ℂ) ^ 4 / (c : ℂ) ^ 4 := by
      rw [← hK]; field_simp
    calc W = ((L.polarKappa : ℂ) ^ 2 * (Fintype.card L.PolarDiscriminantGroup : ℂ)) * W := by
          rw [hκ, one_mul]
      _ = (L.polarKappa : ℂ) ^ 2 * ((K₁ : ℂ) * W) := by rw [hA]; ring
      _ = _ := by rw [hmain, hK']; ring
  have hm0' : ((L.gaussColumnLevel (c : ℤ) : ℕ) : ℂ) ≠ 0 := hm0
  rw [gaussColumn, dif_neg hc, ← hW, hWexp]
  push_cast
  field_simp
  ring

/-! ## The row coefficient (4.2) -/

/-- The row coefficient `B_{c,a}(m) = c⁻² Σ*_{0 ≤ j < c} F(c, j)_a e(m j/c)`. -/
def gaussRowCoefficient (c : ℕ) (a : L.PolarDiscriminantGroup) (m : ℝ) : ℂ :=
  ((c : ℂ) ^ 2)⁻¹ * ∑ j ∈ (range c).filter (fun j ↦ c.Coprime j),
    L.gaussColumn (c : ℤ) j a * exp (2 * Real.pi * I * (m : ℂ) * (j : ℂ) / (c : ℂ))

/-- The row coefficient (4.2): at a frequency `m = q(ν) + λ` of the class `[u]`,
`B_{c,[u]}(m) = -κ A^{cos}_c(u, λ)`. -/
theorem gaussRowCoefficient_eq (c : ℕ) [NeZero c] (u : Fin 4 → ℤ) (lam : ℤ) :
    L.gaussRowCoefficient c (u : L.PolarDiscriminantGroup) (L.polarDualNorm u + lam) =
      -(L.polarKappa : ℂ) * L.cosetGaussRamanujanCoefficient u lam c := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  unfold gaussRowCoefficient cosetGaussRamanujanCoefficient
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [L.gaussColumn_explicit c j u]
  have hphase : L.polarDualPhase (-((j : ℤ) : ℚ) / ((c : ℤ) : ℚ)) u *
      exp (2 * Real.pi * I * (((L.polarDualNorm u + lam : ℝ)) : ℂ) * (j : ℂ) / (c : ℂ)) =
      ZMod.stdAddChar ((lam : ZMod c) * (j : ZMod c)) := by
    rw [show ((lam : ZMod c) * (j : ZMod c)) = (((lam * j : ℤ)) : ZMod c) by push_cast; ring,
      ZMod.stdAddChar_coe]
    unfold polarDualPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  calc ((c : ℂ) ^ 2)⁻¹ * (-(L.polarKappa : ℂ) * ((c : ℂ) ^ 2)⁻¹ *
        L.polarDualPhase (-(((j : ℕ) : ℤ) : ℚ) / ((c : ℤ) : ℚ)) u * L.cosetGaussSum u c (j : ℤ) *
        exp (2 * Real.pi * I * (((L.polarDualNorm u + lam : ℝ)) : ℂ) * (j : ℂ) / (c : ℂ)))
      = -(L.polarKappa : ℂ) * ((c : ℂ) ^ 4)⁻¹ * (L.polarDualPhase (-((j : ℤ) : ℚ) / ((c : ℤ) : ℚ)) u *
          exp (2 * Real.pi * I * (((L.polarDualNorm u + lam : ℝ)) : ℂ) * (j : ℂ) / (c : ℂ))) *
          L.cosetGaussSum u c (j : ℤ) := by
        field_simp
    _ = _ := by rw [hphase]; ring

end PositiveDefiniteIntegralLattice
