import SMSFormula.RationalLatticeCosetGaussRamanujan

/-!
# The squaring bound for coset Gauss sums

For a unit `a mod c` the coset Gauss sum `G_u(c, a) = Σ_{z mod c} e(-a P_u(z)/c)` satisfies

`|G_u(c, a)|² ≤ cᵏ · #ker(S mod c) ≤ cᵏ · Dᵏ`   (`norm_cosetGaussSum_sq_le`, rank `k`, `D = |det S|`).

Proof (squaring): `G · conj G = Σ_h e(-a P_u(h)/c) Σ_y e(-a yᵀSh/c)`, by `z = y + h` and the reduced polarization
`q(y + h) = q(y) + yᵀSh + q(h)`; the inner sum is `cᵏ [Sh ≡ 0]` (character orthogonality, `a` a unit).  The
kernel of `S mod c` lies in the kernel of `D` (adjugate), and `#{t mod c : Dt ≡ 0} ≤ D` by the injection
`t ↦ D t / c`.  The linear term `uᵀz` never matters for the bound.  In rank four this gives
`‖A^{cos}_c(u, λ)‖ ≤ D² φ(c)/c² ≤ D²/c` (`norm_cosetGaussRamanujanCoefficient_le`).  Nothing is chosen.
-/

noncomputable section

open Matrix Finset ComplexConjugate

namespace PositiveDefiniteIntegralLattice

variable {k : ℕ}

/-! ## The kernel of the determinant and of the polar matrix -/

/-- `#{t mod c : D t ≡ 0} ≤ D`. -/
theorem card_filter_natCast_mul_eq_zero_le (c : ℕ) [NeZero c] {D : ℕ} (hD : 0 < D) :
    (univ.filter fun t : ZMod c ↦ (D : ZMod c) * t = 0).card ≤ D := by
  have hdvd : ∀ s ∈ univ.filter (fun s : ZMod c ↦ (D : ZMod c) * s = 0), c ∣ D * s.val := by
    intro s hs
    have h := (mem_filter.1 hs).2
    rw [← ZMod.natCast_zmod_val s, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hmaps : ∀ t ∈ univ.filter (fun t : ZMod c ↦ (D : ZMod c) * t = 0), D * t.val / c ∈ range D := by
    intro t _
    rw [mem_range, Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne c))]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt t) hD
  have hinj : Set.InjOn (fun t : ZMod c ↦ D * t.val / c)
      (univ.filter fun t ↦ (D : ZMod c) * t = 0 : Finset (ZMod c)) := by
    intro t ht t' ht' heq
    have h1 := Nat.div_mul_cancel (hdvd t ht)
    have h2 := Nat.div_mul_cancel (hdvd t' ht')
    have heq' : D * t.val / c = D * t'.val / c := heq
    have : D * t.val = D * t'.val := by rw [← h1, ← h2, heq']
    exact ZMod.val_injective c (Nat.eq_of_mul_eq_mul_left hD this)
  calc _ ≤ (range D).card := card_le_card_of_injOn _ (fun t ht ↦ hmaps t ht) hinj
    _ = D := card_range D

/-- The polar matrix reduced modulo `c`. -/
abbrev zmodGram (L : PositiveDefiniteIntegralLattice k) (c : ℕ) : Matrix (Fin k) (Fin k) (ZMod c) :=
  L.polarGramMatrix.map (Int.castRingHom (ZMod c))

/-- `#ker(S mod c) ≤ Dᵏ`. -/
theorem card_ker_zmodGram_le (L : PositiveDefiniteIntegralLattice k) (c : ℕ) [NeZero c] :
    (univ.filter fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0).card ≤
      L.polarGramMatrix.det.natAbs ^ k := by
  set D := L.polarGramMatrix.det.natAbs with hDdef
  have hDpos : 0 < L.polarGramMatrix.det := L.polarDeterminant_pos
  have hD : 0 < D := Int.natAbs_pos.2 hDpos.ne'
  set K₀ := univ.filter fun t : ZMod c ↦ (D : ZMod c) * t = 0 with hK₀
  have hdet : (L.zmodGram c).det = ((D : ℕ) : ZMod c) := by
    rw [zmodGram, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast, hDdef,
      ← Int.cast_natCast, Int.natAbs_of_nonneg hDpos.le]
  have hsub : (univ.filter fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0) ⊆
      Fintype.piFinset (fun _ : Fin k ↦ K₀) := by
    intro h hh
    rw [Fintype.mem_piFinset]
    intro i
    rw [hK₀, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hS := (mem_filter.1 hh).2
    have h' := congrArg (fun v ↦ ((L.zmodGram c).adjugate *ᵥ v) i) hS
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h'
    rwa [hdet] at h'
  calc _ ≤ (Fintype.piFinset fun _ : Fin k ↦ K₀).card := card_le_card hsub
    _ = K₀.card ^ k := by rw [Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]
    _ ≤ D ^ k := Nat.pow_le_pow_left (card_filter_natCast_mul_eq_zero_le c hD) k

/-! ## The reduced polarization and the character sum -/

theorem intCast_mulVec_general {m : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (z : Fin k → ℤ) :
    (fun i ↦ (((A *ᵥ z) i : ℤ) : ZMod m)) =
      A.map (Int.castRingHom (ZMod m)) *ᵥ (fun i ↦ ((z i : ℤ) : ZMod m)) := by
  have h := RingHom.map_mulVec (Int.castRingHom (ZMod m)) A z
  funext i
  simpa using h i

/-- `q(y + h) = q(y) + yᵀSh + q(h)` modulo `c`. -/
theorem zmodQuadForm_add (L : PositiveDefiniteIntegralLattice k) (c : ℕ) [NeZero c] (y h : Fin k → ZMod c) :
    L.zmodQuadForm c (y + h) =
      L.zmodQuadForm c y + y ⬝ᵥ (L.zmodGram c *ᵥ h) + L.zmodQuadForm c h := by
  set yl : Fin k → ℤ := fun i ↦ ((y i).val : ℤ) with hyl
  set hl : Fin k → ℤ := fun i ↦ ((h i).val : ℤ) with hhl
  have hy : y = fun i ↦ ((yl i : ℤ) : ZMod c) := by funext i; simp [hyl]
  have hh : h = fun i ↦ ((hl i : ℤ) : ZMod c) := by funext i; simp [hhl]
  have hyh : y + h = fun i ↦ (((yl + hl) i : ℤ) : ZMod c) := by
    rw [hy, hh]; funext i; simp
  rw [hyh, zmodQuadForm_intCast, L.quadForm_add_gram, hy, hh, zmodQuadForm_intCast,
    zmodQuadForm_intCast, zmodGram, ← intCast_mulVec_general]
  push_cast [dotProduct]
  ring

/-- An additive character turns finite sums into products. -/
theorem addChar_map_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Character orthogonality on `(ℤ/c)ᵏ`: `Σ_y e(yᵀv/c) = cᵏ [v = 0]`. -/
theorem sum_stdAddChar_dotProduct (c : ℕ) [NeZero c] (v : Fin k → ZMod c) :
    ∑ y : Fin k → ZMod c, ZMod.stdAddChar (y ⬝ᵥ v) = if v = 0 then (c : ℂ) ^ k else 0 := by
  have h1 : ∀ y : Fin k → ZMod c, ZMod.stdAddChar (y ⬝ᵥ v) = ∏ i, ZMod.stdAddChar (y i * v i) := by
    intro y
    rw [dotProduct, addChar_map_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (t : ZMod c) ↦ ZMod.stdAddChar (t * v i))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar c), ZMod.card, Nat.cast_ite,
    Nat.cast_zero]
  rw [Fintype.prod_ite_zero, Finset.prod_const, card_univ, Fintype.card_fin]
  congr 1
  exact propext ⟨fun h ↦ funext h, fun h i ↦ congrFun h i⟩

/-! ## The squaring bound -/

/-- The squaring identity: `G · conj G = Σ_h e(-a P_u(h)/c) · cᵏ [Sh ≡ 0]` for a unit `a`. -/
theorem cosetGaussSum_mul_conj (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (c : ℕ) [NeZero c] {a : ℤ}
    (ha : IsUnit (a : ZMod c)) :
    L.cosetGaussSum u c a * conj (L.cosetGaussSum u c a) =
      ∑ h : Fin k → ZMod c, ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c h)) *
        (if L.zmodGram c *ᵥ h = 0 then (c : ℂ) ^ k else 0) := by
  unfold cosetGaussSum
  rw [map_sum, Finset.sum_mul_sum]
  -- reindex the first variable as `y + h`
  have hre : ∀ y : Fin k → ZMod c,
      ∑ x : Fin k → ZMod c, ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c x)) *
          conj (ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c y))) =
        ∑ h : Fin k → ZMod c, ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c h)) *
          ZMod.stdAddChar (y ⬝ᵥ (-(a : ZMod c) • (L.zmodGram c *ᵥ h))) := by
    intro y
    rw [← Fintype.sum_equiv (Equiv.addLeft y) (fun h ↦ ZMod.stdAddChar
        (-((a : ZMod c) * L.zmodCosetPoly u c (y + h))) *
          conj (ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c y)))) _ (fun _ ↦ rfl)]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    unfold zmodCosetPoly
    rw [L.zmodQuadForm_add c y h, dotProduct_smul, smul_eq_mul]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  rw [Finset.sum_comm]
  simp_rw [hre]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [← Finset.mul_sum, sum_stdAddChar_dotProduct]
  congr 1
  have hiff : (-(a : ZMod c) • (L.zmodGram c *ᵥ h) = 0) ↔ (L.zmodGram c *ᵥ h = 0) := by
    constructor
    · intro h0
      exact (ha.neg.smul_eq_zero).1 h0
    · intro h0; rw [h0, smul_zero]
  simp only [hiff]

/-- The squaring bound, kernel form: `|G_u(c, a)|² ≤ cᵏ · #ker(S mod c)` for a unit `a mod c`. -/
theorem norm_cosetGaussSum_sq_le_card_ker (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (c : ℕ) [NeZero c]
    {a : ℤ} (ha : IsUnit (a : ZMod c)) :
    ‖L.cosetGaussSum u c a‖ ^ 2 ≤
      (c : ℝ) ^ k * ((univ.filter fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0).card : ℝ) := by
  have hsq : ((‖L.cosetGaussSum u c a‖ ^ 2 : ℝ) : ℂ) =
      L.cosetGaussSum u c a * conj (L.cosetGaussSum u c a) := by
    rw [Complex.mul_conj']; push_cast; rfl
  have hn : ‖L.cosetGaussSum u c a‖ ^ 2 = ‖((‖L.cosetGaussSum u c a‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn, hsq, L.cosetGaussSum_mul_conj u c ha]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ h : Fin k → ZMod c,
      ‖ZMod.stdAddChar (-((a : ZMod c) * L.zmodCosetPoly u c h)) *
          (if L.zmodGram c *ᵥ h = 0 then (c : ℂ) ^ k else 0)‖ =
        if L.zmodGram c *ᵥ h = 0 then (c : ℝ) ^ k else 0 := by
    intro h
    rw [norm_mul, AddChar.norm_apply, one_mul]
    split_ifs
    · rw [norm_pow, Complex.norm_natCast]
    · rw [norm_zero]
  rw [Finset.sum_congr rfl fun h _ ↦ hterm h, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

/-- The squaring bound (4.8): `|G_u(c, a)|² ≤ cᵏ Dᵏ` for a unit `a mod c`. -/
theorem norm_cosetGaussSum_sq_le (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (c : ℕ) [NeZero c] {a : ℤ}
    (ha : IsUnit (a : ZMod c)) :
    ‖L.cosetGaussSum u c a‖ ^ 2 ≤ (c : ℝ) ^ k * (L.polarGramMatrix.det.natAbs : ℝ) ^ k := by
  refine (L.norm_cosetGaussSum_sq_le_card_ker u c ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast L.card_ker_zmodGram_le c

/-- At a level prime to `D` the polar matrix is invertible: `#ker(S mod c) ≤ 1`. -/
theorem card_ker_zmodGram_le_one_of_coprime (L : PositiveDefiniteIntegralLattice k) (c : ℕ) [NeZero c]
    (hc : Nat.Coprime L.polarGramMatrix.det.natAbs c) :
    (univ.filter fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0).card ≤ 1 := by
  have hDpos : 0 < L.polarGramMatrix.det := L.polarDeterminant_pos
  have hdet : (L.zmodGram c).det = ((L.polarGramMatrix.det.natAbs : ℕ) : ZMod c) := by
    rw [zmodGram, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast,
      ← Int.cast_natCast, Int.natAbs_of_nonneg hDpos.le]
  have hunit : IsUnit (((L.polarGramMatrix.det.natAbs : ℕ) : ZMod c)) :=
    (ZMod.unitOfCoprime _ hc).isUnit
  refine Finset.card_le_one.2 fun h hh h' hh' ↦ ?_
  have hzero : ∀ v ∈ univ.filter (fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0), v = 0 := by
    intro v hv
    have hS := (mem_filter.1 hv).2
    funext i
    have h1 := congrArg (fun w ↦ ((L.zmodGram c).adjugate *ᵥ w) i) hS
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [hdet] at h1
    exact (hunit.mul_right_eq_zero).1 h1
  rw [hzero h hh, hzero h' hh']

/-- At a level prime to `D`: `|G_u(c, a)|² ≤ cᵏ`. -/
theorem norm_cosetGaussSum_sq_le_of_coprime (L : PositiveDefiniteIntegralLattice k) (u : Fin k → ℤ) (c : ℕ)
    [NeZero c] (hc : Nat.Coprime L.polarGramMatrix.det.natAbs c) {a : ℤ} (ha : IsUnit (a : ZMod c)) :
    ‖L.cosetGaussSum u c a‖ ^ 2 ≤ (c : ℝ) ^ k := by
  refine (L.norm_cosetGaussSum_sq_le_card_ker u c ha).trans ?_
  have := L.card_ker_zmodGram_le_one_of_coprime c hc
  have h1 : ((univ.filter fun h : Fin k → ZMod c ↦ L.zmodGram c *ᵥ h = 0).card : ℝ) ≤ 1 := by
    exact_mod_cast this
  calc (c : ℝ) ^ k * _ ≤ (c : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

/-- In rank four, `|G_u(c, a)| ≤ c² D²` for a unit `a mod c`. -/
theorem norm_cosetGaussSum_le (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (c : ℕ) [NeZero c] {a : ℤ}
    (ha : IsUnit (a : ZMod c)) :
    ‖L.cosetGaussSum u c a‖ ≤ (c : ℝ) ^ 2 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 := by
  have h := L.norm_cosetGaussSum_sq_le u c ha
  rw [show (c : ℝ) ^ 4 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 4 =
    ((c : ℝ) ^ 2 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 2) ^ 2 by ring] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The termwise coefficient bound in rank four: `‖A^{cos}_c(u, λ)‖ ≤ D² φ(c)/c²`. -/
theorem norm_cosetGaussRamanujanCoefficient_le (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ)
    (c : ℕ) [NeZero c] :
    ‖L.cosetGaussRamanujanCoefficient u lam c‖ ≤
      (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 * (c.totient : ℝ) / (c : ℝ) ^ 2 := by
  have hc : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  unfold cosetGaussRamanujanCoefficient
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
      ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖ ≤
      (c.totient : ℝ) * ((c : ℝ) ^ 2 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
          ‖ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖
        ≤ ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
            (c : ℝ) ^ 2 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          rw [norm_mul, AddChar.norm_apply, one_mul]
          have hca : Nat.Coprime a c := (Nat.coprime_comm).1 (mem_filter.1 ha).2
          have hu : IsUnit (((a : ℕ) : ℤ) : ZMod c) := by
            rw [Int.cast_natCast]
            exact (ZMod.unitOfCoprime a hca).isUnit
          exact L.norm_cosetGaussSum_le u c hu
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]
  calc ((c : ℝ) ^ 4)⁻¹ * ‖∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
        ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖
      ≤ ((c : ℝ) ^ 4)⁻¹ * ((c.totient : ℝ) * ((c : ℝ) ^ 2 * (L.polarGramMatrix.det.natAbs : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- `‖A^{cos}_{p^j}(u, λ)‖ ≤ D²/p^j`. -/
theorem norm_cosetGRCoeff_primePow_le (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    ‖L.cosetGRCoeff u lam (p ^ j)‖ ≤ (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 / (p : ℝ) ^ j := by
  haveI : NeZero (p ^ j) := ⟨pow_ne_zero j hp.ne_zero⟩
  rw [L.cosetGRCoeff_eq_cosetGaussRamanujanCoefficient]
  refine (L.norm_cosetGaussRamanujanCoefficient_le u lam (p ^ j)).trans ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htot : ((p ^ j).totient : ℝ) ≤ (p : ℝ) ^ j := by exact_mod_cast Nat.totient_le (p ^ j)
  rw [Nat.cast_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 * ((p ^ j).totient : ℝ) * (p : ℝ) ^ j
      ≤ (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 * (p : ℝ) ^ j * (p : ℝ) ^ j := by gcongr
    _ = (L.polarGramMatrix.det.natAbs : ℝ) ^ 2 * ((p : ℝ) ^ j) ^ 2 := by ring

/-- In rank four at a level prime to `D`: `‖A^{cos}_c(u, λ)‖ ≤ φ(c)/c² ≤ 1/c`. -/
theorem norm_cosetGaussRamanujanCoefficient_le_of_coprime (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ)
    (lam : ℤ) (c : ℕ) [NeZero c] (hc : Nat.Coprime L.polarGramMatrix.det.natAbs c) :
    ‖L.cosetGaussRamanujanCoefficient u lam c‖ ≤ (c : ℝ)⁻¹ := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  unfold cosetGaussRamanujanCoefficient
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hG : ∀ a ∈ (range c).filter (fun a ↦ c.Coprime a), ‖L.cosetGaussSum u c (a : ℤ)‖ ≤ (c : ℝ) ^ 2 := by
    intro a ha
    have hca : Nat.Coprime a c := (Nat.coprime_comm).1 (mem_filter.1 ha).2
    have hu : IsUnit (((a : ℕ) : ℤ) : ZMod c) := by
      rw [Int.cast_natCast]
      exact (ZMod.unitOfCoprime a hca).isUnit
    have h := L.norm_cosetGaussSum_sq_le_of_coprime u c hc hu
    rw [show (c : ℝ) ^ 4 = ((c : ℝ) ^ 2) ^ 2 by ring] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  have hsum : ‖∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
      ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖ ≤
      (c.totient : ℝ) * (c : ℝ) ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
          ‖ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖
        ≤ ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a), (c : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hG a ha
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]
  have htot : (c.totient : ℝ) ≤ c := by exact_mod_cast Nat.totient_le c
  calc ((c : ℝ) ^ 4)⁻¹ * ‖∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
        ZMod.stdAddChar ((lam : ZMod c) * (a : ZMod c)) * L.cosetGaussSum u c a‖
      ≤ ((c : ℝ) ^ 4)⁻¹ * ((c.totient : ℝ) * (c : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((c : ℝ) ^ 4)⁻¹ * ((c : ℝ) * (c : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htot (by positivity)) (by positivity)
    _ = (c : ℝ)⁻¹ := by field_simp

/-- At a prime `p ∤ D`: `‖A^{cos}_{p^j}(u, λ)‖ ≤ 1/p^j`. -/
theorem norm_cosetGRCoeff_primePow_le_of_not_dvd (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ)
    {p : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ L.polarGramMatrix.det.natAbs) (j : ℕ) :
    ‖L.cosetGRCoeff u lam (p ^ j)‖ ≤ 1 / (p : ℝ) ^ j := by
  haveI : NeZero (p ^ j) := ⟨pow_ne_zero j hp.ne_zero⟩
  have hcop : Nat.Coprime L.polarGramMatrix.det.natAbs (p ^ j) :=
    Nat.Coprime.pow_right j ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpD))
  rw [L.cosetGRCoeff_eq_cosetGaussRamanujanCoefficient]
  refine (L.norm_cosetGaussRamanujanCoefficient_le_of_coprime u lam (p ^ j) hcop).trans (le_of_eq ?_)
  push_cast
  rw [one_div]

end PositiveDefiniteIntegralLattice
