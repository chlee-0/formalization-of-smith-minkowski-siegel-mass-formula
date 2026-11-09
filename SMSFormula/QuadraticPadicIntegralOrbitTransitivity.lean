import SMSFormula.QuadraticCartanDieudonneParity

/-! Integral-orbit transitivity at a good place (abstract core). Let `Q` be a
quadratic form on `ℚ_p^N`, `p` odd, `N ≥ 2`, whose polar form is integral and
unimodular on the standard lattice `L = {‖x‖ ≤ 1}` (unimodular: a lattice vector
polar-orthogonal to `L` modulo `p` lies in `pL`). For lattice vectors `v, w`
with `Q v = Q w` a unit there is a linear isometry of determinant one mapping
`L` onto `L` and `v` to `w`: a product of two quadratic reflections in
unit-norm lattice vectors. Since `Q (v - w) + Q (v + w) = 4 Q w` is a unit, one
of `v ± w` has unit norm; in the `v - w` case a unit-norm lattice vector
polar-orthogonal to `w` (which exists by unimodularity and `N ≥ 2`) restores
determinant one. No representative, chart or normalization is chosen: the
reflections are in the supplied vectors and an existentially obtained vector. -/
noncomputable section
open CliffordAlgebra

namespace QuadraticMap

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

local notation "E" => (Fin N → ℚ_[p])

/-- The polar form is integral on the standard lattice. -/
def IsPadicIntegralPolar (Q : QuadraticForm ℚ_[p] E) : Prop :=
  ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖polar Q x y‖ ≤ 1

/-- The polar form is unimodular on the standard lattice: a lattice vector whose
polar pairing with every lattice vector is divisible by `p` is divisible by `p`. -/
def IsPadicUnimodularPolar (Q : QuadraticForm ℚ_[p] E) : Prop :=
  ∀ x : E, ‖x‖ ≤ 1 → (∀ y : E, ‖y‖ ≤ 1 → ‖polar Q x y‖ < 1) → ‖x‖ < 1

theorem padic_norm_two_of_ne_two (hp : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  intro hdvd
  exact hp ((Nat.Prime.dvd_iff_eq Nat.prime_two (Fact.out : Nat.Prime p).ne_one).mp hdvd).symm

theorem padic_norm_add_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ≤ 1 :=
  (Padic.nonarchimedean a b).trans (max_le ha hb)

theorem padic_norm_sub_le_one {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact padic_norm_add_le_one ha (by rwa [norm_neg])

theorem padic_norm_add_lt_one {a b : ℚ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖a + b‖ < 1 :=
  (Padic.nonarchimedean a b).trans_lt (max_lt ha hb)

theorem padic_norm_sub_lt_one {a b : ℚ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]
  exact padic_norm_add_lt_one ha (by rwa [norm_neg])

theorem padicVector_norm_le_one_iff {x : E} : ‖x‖ ≤ 1 ↔ ∀ i, ‖x i‖ ≤ 1 :=
  pi_norm_le_iff_of_nonneg zero_le_one

theorem padicVector_norm_add_le_one {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x + y‖ ≤ 1 := by
  rw [padicVector_norm_le_one_iff] at *
  exact fun i ↦ padic_norm_add_le_one (hx i) (hy i)

theorem padicVector_norm_sub_le_one {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x - y‖ ≤ 1 := by
  rw [padicVector_norm_le_one_iff] at *
  exact fun i ↦ padic_norm_sub_le_one (hx i) (hy i)

theorem padicVector_norm_sub_smul_le_one {x u : E} {c : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) : ‖x - c • u‖ ≤ 1 := by
  rw [padicVector_norm_le_one_iff] at *
  intro i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact padic_norm_sub_le_one (hx i) (by rw [norm_mul]; exact mul_le_one₀ hc (norm_nonneg _) (hu i))

variable (Q : QuadraticForm ℚ_[p] (Fin N → ℚ_[p]))

/-- An integral polar form gives integral quadratic values away from `2`. -/
theorem padicIntegralPolar_norm_apply_le_one (hp : p ≠ 2) (hB : IsPadicIntegralPolar (p := p) Q)
    {x : E} (hx : ‖x‖ ≤ 1) : ‖(Q x : ℚ_[p])‖ ≤ 1 := by
  have h := hB x x hx hx
  rw [polar_self, nsmul_eq_mul, norm_mul] at h
  simpa [padic_norm_two_of_ne_two hp] using h

/-- A reflection in a unit-norm lattice vector preserves the lattice. -/
theorem quadraticReflection_norm_le_one (hB : IsPadicIntegralPolar (p := p) Q) {u : E} (hu : ‖u‖ ≤ 1)
    (hQu : Q u ≠ 0) (hQu1 : ‖(Q u : ℚ_[p])‖ = 1) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖quadraticReflectionOfNeZero Q u hQu x‖ ≤ 1 := by
  rw [quadraticReflectionOfNeZero_apply]
  refine padicVector_norm_sub_smul_le_one hx hu ?_
  rw [norm_mul, norm_inv, hQu1, inv_one, one_mul]
  exact hB u x hu hx

/-- The reflection is an involution. -/
theorem quadraticReflectionOfNeZero_apply_apply {u : E} (hQu : Q u ≠ 0) (x : E) :
    quadraticReflectionOfNeZero Q u hQu (quadraticReflectionOfNeZero Q u hQu x) = x := by
  simp only [quadraticReflectionOfNeZero_apply]
  have hcoef : (Q u)⁻¹ * polar Q u (x - ((Q u)⁻¹ * polar Q u x) • u) =
      -((Q u)⁻¹ * polar Q u x) := by
    rw [polar_sub_right, polar_smul_right, polar_self, smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  rw [hcoef, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem quadraticReflectionOfNeZero_symm_apply {u : E} (hQu : Q u ≠ 0) (x : E) :
    (quadraticReflectionOfNeZero Q u hQu).symm x = quadraticReflectionOfNeZero Q u hQu x :=
  (LinearEquiv.symm_apply_eq _).mpr (quadraticReflectionOfNeZero_apply_apply Q hQu x).symm

/-- A reflection moves `v` to `v - b` when the polar pairing equals the norm. -/
theorem quadraticReflectionOfNeZero_apply_of_polar_eq {b : E} (hQb : Q b ≠ 0) {v : E}
    (h : polar Q b v = Q b) : quadraticReflectionOfNeZero Q b hQb v = v - b := by
  rw [quadraticReflectionOfNeZero_apply, h, inv_mul_cancel₀ hQb, one_smul]

/-- Products of two unit reflections: isometries of determinant one preserving the
lattice in both directions. -/
theorem quadraticReflection_trans_props (hB : IsPadicIntegralPolar (p := p) Q) {a b : E}
    (ha : ‖a‖ ≤ 1) (hQa : Q a ≠ 0) (hQa1 : ‖(Q a : ℚ_[p])‖ = 1)
    (hb : ‖b‖ ≤ 1) (hQb : Q b ≠ 0) (hQb1 : ‖(Q b : ℚ_[p])‖ = 1) :
    let g : E ≃ₗ[ℚ_[p]] E := (quadraticReflectionOfNeZero Q b hQb).trans (quadraticReflectionOfNeZero Q a hQa)
    (∀ x, Q (g x) = Q x) ∧ LinearMap.det (g : E →ₗ[ℚ_[p]] E) = 1 ∧
      (∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) ∧ (∀ x, ‖x‖ ≤ 1 → ‖g.symm x‖ ≤ 1) := by
  intro g
  refine ⟨fun x ↦ ?_, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · change Q (quadraticReflectionOfNeZero Q a hQa (quadraticReflectionOfNeZero Q b hQb x)) = Q x
    rw [quadraticReflectionOfNeZero_map_app, quadraticReflectionOfNeZero_map_app]
  · rw [LinearEquiv.coe_trans, LinearMap.det_comp, quadraticReflectionOfNeZero_det,
      quadraticReflectionOfNeZero_det]
    norm_num
  · exact quadraticReflection_norm_le_one Q hB ha hQa hQa1
      (quadraticReflection_norm_le_one Q hB hb hQb hQb1 hx)
  · rw [LinearEquiv.symm_trans_apply, quadraticReflectionOfNeZero_symm_apply,
      quadraticReflectionOfNeZero_symm_apply]
    exact quadraticReflection_norm_le_one Q hB hb hQb hQb1
      (quadraticReflection_norm_le_one Q hB ha hQa hQa1 hx)

/-- Unit-norm orthogonal vector: for a unit-norm lattice vector `w` of a
unimodular integral form of rank at least two (`p` odd) there is a unit-norm
lattice vector polar-orthogonal to `w`. -/
theorem exists_padicUnit_polar_orthogonal (hp : p ≠ 2) (hN : 2 ≤ N)
    (hB : IsPadicIntegralPolar (p := p) Q) (hU : IsPadicUnimodularPolar (p := p) Q) {w : E} (hw : ‖w‖ ≤ 1)
    (hQw : ‖(Q w : ℚ_[p])‖ = 1) : ∃ u : E, ‖u‖ ≤ 1 ∧ ‖(Q u : ℚ_[p])‖ = 1 ∧ polar Q u w = (0 : ℚ_[p]) := by
  by_contra hcon
  have hsmall : ∀ u : E, ‖u‖ ≤ 1 → polar Q u w = (0 : ℚ_[p]) → ‖(Q u : ℚ_[p])‖ < 1 := fun u hu h0 ↦
    lt_of_le_of_ne (padicIntegralPolar_norm_apply_le_one Q hp hB hu)
      (fun h1 ↦ hcon ⟨u, hu, h1, h0⟩)
  have hQw0 : Q w ≠ 0 := by
    intro h; rw [h, norm_zero] at hQw; exact zero_ne_one hQw
  set d : ℚ_[p] := 2 * Q w with hd
  have hd0 : d ≠ 0 := mul_ne_zero two_ne_zero hQw0
  have hd1 : ‖d‖ = 1 := by rw [hd, norm_mul, padic_norm_two_of_ne_two hp, hQw, one_mul]
  set π : E → E := fun x ↦ x - (polar Q x w / d) • w with hπ
  have hcoef : ∀ x : E, ‖x‖ ≤ 1 → ‖polar Q x w / d‖ ≤ 1 := fun x hx ↦ by
    rw [norm_div, hd1, div_one]; exact hB x w hx hw
  have hπL : ∀ x : E, ‖x‖ ≤ 1 → ‖π x‖ ≤ 1 := fun x hx ↦
    padicVector_norm_sub_smul_le_one hx hw (hcoef x hx)
  have hπw : ∀ x : E, polar Q (π x) w = 0 := fun x ↦ by
    simp only [hπ]
    rw [polar_sub_left, polar_smul_left, polar_self, smul_eq_mul, nsmul_eq_mul, hd]
    field_simp
    ring
  have hπadd : ∀ x y : E, π (x + y) = π x + π y := fun x y ↦ by
    simp only [hπ]
    rw [polar_add_left, add_div, add_smul]
    abel
  have hdecomp : ∀ y : E, y = π y + (polar Q y w / d) • w := fun y ↦ by
    simp only [hπ, sub_add_cancel]
  have hpolπ : ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖polar Q (π x) y‖ < 1 := by
    intro x y hx hy
    have h1 : polar Q (π x) y = polar Q (π x) (π y) := by
      conv_lhs => rw [hdecomp y]
      rw [polar_add_right, polar_smul_right, hπw, smul_zero, add_zero]
    have h2 : polar Q (π x) (π y) = Q (π (x + y)) - Q (π x) - Q (π y) := by
      rw [hπadd]; rfl
    rw [h1, h2]
    exact padic_norm_sub_lt_one (padic_norm_sub_lt_one
      (hsmall _ (hπL _ (padicVector_norm_add_le_one hx hy)) (hπw _))
      (hsmall _ (hπL x hx) (hπw x))) (hsmall _ (hπL y hy) (hπw y))
  have hπsmall : ∀ x : E, ‖x‖ ≤ 1 → ‖π x‖ < 1 := fun x hx ↦
    hU (π x) (hπL x hx) (fun y hy ↦ hpolπ x y hx hy)
  -- two standard basis vectors are congruent to multiples of `w`: impossible
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hsingle : ∀ i : Fin N, ‖(Pi.single i (1 : ℚ_[p]) : E)‖ ≤ 1 := fun i ↦ by
    rw [padicVector_norm_le_one_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hcoord : ∀ i j : Fin N, ‖(Pi.single i (1 : ℚ_[p]) : E) j -
      polar Q (Pi.single i 1) w / d * w j‖ < 1 := fun i j ↦ by
    have h := (norm_le_pi_norm (π (Pi.single i 1)) j).trans_lt (hπsmall _ (hsingle i))
    simpa [hπ] using h
  have hwcoord : ∀ j, ‖w j‖ ≤ 1 := padicVector_norm_le_one_iff.mp hw
  set c₀ := polar Q (Pi.single i₀ (1 : ℚ_[p])) w / d
  set c₁ := polar Q (Pi.single i₁ (1 : ℚ_[p])) w / d
  have hc₀ : ‖c₀‖ ≤ 1 := hcoef _ (hsingle i₀)
  have h00 := hcoord i₀ i₀
  rw [Pi.single_eq_same] at h00
  have h00' : ‖c₀ * w i₀‖ = 1 :=
    (Padic.norm_eq_of_norm_sub_lt_left (by rwa [norm_one])).symm.trans norm_one
  have hw₀ : ‖w i₀‖ = 1 := by
    refine le_antisymm (hwcoord i₀) ?_
    calc (1 : ℝ) = ‖c₀‖ * ‖w i₀‖ := by rw [← norm_mul, h00']
      _ ≤ 1 * ‖w i₀‖ := mul_le_mul_of_nonneg_right hc₀ (norm_nonneg _)
      _ = ‖w i₀‖ := one_mul _
  have h10 := hcoord i₁ i₀
  rw [Pi.single_eq_of_ne hne.symm, zero_sub, norm_neg, norm_mul, hw₀, mul_one] at h10
  have h11 := hcoord i₁ i₁
  rw [Pi.single_eq_same] at h11
  have h11' : ‖c₁ * w i₁‖ = 1 :=
    (Padic.norm_eq_of_norm_sub_lt_left (by rwa [norm_one])).symm.trans norm_one
  have : ‖c₁ * w i₁‖ < 1 := by
    rw [norm_mul]
    calc ‖c₁‖ * ‖w i₁‖ ≤ ‖c₁‖ * 1 := mul_le_mul_of_nonneg_left (hwcoord i₁) (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  exact absurd h11' this.ne

/-- Integral-orbit transitivity (abstract core): lattice vectors of the same
unit value are related by a lattice-preserving isometry of determinant one. -/
theorem exists_padicIntegral_isometry_det_one_apply_eq (hp : p ≠ 2) (hN : 2 ≤ N)
    (hB : IsPadicIntegralPolar (p := p) Q) (hU : IsPadicUnimodularPolar (p := p) Q) {v w : E}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hvw : Q v = Q w) (hQw : ‖(Q w : ℚ_[p])‖ = 1) :
    ∃ g : E ≃ₗ[ℚ_[p]] E, (∀ x, Q (g x) = Q x) ∧ LinearMap.det (g : E →ₗ[ℚ_[p]] E) = 1 ∧
      (∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) ∧ (∀ x, ‖x‖ ≤ 1 → ‖g.symm x‖ ≤ 1) ∧ g v = w := by
  have hne0 : ∀ z : ℚ_[p], ‖z‖ = 1 → z ≠ 0 := fun z hz h ↦ by
    rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hQw0 := hne0 _ hQw
  have hsum := quadraticForm_sub_add_sum_of_eq Q w v hvw
  have hfour : ‖(4 : ℚ_[p])‖ = 1 := by
    rw [show (4 : ℚ_[p]) = 2 * 2 by norm_num, norm_mul, padic_norm_two_of_ne_two hp, one_mul]
  have hsum1 : ‖Q (v - w) + Q (v + w)‖ = 1 := by rw [hsum, norm_mul, hfour, hQw, one_mul]
  have hminus_le := padicIntegralPolar_norm_apply_le_one Q hp hB (padicVector_norm_sub_le_one hv hw)
  have hplus_le := padicIntegralPolar_norm_apply_le_one Q hp hB (padicVector_norm_add_le_one hv hw)
  by_cases hplus : ‖Q (v + w)‖ = 1
  · -- `g = τ_w ∘ τ_(v+w)`
    have hQp0 := hne0 _ hplus
    obtain ⟨h1, h2, h3, h4⟩ := quadraticReflection_trans_props Q hB hw hQw0 hQw
      (padicVector_norm_add_le_one hv hw) hQp0 hplus
    refine ⟨_, h1, h2, h3, h4, ?_⟩
    change quadraticReflectionOfNeZero Q w hQw0
      (quadraticReflectionOfNeZero Q (v + w) hQp0 v) = w
    have hpol : polar Q (v + w) v = Q (v + w) := by
      rw [polar_add_left, polar_self, nsmul_eq_mul, QuadraticMap.map_add Q, polar_comm Q w v]
      rw [hvw]; push_cast; ring
    rw [quadraticReflectionOfNeZero_apply_of_polar_eq Q hQp0 hpol, sub_add_cancel_left,
      quadraticReflectionOfNeZero_apply, polar_neg_right, polar_self, nsmul_eq_mul]
    have : (Q w)⁻¹ * -((2 : ℕ) * Q w) = -2 := by field_simp; push_cast; ring
    rw [this]
    module
  · -- `g = τ_u ∘ τ_(v-w)` with `u` a unit-norm vector orthogonal to `w`
    have hminus : ‖Q (v - w)‖ = 1 := by
      by_contra hm
      have hlt := padic_norm_add_lt_one (lt_of_le_of_ne hminus_le hm) (lt_of_le_of_ne hplus_le hplus)
      rw [hsum1] at hlt
      exact lt_irrefl _ hlt
    have hQm0 := hne0 _ hminus
    obtain ⟨u, hu, hQu, huw⟩ := exists_padicUnit_polar_orthogonal Q hp hN hB hU hw hQw
    have hQu0 := hne0 _ hQu
    obtain ⟨h1, h2, h3, h4⟩ := quadraticReflection_trans_props Q hB hu hQu0 hQu
      (padicVector_norm_sub_le_one hv hw) hQm0 hminus
    refine ⟨_, h1, h2, h3, h4, ?_⟩
    change quadraticReflectionOfNeZero Q u hQu0
      (quadraticReflectionOfNeZero Q (v - w) hQm0 v) = w
    have hpol : polar Q (v - w) v = Q (v - w) := by
      rw [polar_sub_left, polar_self, nsmul_eq_mul, sub_eq_add_neg v w, QuadraticMap.map_add Q,
        QuadraticMap.map_neg, polar_neg_right, polar_comm Q w v, hvw]
      push_cast; ring
    rw [quadraticReflectionOfNeZero_apply_of_polar_eq Q hQm0 hpol, sub_sub_cancel,
      quadraticReflectionOfNeZero_apply, huw, mul_zero, zero_smul, sub_zero]

end QuadraticMap
