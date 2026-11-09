import SMSFormula.RationalLatticeGaussColumnBoundary

/-!
# The Gauss-sum columns and their S,T transport in rank four

For a rank-four lattice with discriminant group `A`, define the columns `F(c,d) ∈ ℂ[A]`:
* `F(0,d) = e₀`;
* for `c ≠ 0`, `F(c,d)_a = -c² m⁻⁴ Σ_{r mod m} w_{c,d,a}(r) / √det(S⁻¹)`, with the column level `m` and the column
  weight `w` of `RationalLatticeGaussColumnBoundary`.
Then the rational boundary limit reads `t² θ_a(-d/c + it) → -F(c,d)_a / c²`.

Every transport identity is deduced from the theta laws by uniqueness of limits:
* `gaussColumn_sub_self`: `F(c, d - c) = T₀ F(c,d)` (T-law);
* `gaussColumn_neg_neg`: `F(-c,-d) = F(c,d)`;
* `gaussColumn_neg_inv`: `F(-d, c) = U F(c,d)` for `c, d ≠ 0` (S-law; the real displacement `O(t²)` of `-1/z` is the
  Abel lemma's error term, with `ε/σ = (c/d) t → 0`);
* `gaussColumn_one_zero`: `F(1,0) = U e₀`, via the S-law and `θ(iy) → e₀`;
* `gaussU_gaussU_single_zero`: `U² e₀ = e₀`, via the S-law applied twice and `θ(iy) → e₀`.
Here `(U v)_{a₀} = -√det(S⁻¹) Σ_a e(-B(a₀,a)) v_a` and `(T₀ v)_a = e(q(a)) v_a` are the explicit finite operators.
The cardinality of `A` is never computed.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm

namespace PositiveDefiniteIntegralLattice

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## The operators -/

/-- `κ = √det(S⁻¹)`. -/
def polarKappa : ℝ := Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det

theorem polarKappa_pos : 0 < L.polarKappa :=
  Real.sqrt_pos.2 L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv.det_pos

/-- The S-operator `(U v)_{a₀} = -κ Σ_a e(-B(a₀,a)) v_a`. -/
def gaussU (v : L.PolarDiscriminantGroup → ℂ) (a₀ : L.PolarDiscriminantGroup) : ℂ :=
  -(L.polarKappa : ℂ) * ∑ a, L.polarDiscPairingChar a₀ a * v a

/-- The T-operator `(T₀ v)_a = e(q(a)) v_a`. -/
def gaussT (v : L.PolarDiscriminantGroup → ℂ) (a : L.PolarDiscriminantGroup) : ℂ :=
  L.polarDiscNormChar a * v a

/-- The origin vector `e₀`. -/
def gaussE0 : L.PolarDiscriminantGroup → ℂ := Pi.single 0 1

/-! ## The columns -/

/-- The Gauss-sum column `F(c,d)`. -/
def gaussColumn (c d : ℤ) (a : L.PolarDiscriminantGroup) : ℂ :=
  if hc : c = 0 then L.gaussE0 a else
    haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩;
    -((c : ℂ) ^ 2) * ((((L.gaussColumnLevel c : ℝ) ^ 4 : ℂ)⁻¹) * ∑ r, L.gaussColumnWeight c d a r) /
      (L.polarKappa : ℂ)

theorem gaussColumn_zero (d : ℤ) : L.gaussColumn 0 d = L.gaussE0 := by
  funext a
  simp [gaussColumn]

/-- `√(σ⁴ det S⁻¹) = σ² κ` for `σ ≥ 0`. -/
theorem sqrt_pow_four_mul_det (σ : ℝ) :
    Real.sqrt (σ ^ 4 * (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det) = σ ^ 2 * L.polarKappa := by
  rw [Real.sqrt_mul (by positivity), show σ ^ 4 = (σ ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity), polarKappa]

/-- The boundary limit in column form: `σ² θ_a(-d/c - ε + iσ) → -F(c,d)_a / c²`. -/
theorem tendsto_sq_mul_polarClassTheta_boundary {c : ℤ} (hc : c ≠ 0) (d : ℤ)
    (a : L.PolarDiscriminantGroup) {κ : Type*} {l : Filter κ} (σ ε : κ → ℝ)
    (hσ : Tendsto σ l (𝓝[>] 0)) (hε : Tendsto (fun x ↦ ε x / σ x) l (𝓝 0)) :
    Tendsto (fun x ↦ ((σ x : ℂ) ^ 2) *
        L.polarClassTheta (((-(d : ℚ) / c : ℚ) : ℂ) - ε x + σ x * I) a) l
      (𝓝 (-L.gaussColumn c d a / (c : ℂ) ^ 2)) := by
  haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  have h := (L.tendsto_polarClassTheta_boundary hc d a σ ε hσ hε).div_const (L.polarKappa : ℂ)
  have hk : (L.polarKappa : ℂ) ≠ 0 := by exact_mod_cast L.polarKappa_pos.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hc2 : ((c : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 hc'
  have hval : ((((L.gaussColumnLevel c : ℝ) ^ 4 : ℂ)⁻¹) * ∑ r, L.gaussColumnWeight c d a r) /
      (L.polarKappa : ℂ) = -L.gaussColumn c d a / (c : ℂ) ^ 2 := by
    rw [gaussColumn, dif_neg hc]
    field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards with x
  rw [L.sqrt_pow_four_mul_det (σ x)]
  push_cast
  field_simp

/-- The limit along `t → 0⁺` at the point `-d/c + it`. -/
theorem tendsto_sq_mul_polarClassTheta_rational {c : ℤ} (hc : c ≠ 0) (d : ℤ)
    (a : L.PolarDiscriminantGroup) :
    Tendsto (fun t : ℝ ↦ ((t : ℂ) ^ 2) * L.polarClassTheta (((-(d : ℚ) / c : ℚ) : ℂ) + t * I) a)
      (𝓝[>] 0) (𝓝 (-L.gaussColumn c d a / (c : ℂ) ^ 2)) := by
  have h := L.tendsto_sq_mul_polarClassTheta_boundary hc d a (fun t ↦ t) (fun _ ↦ 0)
    (tendsto_id.mono_left le_rfl) (by simp)
  simpa using h

/-! ## T transport and evenness -/

/-- `F(c, d - c) = T₀ F(c, d)`. -/
theorem gaussColumn_sub_self (c d : ℤ) : L.gaussColumn c (d - c) = L.gaussT (L.gaussColumn c d) := by
  funext a
  by_cases hc : c = 0
  · subst hc
    rw [sub_zero, gaussColumn_zero, gaussT, gaussE0]
    by_cases ha : a = 0
    · subst ha
      have h0 : L.polarDiscNormChar (0 : L.PolarDiscriminantGroup) = 1 := by
        rw [← QuotientAddGroup.mk_zero, polarDiscNormChar_coe]
        simp [polarDualNorm]
      simp [h0]
    · simp [ha]
  have h1 := L.tendsto_sq_mul_polarClassTheta_rational hc (d - c) a
  have h2 := (L.tendsto_sq_mul_polarClassTheta_rational hc d a).const_mul (L.polarDiscNormChar a)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have heq : ∀ t : ℝ, ((t : ℂ) ^ 2) * L.polarClassTheta (((-((d - c : ℤ) : ℚ) / c : ℚ) : ℂ) + t * I) a =
      L.polarDiscNormChar a * (((t : ℂ) ^ 2) * L.polarClassTheta (((-(d : ℚ) / c : ℚ) : ℂ) + t * I) a) := by
    intro t
    have hpt : (((-((d - c : ℤ) : ℚ) / c : ℚ) : ℂ) + t * I) =
        ((((-(d : ℚ) / c : ℚ) : ℂ) + t * I) + 1) := by
      push_cast
      field_simp
      ring
    rw [hpt, L.polarClassTheta_add_one]
    ring
  simp_rw [heq] at h1
  have := tendsto_nhds_unique h1 h2
  have hc2 : ((c : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 hc'
  rw [gaussT]
  rw [neg_div, neg_div, mul_neg, neg_inj, ← mul_div_assoc, div_left_inj' hc2] at this
  exact this

/-- `F(-c, -d) = F(c, d)`. -/
theorem gaussColumn_neg_neg (c d : ℤ) : L.gaussColumn (-c) (-d) = L.gaussColumn c d := by
  funext a
  by_cases hc : c = 0
  · subst hc
    rw [neg_zero, gaussColumn_zero, gaussColumn_zero]
  have hnc : -c ≠ 0 := neg_ne_zero.2 hc
  have h1 := L.tendsto_sq_mul_polarClassTheta_rational hnc (-d) a
  have h2 := L.tendsto_sq_mul_polarClassTheta_rational hc d a
  have hpt : (((-((-d : ℤ) : ℚ) / ((-c : ℤ) : ℚ) : ℚ) : ℂ)) = (((-(d : ℚ) / c : ℚ) : ℂ)) := by
    push_cast
    rw [neg_div_neg_eq]
  simp_rw [hpt] at h1
  have := tendsto_nhds_unique h1 h2
  have hc2 : ((c : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hc)
  push_cast at this
  rw [neg_sq, neg_div, neg_div, neg_inj, div_left_inj' hc2] at this
  exact this

/-! ## S transport -/

/-- The inverse boundary point: `-(-r + it)⁻¹ = 1/r - ε(t) + i σ(t)`. -/
theorem neg_inv_boundary_point {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    -((-(r : ℂ)) + t * I)⁻¹ =
      ((1 / r : ℝ) : ℂ) - ((t ^ 2 / (r * (r ^ 2 + t ^ 2)) : ℝ) : ℂ) + ((t / (r ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
  have hpos : 0 < r ^ 2 + t ^ 2 := by positivity
  set w : ℂ := (-(r : ℂ)) + t * I with hw
  have hwre : w.re = -r := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hN : normSq w = r ^ 2 + t ^ 2 := by rw [normSq_apply, hwre, hwim]; ring
  apply Complex.ext
  · simp only [neg_re, inv_re, hwre, hN, add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, mul_one, add_zero]
    field_simp
    ring
  · simp only [neg_im, inv_im, hwim, hN, add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, sub_zero, mul_one, add_zero, zero_add]
    field_simp

theorem tendsto_boundary_scale {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun t : ℝ ↦ t / (r ^ 2 + t ^ 2)) (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : ContinuousAt (fun t : ℝ ↦ t / (r ^ 2 + t ^ 2)) 0 := by
    have : r ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact div_pos ht (by positivity)

theorem tendsto_boundary_error_div_scale {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun t : ℝ ↦ (t ^ 2 / (r * (r ^ 2 + t ^ 2))) / (t / (r ^ 2 + t ^ 2))) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ ↦ t / r) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_id.div_const r).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hpos : 0 < r ^ 2 + t ^ 2 := by positivity
  field_simp

/-- The S transport: `F(-d, c) = U F(c, d)` for `c, d ≠ 0`. -/
theorem gaussColumn_neg_inv {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) :
    L.gaussColumn (-d) c = L.gaussU (L.gaussColumn c d) := by
  funext a₀
  set r : ℝ := (d : ℝ) / c with hrdef
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hr : r ≠ 0 := div_ne_zero hd' hc'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hnd : -d ≠ 0 := neg_ne_zero.2 hd
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  set σ : ℝ → ℝ := fun t ↦ t / (r ^ 2 + t ^ 2) with hσdef
  set ε : ℝ → ℝ := fun t ↦ t ^ 2 / (r * (r ^ 2 + t ^ 2)) with hεdef
  -- the two boundary points
  have hpt0 : (((-(d : ℚ) / c : ℚ) : ℂ)) = -(r : ℂ) := by
    rw [hrdef]; push_cast; ring
  have hpt1 : (((-((c : ℤ) : ℚ) / ((-d : ℤ) : ℚ) : ℚ) : ℂ)) = ((1 / r : ℝ) : ℂ) := by
    rw [hrdef]; push_cast; field_simp
  -- left side: the boundary limit at `c/d` for the pair `(-d, c)`
  have hL := L.tendsto_sq_mul_polarClassTheta_boundary hnd c a₀ σ ε
    (tendsto_boundary_scale hr) (tendsto_boundary_error_div_scale hr)
  -- right side: the S-law and the boundary limit at `-d/c`
  have hR0 : ∀ a, Tendsto (fun t : ℝ ↦ ((t : ℂ) ^ 2) * L.polarClassTheta (-(r : ℂ) + t * I) a)
      (𝓝[>] 0) (𝓝 (-L.gaussColumn c d a / (c : ℂ) ^ 2)) := by
    intro a
    have h := L.tendsto_sq_mul_polarClassTheta_rational hc d a
    rwa [hpt0] at h
  have hg : Tendsto (fun t : ℝ ↦ (-(r : ℂ) + t * I) ^ 2 / ((r : ℂ) ^ 2 + (t : ℂ) ^ 2) ^ 2)
      (𝓝[>] 0) (𝓝 ((c : ℂ) ^ 2 / (d : ℂ) ^ 2)) := by
    have hne : ((r : ℂ) ^ 2 + ((0 : ℝ) : ℂ) ^ 2) ^ 2 ≠ 0 := by
      simp only [ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      exact pow_ne_zero 2 (pow_ne_zero 2 hrC)
    have hcont : ContinuousAt (fun t : ℝ ↦ (-(r : ℂ) + t * I) ^ 2 / ((r : ℂ) ^ 2 + (t : ℂ) ^ 2) ^ 2) 0 := by
      fun_prop (disch := assumption)
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    convert h using 2
    rw [hrdef]
    push_cast
    field_simp
    ring
  have hR : Tendsto (fun t : ℝ ↦ -(L.polarKappa : ℂ) * ∑ a, L.polarDiscPairingChar a₀ a *
        (((-(r : ℂ) + t * I) ^ 2 / ((r : ℂ) ^ 2 + (t : ℂ) ^ 2) ^ 2) *
          (((t : ℂ) ^ 2) * L.polarClassTheta (-(r : ℂ) + t * I) a)))
      (𝓝[>] 0) (𝓝 (-(L.polarKappa : ℂ) * ∑ a, L.polarDiscPairingChar a₀ a *
        (((c : ℂ) ^ 2 / (d : ℂ) ^ 2) * (-L.gaussColumn c d a / (c : ℂ) ^ 2)))) :=
    (tendsto_finset_sum _ fun a _ ↦ ((hg.mul (hR0 a)).const_mul _)).const_mul _
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((σ t : ℂ) ^ 2) *
      L.polarClassTheta ((((-((c : ℤ) : ℚ) / ((-d : ℤ) : ℚ) : ℚ) : ℂ)) - ε t + σ t * I) a₀ =
      -(L.polarKappa : ℂ) * ∑ a, L.polarDiscPairingChar a₀ a *
        (((-(r : ℂ) + t * I) ^ 2 / ((r : ℂ) ^ 2 + (t : ℂ) ^ 2) ^ 2) *
          (((t : ℂ) ^ 2) * L.polarClassTheta (-(r : ℂ) + t * I) a)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hzim : 0 < (-(r : ℂ) + t * I).im := by simpa using ht
    rw [hpt1, ← neg_inv_boundary_point hr t, L.polarClassTheta_neg_inv hzim, cpow_half_pow_four]
    have hI : (-I * (-(r : ℂ) + t * I)) ^ 2 = -(-(r : ℂ) + t * I) ^ 2 := by
      linear_combination (-(r : ℂ) + t * I) ^ 2 * I_sq
    rw [hI]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hRne : ((r : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
      have : (r ^ 2 + t ^ 2 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    simp only [hσdef, polarKappa]
    push_cast
    field_simp
  have hlim := tendsto_nhds_unique (hL.congr' heq) hR
  -- solve for the column
  have hd2 : ((d : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hdC
  have hc2 : ((c : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hcC
  set S := ∑ a, L.polarDiscPairingChar a₀ a * L.gaussColumn c d a with hSdef
  have hsum : ∑ a, L.polarDiscPairingChar a₀ a *
      ((c : ℂ) ^ 2 / (d : ℂ) ^ 2 * (-L.gaussColumn c d a / (c : ℂ) ^ 2)) = -S / (d : ℂ) ^ 2 := by
    rw [hSdef, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    field_simp
  rw [hsum] at hlim
  push_cast at hlim
  rw [neg_sq, show -(L.polarKappa : ℂ) * (-S / (d : ℂ) ^ 2) = ((L.polarKappa : ℂ) * S) / (d : ℂ) ^ 2 by
    ring, neg_div, ← neg_div] at hlim
  rw [div_left_inj' hd2] at hlim
  rw [gaussU, ← hSdef]
  linear_combination -hlim

/-! ## The cusp at infinity, `F(1,0) = U e₀` and `U² e₀ = e₀` -/

/-- `θ_b(iy) → [b = 0]` as `y → ∞`. -/
theorem tendsto_polarClassTheta_atTop (b : L.PolarDiscriminantGroup) :
    Tendsto (fun y : ℝ ↦ L.polarClassTheta ((y : ℂ) * I) b) atTop (𝓝 (L.gaussE0 b)) := by
  have hcomb : ∀ τ, L.polarThetaCombination (Pi.single b 1) τ = L.polarClassTheta τ b := by
    intro τ
    unfold polarThetaCombination
    rw [Finset.sum_eq_single b (fun a _ hab ↦ by simp [hab]) (by simp)]
    simp
  have h0 : (Pi.single b (1 : ℂ) : L.PolarDiscriminantGroup → ℂ) 0 = L.gaussE0 b := by
    simp only [gaussE0, Pi.single_apply]
    by_cases hb : b = 0
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Y, hY⟩ := L.polarThetaCombination_tendsto (Pi.single b 1) (ε / 2) (by positivity)
  refine ⟨max Y 0 + 1, fun y hy ↦ ?_⟩
  have hy0 : 0 < y := by linarith [le_max_right Y 0]
  have hmem : (y : ℂ) * I ∈ upperHalfSet := by simp [upperHalfSet, hy0]
  have h := hY _ hmem (by simp; linarith [le_max_left Y 0])
  rw [hcomb, h0] at h
  rw [dist_eq_norm]
  linarith

theorem polarDiscPairingChar_zero_right (a : L.PolarDiscriminantGroup) :
    L.polarDiscPairingChar a 0 = 1 := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [← QuotientAddGroup.mk_zero, polarDiscPairingChar_coe]
  simp [polarDualPairing]

theorem gaussU_gaussE0 : L.gaussU L.gaussE0 = fun _ ↦ -(L.polarKappa : ℂ) := by
  funext a
  unfold gaussU gaussE0
  rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [hb]) (by simp),
    Pi.single_eq_same, mul_one, polarDiscPairingChar_zero_right, mul_one]

/-- `F(1, 0) = U e₀`. -/
theorem gaussColumn_one_zero : L.gaussColumn 1 0 = L.gaussU L.gaussE0 := by
  funext a
  rw [L.gaussU_gaussE0]
  have h1 := L.tendsto_sq_mul_polarClassTheta_rational (c := 1) one_ne_zero 0 a
  have h2 : Tendsto (fun t : ℝ ↦ ((t : ℂ) ^ 2) *
      L.polarClassTheta (((-((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) : ℚ) : ℂ) + t * I) a) (𝓝[>] 0)
      (𝓝 ((L.polarKappa : ℂ) * ∑ b, L.polarDiscPairingChar a b * L.gaussE0 b)) := by
    have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    have hθ : ∀ b, Tendsto (fun t : ℝ ↦ L.polarClassTheta ((t⁻¹ : ℝ) * I) b) (𝓝[>] 0)
        (𝓝 (L.gaussE0 b)) := fun b ↦ (L.tendsto_polarClassTheta_atTop b).comp hinv
    have hlim := (tendsto_finset_sum (Finset.univ : Finset L.PolarDiscriminantGroup)
      fun b _ ↦ (hθ b).const_mul (L.polarDiscPairingChar a b)).const_mul (L.polarKappa : ℂ)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have htim : 0 < (((t⁻¹ : ℝ) : ℂ) * I).im := by simpa using ht
    have hpt : (((-((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) : ℚ) : ℂ) + t * I) = -((((t⁻¹ : ℝ) : ℂ) * I))⁻¹ := by
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [hpt, L.polarClassTheta_neg_inv htim, cpow_half_pow_four]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hsq : (-I * (((t⁻¹ : ℝ) : ℂ) * I)) ^ 2 = ((t : ℂ) ^ 2)⁻¹ := by
      rw [show (-I * (((t⁻¹ : ℝ) : ℂ) * I)) ^ 2 = (((t⁻¹ : ℝ) : ℂ)) ^ 2 * (I ^ 2) ^ 2 by ring, I_sq]
      push_cast
      ring
    rw [hsq]
    simp only [polarKappa]
    field_simp
  have := tendsto_nhds_unique h1 h2
  rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [gaussE0, hb]) (by simp)] at this
  simp only [gaussE0, Pi.single_eq_same, mul_one, polarDiscPairingChar_zero_right] at this
  push_cast at this
  linear_combination -this

/-- The S-law applied twice: `θ(τ) = U² θ(τ)`. -/
theorem polarClassTheta_eq_gaussU_gaussU {τ : ℂ} (hτ : τ ∈ upperHalfSet) :
    (fun b ↦ L.polarClassTheta τ b) = L.gaussU (L.gaussU fun b ↦ L.polarClassTheta τ b) := by
  funext a
  have hτ0 : τ ≠ 0 := ne_zero_of_mem hτ
  have h' : -τ⁻¹ ∈ upperHalfSet := neg_inv_mem hτ
  have hback : -(-τ⁻¹)⁻¹ = τ := by rw [inv_neg, inv_inv, neg_neg]
  have h1 := L.polarClassTheta_neg_inv (τ := -τ⁻¹) h' a
  rw [hback, cpow_half_pow_four] at h1
  rw [h1]
  unfold gaussU
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [L.polarClassTheta_neg_inv hτ b, cpow_half_pow_four]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hI : (-I * -τ⁻¹) ^ 2 * (-I * τ) ^ 2 = 1 := by
    field_simp
    linear_combination (I ^ 2 - 1) * I_sq
  simp only [polarKappa]
  linear_combination (Real.sqrt (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det : ℂ) ^ 2 *
    L.polarDiscPairingChar a b * L.polarDiscPairingChar b c * L.polarClassTheta τ c * hI

/-- `U² e₀ = e₀`. -/
theorem gaussU_gaussU_gaussE0 : L.gaussU (L.gaussU L.gaussE0) = L.gaussE0 := by
  funext a
  have hθ : ∀ b, Tendsto (fun y : ℝ ↦ L.polarClassTheta ((y : ℂ) * I) b) atTop (𝓝 (L.gaussE0 b)) :=
    L.tendsto_polarClassTheta_atTop
  have hU : ∀ v : L.PolarDiscriminantGroup → ℂ, ∀ a, L.gaussU (L.gaussU v) a =
      (L.polarKappa : ℂ) ^ 2 * ∑ b, L.polarDiscPairingChar a b * ∑ c, L.polarDiscPairingChar b c * v c := by
    intro v a
    unfold gaussU
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    ring
  have hlim : Tendsto (fun y : ℝ ↦ L.gaussU (L.gaussU fun b ↦ L.polarClassTheta ((y : ℂ) * I) b) a)
      atTop (𝓝 (L.gaussU (L.gaussU L.gaussE0) a)) := by
    simp only [hU]
    exact (tendsto_finset_sum _ fun b _ ↦ ((tendsto_finset_sum _ fun c _ ↦
      (hθ c).const_mul _)).const_mul _).const_mul _
  have heq : ∀ᶠ y : ℝ in atTop, L.gaussU (L.gaussU fun b ↦ L.polarClassTheta ((y : ℂ) * I) b) a =
      L.polarClassTheta ((y : ℂ) * I) a := by
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hmem : (y : ℂ) * I ∈ upperHalfSet := by simp [upperHalfSet, hy]
    exact (congrFun (L.polarClassTheta_eq_gaussU_gaussU hmem) a).symm
  exact tendsto_nhds_unique (hlim.congr' heq) (hθ a)

/-! ## `J`-evenness -/

/-- `θ_{-a} = θ_a`. -/
theorem polarClassTheta_neg (τ : ℂ) (a : L.PolarDiscriminantGroup) :
    L.polarClassTheta τ (-a) = L.polarClassTheta τ a := by
  unfold polarClassTheta
  let e : {u : Fin 4 → ℤ // (u : L.PolarDiscriminantGroup) = a} ≃
      {u : Fin 4 → ℤ // (u : L.PolarDiscriminantGroup) = -a} :=
    { toFun := fun u ↦ ⟨-u.1, by rw [QuotientAddGroup.mk_neg, u.2]⟩
      invFun := fun u ↦ ⟨-u.1, by rw [QuotientAddGroup.mk_neg, u.2, neg_neg]⟩
      left_inv := fun u ↦ by simp
      right_inv := fun u ↦ by simp }
  rw [← e.tsum_eq]
  refine tsum_congr fun u ↦ ?_
  change exp (2 * Real.pi * I * τ * (L.polarDualNorm (-u.1) : ℂ)) = _
  congr 3
  unfold polarDualNorm
  have hneg : integerVectorReal (-u.1) = -integerVectorReal u.1 := by
    funext i; simp [integerVectorReal]
  rw [hneg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/-- `F(c,d)_{-a} = F(c,d)_a`. -/
theorem gaussColumn_neg_class (c d : ℤ) (a : L.PolarDiscriminantGroup) :
    L.gaussColumn c d (-a) = L.gaussColumn c d a := by
  by_cases hc : c = 0
  · subst hc
    rw [gaussColumn_zero]
    simp only [gaussE0, Pi.single_apply, neg_eq_zero]
  have h1 := L.tendsto_sq_mul_polarClassTheta_rational hc d (-a)
  have h2 := L.tendsto_sq_mul_polarClassTheta_rational hc d a
  simp_rw [L.polarClassTheta_neg] at h1
  have := tendsto_nhds_unique h1 h2
  have hc2 : ((c : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hc)
  rw [neg_div, neg_div, neg_inj, div_left_inj' hc2] at this
  exact this

/-! ## S transport for every coprime pair -/

/-- The S transport for every coprime pair: `F(-d, c) = U F(c, d)`. -/
theorem gaussColumn_neg_inv_of_isCoprime {c d : ℤ} (h : IsCoprime c d) :
    L.gaussColumn (-d) c = L.gaussU (L.gaussColumn c d) := by
  by_cases hc : c = 0
  · subst hc
    have hd : IsUnit d := isCoprime_zero_left.1 h
    rw [gaussColumn_zero]
    have hm : L.gaussColumn (-1) 0 = L.gaussColumn 1 0 := by
      have := L.gaussColumn_neg_neg 1 0
      rwa [neg_zero] at this
    rcases Int.isUnit_iff.1 hd with rfl | rfl
    · rw [hm, L.gaussColumn_one_zero]
    · rw [neg_neg, L.gaussColumn_one_zero]
  by_cases hd : d = 0
  · subst hd
    have hcu : IsUnit c := isCoprime_zero_right.1 h
    rw [neg_zero, gaussColumn_zero]
    have hm : L.gaussColumn (-1) 0 = L.gaussColumn 1 0 := by
      have := L.gaussColumn_neg_neg 1 0
      rwa [neg_zero] at this
    rcases Int.isUnit_iff.1 hcu with rfl | rfl
    · rw [L.gaussColumn_one_zero, L.gaussU_gaussU_gaussE0]
    · rw [hm, L.gaussColumn_one_zero, L.gaussU_gaussU_gaussE0]
  exact L.gaussColumn_neg_inv hc hd

end PositiveDefiniteIntegralLattice
