import SMSFormula.RationalLatticeEisensteinRows
import SMSFormula.RationalLatticeGaussColumnExplicit
import SMSFormula.RationalLatticeRowKernel

/-!
# The Fourier expansion of a regularized row

For `c ≥ 1`, `0 < s ≤ 1`, `z = x + iy` and a class `[u]` (`r = q(ν) = polarDualNorm u`):

`Row_c(s, z)_{[u]} = y^s c^{-2s} Σ_{k ∈ ℤ} ĥ_{s,y}(k + r) e((k + r) x) B_{c,[u]}(k + r)`   (`regEisRow_apply_fourier`),

where `B_{c,[u]}` is the row coefficient (`gaussRowCoefficient`).  Steps:
* `(Im γz)^s (cz+d)⁻² = y^s (c²)^{-s} c⁻² h_{s,y}(x + d/c)` (`eisRegularizer_mul_inv_sq`);
* `d = q c + a` with `0 ≤ a < c` (Mathlib `Int.divModEquiv`), `(c, qc + a) = 1 ⟺ (c, a) = 1`, and
  `F(c, qc + a)_{[u]} = e(-q r) F(c, a)_{[u]}` from the explicit column (`gaussColumn_add_mul_apply`);
* the twisted Poisson identity for `h_{s,y}` (`tsum_twisted_rowKernel`);
* `e((k + r)(x + a/c)) = e((k + r) x) e((k + r) a/c)`, and the finite `a`-sum is `c² B_{c,[u]}(k + r)`.
All sums are absolute.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm SMSFormula.RowKernel Finset
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## The row term -/

/-- `(Im γz)^s (cz+d)⁻² = y^s (c²)^{-s} c⁻² h_{s,y}(x + d/c)` for `c ≥ 1`. -/
theorem eisRegularizer_mul_inv_sq (s : ℝ) {z : ℂ} (hz : z ∈ upperHalfSet) {c : ℕ} (hc : c ≠ 0)
    (d : ℤ) :
    ((eisRegularizer s z ![(c : ℤ), d] : ℝ) : ℂ) * ((((c : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)) ^ 2)⁻¹ =
      ((z.im ^ s * ((c : ℝ) ^ 2) ^ (-s) * ((c : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
        rowKernel s z.im (z.re + d / c) := by
  have hy : 0 < z.im := hz
  have hc' : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  set t : ℝ := z.re + d / c with ht
  have hw : ((c : ℤ) : ℂ) * z + ((d : ℤ) : ℂ) = (c : ℂ) * ((t : ℂ) + z.im * I) := by
    rw [ht]
    push_cast
    conv_lhs => rw [← Complex.re_add_im z]
    field_simp
    ring
  have hρ : 0 < t ^ 2 + z.im ^ 2 := sq_add_sq_pos hy t
  have hN : normSq (((c : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)) = (c : ℝ) ^ 2 * (t ^ 2 + z.im ^ 2) := by
    rw [hw, normSq_mul, Complex.normSq_natCast, normSq_add_mul_I]
    ring
  unfold eisRegularizer rowKernel
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hN, hw, Real.div_rpow hy.le (by positivity), Real.mul_rpow (by positivity) hρ.le,
    Real.rpow_neg (by positivity), Real.rpow_neg hρ.le]
  have hw0 : (t : ℂ) + z.im * I ≠ 0 := add_mul_I_ne_zero hy t
  have hcs : ((c : ℝ) ^ 2) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by positivity) s).ne'
  have hρs : (t ^ 2 + z.im ^ 2) ^ s ≠ 0 := (Real.rpow_pos_of_pos hρ s).ne'
  push_cast
  field_simp

/-- The row term at a primitive pair. -/
theorem regEisSummand_apply (s : ℝ) {z : ℂ} (hz : z ∈ upperHalfSet) {c : ℕ} (hc : c ≠ 0) (d : ℤ)
    (a : L.PolarDiscriminantGroup) :
    L.regEisSummand s z ![(c : ℤ), d] a =
      if IsCoprime (c : ℤ) d then
        ((z.im ^ s * ((c : ℝ) ^ 2) ^ (-s) * ((c : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
          rowKernel s z.im (z.re + d / c) * L.gaussColumn (c : ℤ) d a
      else 0 := by
  unfold regEisSummand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  split_ifs with h
  · rw [Pi.smul_apply, smul_eq_mul, eisRegularizer_mul_inv_sq s hz hc d]
  · rfl

/-! ## The column along a residue class -/

/-- `F(c, qc + a)_{[u]} = e(-q r) F(c, a)_{[u]}`, `r = q(ν)`. -/
theorem gaussColumn_add_mul_apply (c : ℕ) [NeZero c] (q a : ℤ) (u : Fin 4 → ℤ) :
    L.gaussColumn (c : ℤ) (q * c + a) (u : L.PolarDiscriminantGroup) =
      exp (-(2 * Real.pi * I * (L.polarDualNorm u : ℂ) * q)) *
        L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) := by
  rw [L.gaussColumn_explicit c, L.gaussColumn_explicit c]
  have hG : L.cosetGaussSum u c (q * c + a) = L.cosetGaussSum u c a := by
    unfold cosetGaussSum
    congr 1
    funext z
    congr 3
    push_cast
    rw [ZMod.natCast_self, mul_zero, zero_add]
  have hP : L.polarDualPhase (-((q * c + a : ℤ) : ℚ) / ((c : ℤ) : ℚ)) u =
      exp (-(2 * Real.pi * I * (L.polarDualNorm u : ℂ) * q)) *
        L.polarDualPhase (-((a : ℤ) : ℚ) / ((c : ℤ) : ℚ)) u := by
    unfold polarDualPhase
    rw [← Complex.exp_add]
    congr 1
    have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
    push_cast
    field_simp
    ring
  rw [hG, hP]
  ring

/-! ## Splitting the `d`-sum -/

/-- `Σ_{d ∈ ℤ} g(d) = Σ_{0 ≤ a < c} Σ_{q ∈ ℤ} g(qc + a)`. -/
theorem tsum_int_eq_sum_range_tsum (c : ℕ) [NeZero c] {g : ℤ → ℂ} (hg : Summable g) :
    ∑' d, g d = ∑ a ∈ range c, ∑' q : ℤ, g (q * c + a) := by
  set e : ℤ ≃ Fin c × ℤ := (Int.divModEquiv c).trans (Equiv.prodComm ℤ (Fin c)) with he
  have hsymm : ∀ p : Fin c × ℤ, e.symm p = p.2 * c + p.1 := fun p ↦ rfl
  have h1 : ∑' d, g d = ∑' p : Fin c × ℤ, g (e.symm p) := (e.symm.tsum_eq g).symm
  have hs : Summable fun p : Fin c × ℤ ↦ g (e.symm p) := hg.comp_injective e.symm.injective
  rw [h1, hs.tsum_prod, tsum_fintype]
  simp_rw [hsymm]
  exact Fin.sum_univ_eq_sum_range (fun a ↦ ∑' q : ℤ, g (q * c + a)) c

/-! ## The row in a coordinate -/

theorem summable_regEisSummand_row {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) (c : ℤ) :
    Summable fun d : ℤ ↦ L.regEisSummand s z ![c, d] :=
  (L.summable_regEisSummand_prod hs hz).prod_factor c

theorem regEisRow_apply_eq_sum {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) (c : ℕ) [NeZero c]
    (u : Fin 4 → ℤ) :
    L.regEisRow s z c (u : L.PolarDiscriminantGroup) =
      ((z.im ^ s * ((c : ℝ) ^ 2) ^ (-s) * ((c : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ a ∈ (range c).filter (fun a ↦ c.Coprime a),
          L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) *
            ∑' q : ℤ, exp (-(2 * Real.pi * I * (L.polarDualNorm u : ℝ) * q)) *
              rowKernel s z.im ((z.re + (a : ℝ) / c) + q) := by
  have hc : c ≠ 0 := NeZero.ne c
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hsum := L.summable_regEisSummand_row hs hz c
  have hsum' : Summable fun d : ℤ ↦ L.regEisSummand s z ![(c : ℤ), d] (u : L.PolarDiscriminantGroup) :=
    Pi.summable.1 hsum _
  unfold regEisRow
  rw [tsum_apply hsum, tsum_int_eq_sum_range_tsum c hsum', ← sum_filter_add_sum_filter_not (range c)
    (fun a ↦ c.Coprime a)]
  have hnot : ∀ a ∈ (range c).filter (fun a ↦ ¬ c.Coprime a),
      ∑' q : ℤ, L.regEisSummand s z ![(c : ℤ), q * c + a] (u : L.PolarDiscriminantGroup) = 0 := by
    intro a ha
    have hna := (mem_filter.1 ha).2
    have h0 : ∀ q : ℤ, L.regEisSummand s z ![(c : ℤ), q * c + a] (u : L.PolarDiscriminantGroup) = 0 := by
      intro q
      rw [L.regEisSummand_apply s hz hc, if_neg]
      rw [show (q * (c : ℤ) + (a : ℤ)) = (a : ℤ) + (c : ℤ) * q by ring,
        IsCoprime.add_mul_left_right_iff, Nat.isCoprime_iff_coprime]
      exact hna
    rw [tsum_congr h0, tsum_zero]
  rw [sum_congr rfl hnot, sum_const_zero, add_zero, mul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  have hca : c.Coprime a := (mem_filter.1 ha).2
  have hterm : ∀ q : ℤ, L.regEisSummand s z ![(c : ℤ), q * c + a] (u : L.PolarDiscriminantGroup) =
      ((z.im ^ s * ((c : ℝ) ^ 2) ^ (-s) * ((c : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
        (L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) *
          (exp (-(2 * Real.pi * I * (L.polarDualNorm u : ℝ) * q)) *
            rowKernel s z.im ((z.re + (a : ℝ) / c) + q))) := by
    intro q
    rw [L.regEisSummand_apply s hz hc, if_pos, L.gaussColumn_add_mul_apply c q a u]
    · have harg : z.re + ((q * c + a : ℤ) : ℝ) / c = (z.re + (a : ℝ) / c) + q := by
        push_cast
        field_simp
        ring
      rw [harg]
      push_cast
      ring
    · rw [show (q * (c : ℤ) + (a : ℤ)) = (a : ℤ) + (c : ℤ) * q by ring,
        IsCoprime.add_mul_left_right_iff, Nat.isCoprime_iff_coprime]
      exact hca
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_mul_left]

theorem norm_exp_two_pi_I_mul_real (θ : ℝ) : ‖exp (2 * Real.pi * I * (θ : ℂ))‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * I * (θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The row Fourier expansion (6.5):
`Row_c(s, z)_{[u]} = y^s c^{-2s} Σ_k ĥ_{s,y}(k + r) e((k + r) x) B_{c,[u]}(k + r)`, `r = q(ν)`. -/
theorem regEisRow_apply_fourier {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ upperHalfSet)
    (c : ℕ) [NeZero c] (u : Fin 4 → ℤ) :
    L.regEisRow s z c (u : L.PolarDiscriminantGroup) =
      ((z.im ^ s * ((c : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
        ∑' k : ℤ, 𝓕 (rowKernel s z.im) (k + L.polarDualNorm u) *
          exp (2 * Real.pi * I * ((k + L.polarDualNorm u : ℝ) : ℂ) * z.re) *
          L.gaussRowCoefficient c (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u) := by
  have hy : 0 < z.im := hz
  have hc : c ≠ 0 := NeZero.ne c
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [L.regEisRow_apply_eq_sum hs hz c u]
  simp_rw [tsum_twisted_rowKernel hs.le hs1 hy]
  set r : ℝ := L.polarDualNorm u with hr
  -- factor the phase `e((k + r)(x + a/c)) = e((k + r) x) e((k + r) a/c)`
  have hphase : ∀ (a : ℕ) (k : ℤ), exp (2 * Real.pi * I * ((k : ℂ) + (r : ℂ)) * (((z.re + (a : ℝ) / c : ℝ)) : ℂ)) =
      exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
        exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ)) := by
    intro a k
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  simp_rw [hphase]
  -- swap the finite `a`-sum with the `k`-series
  have hsumm : ∀ a ∈ (range c).filter (fun a ↦ c.Coprime a),
      Summable fun k : ℤ ↦ L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) *
        (𝓕 (rowKernel s z.im) (k + r) * (exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
          exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ)))) := by
    intro a _
    refine Summable.of_norm_bounded
      ((summable_norm_fourier_rowKernel_add hs.le hs1 hy r).mul_left
        ‖L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup)‖) fun k ↦ ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re)‖ = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * ((k + r : ℝ) : ℂ) * (z.re : ℂ) =
        2 * Real.pi * I * (((k + r) * z.re : ℝ) : ℂ) by push_cast; ring]
      exact norm_exp_two_pi_I_mul_real _
    have h2 : ‖exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ))‖ = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ) =
        2 * Real.pi * I * (((k + r) * a / c : ℝ) : ℂ) by push_cast; ring]
      exact norm_exp_two_pi_I_mul_real _
    rw [h1, h2, mul_one, mul_one]
  have hmul : ∀ a ∈ (range c).filter (fun a ↦ c.Coprime a),
      L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) *
        ∑' k : ℤ, 𝓕 (rowKernel s z.im) (k + r) *
          (exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
            exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ))) =
      ∑' k : ℤ, L.gaussColumn (c : ℤ) a (u : L.PolarDiscriminantGroup) *
        (𝓕 (rowKernel s z.im) (k + r) * (exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
          exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (a : ℂ) / (c : ℂ)))) := by
    intro a _
    rw [tsum_mul_left]
  rw [sum_congr rfl hmul, ← Summable.tsum_finsetSum hsumm, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  unfold gaussRowCoefficient
  have hfac : ∑ i ∈ (range c).filter (fun a ↦ c.Coprime a),
      L.gaussColumn (c : ℤ) i (u : L.PolarDiscriminantGroup) *
        (𝓕 (rowKernel s z.im) (k + r) * (exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
          exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (i : ℂ) / (c : ℂ)))) =
      𝓕 (rowKernel s z.im) (k + r) * exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
        ∑ i ∈ (range c).filter (fun a ↦ c.Coprime a),
          L.gaussColumn (c : ℤ) i (u : L.PolarDiscriminantGroup) *
            exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * (i : ℂ) / (c : ℂ)) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hfac]
  push_cast
  ring

end PositiveDefiniteIntegralLattice
