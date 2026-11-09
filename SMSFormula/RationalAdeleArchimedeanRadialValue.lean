import SMSFormula.RationalAdeleArchimedeanLocalIntegralVanishing

/-!
# The archimedean Gaussian integral is a one-dimensional integral in the value variable

The archimedean amplitude is a Gaussian integral over `R^n` in the nonnegative polar value
`P(x)`.  To evaluate it -- rather than only to bound it or to kill it -- that integral has
to be pushed forward to the value line.  This file does that with the existing polar square
root, the existing determinant change of variables, and mathlib's radial integration
formula; no new chart, section, measure or normalization is chosen.

The output is, for every continuous `g`,
```text
int_{R^n} g(P(x)) dx = detScale^{-1} * (n * vol(unit ball)) * int_{(0,inf)} r^{n-1} g(r^2) dr.
```

Negative scope: this is a change of variables, not an evaluation.  No value of any local
integral is computed here and no limit is taken.
-/

noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The polar square root carries the polar value to the plain sum of squares. -/
theorem polarRealValue_eq_sum_sq_mulVec (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) :
    L.polarRealValue x = ∑ i, (L.polarRealSqrtMatrix.mulVec x i) ^ 2 :=
  L.polarRealValue_eq_sum_sq x

/-- The existing determinant change of variables, in the value variable. -/
theorem integral_comp_polarRealValue_eq_sumSq (L : PositiveDefiniteIntegralLattice n) {g : ℝ → ℂ}
    (hg : Continuous g) :
    (∫ x : Fin n → ℝ, g (L.polarRealValue x)) =
      (L.polarRealDeterminantScale : ℝ)⁻¹ • ∫ z : Fin n → ℝ, g (∑ i, (z i) ^ 2) := by
  have hmeas : AEMeasurable (Matrix.toLin' L.polarRealSqrtMatrix)
      (volume : Measure (Fin n → ℝ)) :=
    (Matrix.toLin'
      L.polarRealSqrtMatrix).continuous_of_finiteDimensional.measurable.aemeasurable
  have hfun : Continuous fun z : Fin n → ℝ => g (∑ i, (z i) ^ 2) := by
    refine hg.comp (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_apply i).pow 2
  have hleft : (∫ x : Fin n → ℝ, g (L.polarRealValue x)) =
      ∫ x : Fin n → ℝ, g (∑ i, (L.polarRealSqrtMatrix.mulVec x i) ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [L.polarRealValue_eq_sum_sq_mulVec x])
  have hchange : (∫ z : Fin n → ℝ, g (∑ i, (z i) ^ 2)
      ∂Measure.map (Matrix.toLin' L.polarRealSqrtMatrix) (volume : Measure (Fin n → ℝ))) =
      ∫ x : Fin n → ℝ, g (∑ i, (L.polarRealSqrtMatrix.mulVec x i) ^ 2) := by
    simpa only [Matrix.toLin'_apply] using integral_map hmeas hfun.aestronglyMeasurable
  rw [hleft, ← hchange, L.map_polarRealSqrtMatrix_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]

/-- The plain sum of squares is the Euclidean norm squared. -/
theorem integral_sumSq_eq_euclidean (g : ℝ → ℂ) (d : ℕ) :
    (∫ z : Fin d → ℝ, g (∑ i, (z i) ^ 2)) =
      ∫ y : EuclideanSpace ℝ (Fin d), g (‖y‖ ^ 2) := by
  have hmp : MeasurePreserving (@WithLp.toLp 2 (Fin d → ℝ)) :=
    PiLp.volume_preserving_toLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.toLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb (fun y : EuclideanSpace ℝ (Fin d) => g (‖y‖ ^ 2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  congr 1
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine (Finset.sum_congr rfl fun i _ => ?_).symm
  simp [Real.norm_eq_abs, sq_abs]

/-- The radial form of the archimedean Gaussian integral. -/
theorem integral_comp_polarRealValue_radial (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n)
    {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ x : Fin n → ℝ, g (L.polarRealValue x)) =
      (L.polarRealDeterminantScale : ℝ)⁻¹ •
        ((n : ℕ) • (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) •
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) • g (r ^ 2)) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  rw [L.integral_comp_polarRealValue_eq_sumSq hg, integral_sumSq_eq_euclidean g n]
  congr 1
  have h := integral_fun_norm_addHaar (E := EuclideanSpace ℝ (Fin n))
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (fun r : ℝ => g (r ^ 2))
  rw [finrank_euclideanSpace_fin] at h
  exact h

/-- The archimedean value constant of rank `n`: the radial factor after the substitution
`u = r^2`.  It is identified with `pi^(n/2) / Gamma(n/2)` below. -/
def archimedeanValueConstant (n : ℕ) : ℝ :=
  (n : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) / 2

/-- Substituting `u = r^2` turns the radial integral into the value integral. -/
theorem integral_radial_eq_value {n : ℕ} (hn : 0 < n) {g : ℝ → ℂ} :
    (∫ r in Ioi (0 : ℝ), r ^ (n - 1) • g (r ^ 2)) =
      (2 : ℝ)⁻¹ • ∫ u in Ioi (0 : ℝ), (u ^ ((n : ℝ) / 2 - 1)) • g u := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => ((2 : ℝ)⁻¹ * u ^ ((n : ℝ) / 2 - 1)) • g u)
    (p := 2) (by norm_num)
  have hG : (∫ y in Ioi (0 : ℝ), ((2 : ℝ)⁻¹ * y ^ ((n : ℝ) / 2 - 1)) • g y) =
      (2 : ℝ)⁻¹ • ∫ u in Ioi (0 : ℝ), (u ^ ((n : ℝ) / 2 - 1)) • g u := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [smul_smul]
  rw [← hG, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hx2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast x 2]
    norm_num
  rw [hx2, smul_smul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have h1 : x ^ ((2 : ℝ) - 1) = x := by
    norm_num
  have h2 : (x ^ (2 : ℕ)) ^ ((n : ℝ) / 2 - 1) = x ^ ((n : ℝ) - 2) := by
    rw [← hx2, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have h3 : x * x ^ ((n : ℝ) - 2) = x ^ ((n : ℝ) - 1) := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h4 : x ^ ((n : ℝ) - 1) = x ^ (n - 1 : ℕ) := by
    rw [← Real.rpow_natCast x (n - 1)]
    congr 1
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hcast]
  rw [h1, h2, ← h4, ← h3]
  ring

/-- The archimedean Gaussian integral in the value variable. -/
theorem integral_comp_polarRealValue_value (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n)
    {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ x : Fin n → ℝ, g (L.polarRealValue x)) =
      ((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) •
        ∫ u in Ioi (0 : ℝ), (u ^ ((n : ℝ) / 2 - 1)) • g u := by
  rw [L.integral_comp_polarRealValue_radial hn hg, integral_radial_eq_value hn,
    ← Nat.cast_smul_eq_nsmul ℝ n, archimedeanValueConstant]
  simp only [smul_smul]
  congr 1
  ring

/-- The existing real Gamma integral, in the value variable at unit width. -/
theorem integral_value_unitGaussian {n : ℕ} (hn : 0 < n) :
    (∫ u in Ioi (0 : ℝ),
        (u ^ ((n : ℝ) / 2 - 1)) • Complex.exp (-(Real.pi : ℂ) * 1 * (u : ℂ))) =
      ((Real.pi ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2) : ℝ) : ℂ) := by
  have hq : (-1 : ℝ) < (n : ℝ) / 2 - 1 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hreal : (∫ u in Ioi (0 : ℝ),
      u ^ ((n : ℝ) / 2 - 1) * Real.exp (-Real.pi * u)) =
      Real.pi ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (n : ℝ) / 2 - 1)
      (b := Real.pi) one_pos hq Real.pi_pos
    simp only [Real.rpow_one, div_one] at h
    rw [h]
    congr 2 <;> ring
  rw [← hreal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- The archimedean value constant is `pi^(n/2)/Gamma(n/2)`, identified by comparing the
existing unit-width amplitude with the existing real Gamma integral.  No unit-ball volume
is computed. -/
theorem archimedeanValueConstant_eq (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) :
    archimedeanValueConstant n = Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2) := by
  have hgcont : Continuous fun u : ℝ => Complex.exp (-(Real.pi : ℂ) * 1 * (u : ℂ)) := by
    fun_prop
  have hpoint : ∀ x : Fin n → ℝ,
      polarRealGaussian L (1 : ℂ) x =
        Complex.exp (-(Real.pi : ℂ) * 1 * ((L.polarRealValue x : ℝ) : ℂ)) := fun x => by
    rw [polarRealGaussian_eq_exp_polarRealValue]
  have hA : (∫ x : Fin n → ℝ, polarRealGaussian L (1 : ℂ) x) =
      ((L.polarRealDeterminantScale : ℝ) : ℂ)⁻¹ := by
    rw [integral_polarRealGaussian (by norm_num) L]
    simp
  have hB : (∫ x : Fin n → ℝ, polarRealGaussian L (1 : ℂ) x) =
      ((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) •
        ((Real.pi ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (∫ x : Fin n → ℝ, polarRealGaussian L (1 : ℂ) x) =
        ∫ x : Fin n → ℝ, Complex.exp (-(Real.pi : ℂ) * 1 * ((L.polarRealValue x : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [L.integral_comp_polarRealValue_value hn hgcont, integral_value_unitGaussian hn]
  have hscale : (0 : ℝ) < (L.polarRealDeterminantScale : ℝ) := by
    exact_mod_cast L.polarRealDeterminantScale_pos
  have hkey : ((L.polarRealDeterminantScale : ℝ)⁻¹ : ℝ) =
      ((L.polarRealDeterminantScale : ℝ)⁻¹ * archimedeanValueConstant n) *
        (Real.pi ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2)) := by
    have h := hA.symm.trans hB
    rw [Complex.real_smul] at h
    exact_mod_cast h
  have hGpos : 0 < Real.Gamma ((n : ℝ) / 2) := by
    refine Real.Gamma_pos_of_pos ?_
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpi : (0 : ℝ) < Real.pi ^ (-((n : ℝ) / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hone : archimedeanValueConstant n *
      (Real.pi ^ (-((n : ℝ) / 2)) * Real.Gamma ((n : ℝ) / 2)) = 1 := by
    field_simp at hkey
    nlinarith [hkey, hscale, hpi, hGpos]
  have hpiinv : Real.pi ^ (-((n : ℝ) / 2)) = (Real.pi ^ ((n : ℝ) / 2))⁻¹ := by
    rw [Real.rpow_neg Real.pi_pos.le]
  rw [hpiinv] at hone
  field_simp at hone ⊢
  linarith [hone]

end PositiveDefiniteIntegralLattice
