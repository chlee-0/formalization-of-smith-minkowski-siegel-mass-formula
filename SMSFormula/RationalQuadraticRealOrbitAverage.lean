import SMSFormula.RationalCliffordGeneralSpinHorizontalOrbitMassValue
import SMSFormula.RationalAdeleRankOneBruhatFactorization

/-!
# The real orbit average through a supplied point (the archimedean factor of the rank-four density)

For a positive-definite rational quadratic space `V` and a supplied real point `x₀`, the real
invariant-differential Haar measure `μ_∞` of `SO(V)(ℝ)` is finite and nonzero, so

`A_{x₀}(F) = (∫_{SO(ℝ)} F(g · x₀) dμ_∞(g)) / μ_∞(SO(ℝ))`

is a normalized average over the real orbit of `x₀`.  For bounded continuous `F`:
* it is linear (`realOrbitAverage_add`, `realOrbitAverage_smul`);
* it is nonnegative as soon as `F ≥ 0` on the real sphere `{Q_ℝ = Q_ℝ(x₀)}`
  (`realOrbitAverage_nonneg_of_sphere`), because `SO(ℝ)` preserves `Q_ℝ`;
* it is `SO(ℝ)`-invariant (`realOrbitAverage_comp_mulVec`), by left invariance of `μ_∞`;
* it equals `c` when `F = c` on the sphere (`realOrbitAverage_eq_of_sphere`).
The point `x₀` is supplied (for the rank-four density it is the integral representative).
Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance roaGroupMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance roaGroupBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The real special orthogonal matrices preserve the real quadratic value. -/
theorem realQuadraticFormValue_specialFormPreserving_mulVec (V : RationalQuadraticSpaceMatrix n)
    (g : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ))) (x : Fin n → ℝ) :
    V.realQuadraticFormValue ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) =
      V.realQuadraticFormValue x := by
  have hg : (g.1.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * V.pairingMatrix.map (algebraMap ℚ ℝ) *
      g.1.1.1 = V.pairingMatrix.map (algebraMap ℚ ℝ) := g.1.2
  unfold realQuadraticFormValue realFormMatrix
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

/-- The real orbit average through the supplied point `x₀`. -/
def realOrbitAverage (V : RationalQuadraticSpaceMatrix n) (x₀ : Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ g, F ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀) ∂V.realInvariantDifferentialGroupMeasure) /
    V.realInvariantDifferentialGroupMeasure.real Set.univ

section Properties

variable (V : RationalQuadraticSpaceMatrix n)
  (hpos : (V.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (x₀ : Fin n → ℝ)

include hpos in
theorem isFiniteMeasure_realInvariantDifferentialGroupMeasure [NeZero n] :
    IsFiniteMeasure V.realInvariantDifferentialGroupMeasure :=
  ⟨lt_top_iff_ne_top.2 (V.realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hpos).2⟩

include hpos in
theorem realInvariantDifferentialGroupMeasure_real_univ_pos [NeZero n] :
    0 < V.realInvariantDifferentialGroupMeasure.real Set.univ := by
  obtain ⟨h0, ht⟩ := V.realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hpos
  exact ENNReal.toReal_pos h0 ht

theorem continuous_orbitMap :
    Continuous (fun g : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ)) ↦
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀) := by
  have hM : Continuous (fun g : specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℝ)) ↦ (g.1.1.1 : Matrix (Fin n) (Fin n) ℝ)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact hM.matrix_mulVec continuous_const

include hpos in
/-- A bounded continuous test has an integrable orbit function. -/
theorem integrable_orbit [NeZero n] {F : (Fin n → ℝ) → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Integrable (fun g : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ)) ↦
      F ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀)) V.realInvariantDifferentialGroupMeasure := by
  haveI := V.isFiniteMeasure_realInvariantDifferentialGroupMeasure hpos
  refine (integrable_const C).mono' (hF.comp (V.continuous_orbitMap x₀)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun g ↦ by simpa [Real.norm_eq_abs] using hC _

include hpos in
theorem realOrbitAverage_add [NeZero n] {F G : (Fin n → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    {C D : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGD : ∀ x, |G x| ≤ D) :
    V.realOrbitAverage x₀ (F + G) = V.realOrbitAverage x₀ F + V.realOrbitAverage x₀ G := by
  unfold realOrbitAverage
  rw [← add_div]
  congr 1
  exact integral_add (V.integrable_orbit hpos x₀ hF hFC) (V.integrable_orbit hpos x₀ hG hGD)

theorem realOrbitAverage_smul (r : ℝ) (F : (Fin n → ℝ) → ℝ) :
    V.realOrbitAverage x₀ (r • F) = r * V.realOrbitAverage x₀ F := by
  unfold realOrbitAverage
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, mul_div_assoc]

/-- Positivity on the real sphere. -/
theorem realOrbitAverage_nonneg_of_sphere {F : (Fin n → ℝ) → ℝ}
    (hF : ∀ x, V.realQuadraticFormValue x = V.realQuadraticFormValue x₀ → 0 ≤ F x) :
    0 ≤ V.realOrbitAverage x₀ F := by
  unfold realOrbitAverage
  refine div_nonneg (integral_nonneg fun g ↦ hF _ ?_) measureReal_nonneg
  exact V.realQuadraticFormValue_specialFormPreserving_mulVec g x₀

include hpos in
/-- The unit value: a test equal to `c` on the real sphere averages to `c`. -/
theorem realOrbitAverage_eq_of_sphere [NeZero n] {F : (Fin n → ℝ) → ℝ} {c : ℝ}
    (hF : ∀ x, V.realQuadraticFormValue x = V.realQuadraticFormValue x₀ → F x = c) :
    V.realOrbitAverage x₀ F = c := by
  unfold realOrbitAverage
  have h : (fun g : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ)) ↦
      F ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀)) = fun _ ↦ c := by
    funext g
    exact hF _ (V.realQuadraticFormValue_specialFormPreserving_mulVec g x₀)
  rw [h, integral_const, smul_eq_mul, mul_comm, mul_div_assoc,
    div_self (V.realInvariantDifferentialGroupMeasure_real_univ_pos hpos).ne', mul_one]

/-- `SO(ℝ)`-INVARIANCE of the orbit average. -/
theorem realOrbitAverage_comp_mulVec
    (h : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ)))
    (F : (Fin n → ℝ) → ℝ) :
    V.realOrbitAverage x₀ (fun x ↦ F ((h.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)) =
      V.realOrbitAverage x₀ F := by
  haveI := V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  unfold realOrbitAverage
  congr 1
  have hmul : ∀ g : specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ)),
      (h.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀) =
        ((h * g).1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀ := fun g ↦ by
    rw [Matrix.mulVec_mulVec]
    rfl
  simp_rw [hmul]
  exact integral_mul_left_eq_self (μ := V.realInvariantDifferentialGroupMeasure)
    (fun g ↦ F ((g.1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x₀)) h

end Properties

end RationalQuadraticSpaceMatrix
