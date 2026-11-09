import SMSFormula.QuadraticPadicCayleyIdentityChartData

/-! The good-place ledger identity. The integral
subgroup of the lower group is the stabilizer intersection of the integral
subgroup of the higher group: `K_{V,p} ∩ H = K_{W,p}` (a fixed-last block matrix
and its inverse are integral exactly when the lower block and its inverse are).
With the differential Haars, `v_{V,p} = vol_G(K_{V,p})` and
`v_{W,p} = vol_H(K_{W,p})` (positive and finite), at every prime outside the
explicit finite exceptional set

`v_{V,p} / v_{W,p} = κ_p · d_p(a)`, with `κ_p = |r| · ν(ℤ_p)` and `d_p(a) = λ(X_a(ℤ_p))`

for the glued fiber measure `λ` (any atlas covering the nonisotropic
vectors). This is the ledger bridge (1.5) in its own variables; the
probability baselines are not touched here. No chart or normalization is
chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

/-- A fixed-last block matrix is integral exactly when its lower block is. -/
theorem fixLastBlockMatrix_entries_le_one_iff (M : Matrix (Fin n) (Fin n) ℚ_[p]) :
    (∀ i j, ‖fixLastBlockMatrix M i j‖ ≤ 1) ↔ ∀ i j, ‖M i j‖ ≤ 1 := by
  constructor
  · intro h i j
    have := h i.castSucc j.castSucc
    rwa [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_castSucc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_last_last]
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_last_castSucc]
    · simp [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_last]
    · rw [fixLastBlockMatrix, nonisotropicLastBlockMatrix_castSucc_castSucc]; exact h i j

/-- Stabilizer intersection: the integral subgroup of the
higher group meets the lower group in the integral lower subgroup. -/
theorem comap_padicIntegralSpecialSubgroup_lastFiberEmbedHom :
    (padicIntegralSpecialSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).comap
      (W.lastFiberEmbedHom p a ha) =
      padicIntegralSpecialSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p])) := by
  ext g
  rw [Subgroup.mem_comap]
  have h1 : ((W.lastFiberEmbedHom p a ha g).1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) =
      fixLastBlockMatrix (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := rfl
  have h2 : (((W.lastFiberEmbedHom p a ha g).1.1)⁻¹ : (Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])ˣ).1 =
      fixLastBlockMatrix ((g.1.1)⁻¹ : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ).1 := by
    have := congrArg (fun x ↦ (x.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]))
      (map_inv (W.lastFiberEmbedHom p a ha) g)
    exact this.symm
  change ((∀ i j, ((W.lastFiberEmbedHom p a ha g).1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) i j ∈
      PadicInt.subring p) ∧
      (∀ i j, (((W.lastFiberEmbedHom p a ha g).1.1)⁻¹ : (Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])ˣ).1 i j ∈
      PadicInt.subring p)) ↔
    ((∀ i j, (g.1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j ∈ PadicInt.subring p) ∧
      (∀ i j, ((g.1.1)⁻¹ : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ).1 i j ∈ PadicInt.subring p))
  rw [h1, h2]
  simp only [PadicInt.mem_subring_iff]
  rw [fixLastBlockMatrix_entries_le_one_iff, fixLastBlockMatrix_entries_le_one_iff]

section Ledger

local instance ldPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ldPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance ldGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ldGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance ldLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance ldLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

/-- The integral lower mass `v_{W,p}` is positive and finite. -/
theorem padicIntegral_lower_measure_pos_lt_top :
    0 < padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
        (padicIntegralSpecialSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) ∧
      padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
        (padicIntegralSpecialSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) < ∞ := by
  haveI := padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure p n W.pairingMatrix
    W.form_symm W.form_det_ne_zero
  refine ⟨(isOpen_padicIntegralSpecialSubgroup _).measure_pos _
    ⟨1, (padicIntegralSpecialSubgroup _).one_mem⟩,
    (isCompact_padicIntegralSpecialSubgroup _).measure_lt_top⟩

/-- Ledger form at every non-exceptional prime:
`v_{V,p} = κ_p · d_p(a) · v_{W,p}` with `κ_p = |r| ν(ℤ_p)` and `d_p(a) = λ(X_a(ℤ_p))`. -/
theorem padicIntegral_measure_eq_ledger_of_notMem (hn : 1 ≤ n)
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)
    (point : ℕ → Fin (n+1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) =
      ((‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) * ν (closedBall 0 1)) *
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1} *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          (padicIntegralSpecialSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := by
  rw [W.lastCayleyProduct_measure_padicIntegral_eq_integralPoints_of_notMem p a ha ν hn hp point
    hpoint tH hcover, W.comap_padicIntegralSpecialSubgroup_lastFiberEmbedHom p a ha]
  ring

/-- Ledger quotient: `v_{V,p} / v_{W,p} = κ_p · d_p(a)` at every non-exceptional prime. -/
theorem padicIntegral_measure_div_eq_ledger_of_notMem (hn : 1 ≤ n)
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)
    (point : ℕ → Fin (n+1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) /
      padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          (padicIntegralSpecialSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) =
      ((‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) * ν (closedBall 0 1)) *
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1} := by
  obtain ⟨hpos, hfin⟩ := W.padicIntegral_lower_measure_pos_lt_top p
  rw [W.padicIntegral_measure_eq_ledger_of_notMem p a ha ν hn hp point hpoint tH hcover,
    ENNReal.mul_div_cancel_right hpos.ne' hfin.ne]

end Ledger

end RationalQuadraticSpaceMatrix
