import SMSFormula.AdelicGaussianPolarShellDensity
import SMSFormula.RationalAdelePolarDualThetaFiniteness

/-!
# The dual-carrier test is a member of the real Gaussian core

The dual-carrier test `Ψ_b = G_b(x_∞) · 1_{C⁻¹ Ẑ^n}(x_f)` (`rationalAdeleVectorPolarGaussianDualTest`,
with `C` the integral Gram matrix) is a generator of the real Gaussian core:
- centre `u = 0`;
- carrier `c = |polarDeterminant L|`, since `adj(C) · C = polarDeterminant · 1` gives `polarDeterminant · y ∈ Ẑ^n` whenever `C y ∈ Ẑ^n`;
- period `d = 1`, since `C Ẑ^n ⊆ Ẑ^n`.

So the Riesz identity applies to it on every supplied represented shell, exactly as for the
standard test.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The dual carrier is contained in the `|polarDeterminant L|`-divided standard lattice. -/
theorem finitePolarDualLattice_subset_standardDividedLattice (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.finitePolarDualLattice ⊆
      standardDividedLattice n L.polarDeterminant.natAbs := by
  intro y hy
  have hC : (L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele)).mulVec y ∈
      integralFiniteAdeleVectors n := by
    have := hy
    rw [RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff,
      L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix] at this
    exact this
  have hadj := integralFiniteAdeleVectors_mulVec_intMatrix L.polarGramMatrix.adjugate _ hC
  have hmat : L.polarGramMatrix.adjugate.map (algebraMap ℤ RationalFiniteAdele) *
      L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele) =
        L.polarDeterminant • (1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) := by
    rw [← Matrix.map_mul, Matrix.adjugate_mul]
    rw [show L.polarGramMatrix.det = L.polarDeterminant by rfl]
    simpa using Matrix.map_smul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant
      (fun a => map_zsmul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant a)
      (1 : Matrix (Fin n) (Fin n) ℤ)
  rw [Matrix.mulVec_mulVec, hmat, Matrix.smul_mulVec, Matrix.one_mulVec] at hadj
  have hnat : ((L.polarDeterminant.natAbs : ℕ) : ℤ) = L.polarDeterminant := Int.natAbs_of_nonneg L.polarDeterminant_pos.le
  change L.polarDeterminant.natAbs • y ∈ integralFiniteAdeleVectors n
  intro i
  have hi := hadj i
  simp only [Pi.smul_apply, zsmul_eq_mul] at hi
  simp only [Pi.smul_apply, nsmul_eq_mul]
  have : ((L.polarDeterminant.natAbs : ℕ) : RationalFiniteAdele) = (L.polarDeterminant : RationalFiniteAdele) := by
    rw [← Int.cast_natCast, hnat]
  rw [this]
  exact hi

/-- The real finite factor of the dual-carrier test. -/
def realFinitePolarDualLatticeIndicator (L : PositiveDefiniteIntegralLattice n)
    (y : Fin n → RationalFiniteAdele) : ℝ :=
  (L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator y).re

theorem coe_realFinitePolarDualLatticeIndicator (L : PositiveDefiniteIntegralLattice n)
    (y : Fin n → RationalFiniteAdele) :
    ((realFinitePolarDualLatticeIndicator L y : ℝ) : ℂ) =
      L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator y := by
  unfold realFinitePolarDualLatticeIndicator
  by_cases hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hy]; simp
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hy]; simp

theorem realFinitePolarDualLatticeIndicator_eq_zero_or_one (L : PositiveDefiniteIntegralLattice n)
    (y : Fin n → RationalFiniteAdele) :
    realFinitePolarDualLatticeIndicator L y = 0 ∨ realFinitePolarDualLatticeIndicator L y = 1 := by
  unfold realFinitePolarDualLatticeIndicator
  by_cases hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · right; rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hy]; simp
  · left; rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hy]; simp

theorem isStandardCarried_finitePolarDualLatticeIndicator (L : PositiveDefiniteIntegralLattice n) :
    IsStandardCarried L.polarDeterminant.natAbs (fun y ↦ (realFinitePolarDualLatticeIndicator L y : ℂ)) := by
  intro y hy
  dsimp only
  rw [coe_realFinitePolarDualLatticeIndicator]
  exact RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _
    fun h ↦ hy (finitePolarDualLattice_subset_standardDividedLattice L h)

theorem isStandardPeriodic_finitePolarDualLatticeIndicator (L : PositiveDefiniteIntegralLattice n) :
    IsStandardPeriodic 1 (fun y ↦ (realFinitePolarDualLatticeIndicator L y : ℂ)) := by
  intro y u hu
  simp only [coe_realFinitePolarDualLatticeIndicator, one_nsmul]
  have hCu : L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec u ∈
      integralFiniteAdeleVectors n := by
    rw [L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix]
    exact integralFiniteAdeleVectors_mulVec_intMatrix L.polarGramMatrix u hu
  have hiff : y + u ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice ↔
      y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
    simp only [RationalQuadraticSpaceMatrix.mem_finitePolarDualLattice_iff, Matrix.mulVec_add]
    constructor
    · intro h i
      have := integralFiniteAdeleSubring.sub_mem (h i) (hCu i)
      simpa using this
    · intro h i
      exact integralFiniteAdeleSubring.add_mem (h i) (hCu i)
  by_cases hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hy,
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ (hiff.mpr hy)]
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hy,
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _
        (fun h ↦ hy (hiff.mp h))]

/-- The dual-carrier test as a member of the real Gaussian core. -/
def polarGaussianDualCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) : realGaussianCore L b :=
  ⟨fun x ↦ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realFinitePolarDualLatticeIndicator L (rationalAdeleVectorFinitePart n x),
    Submodule.subset_span ⟨0, L.polarDeterminant.natAbs, 1, realFinitePolarDualLatticeIndicator L,
      Int.natAbs_ne_zero.mpr L.polarDeterminant_pos.ne', one_ne_zero,
      isStandardCarried_finitePolarDualLatticeIndicator L,
      isStandardPeriodic_finitePolarDualLatticeIndicator L, rfl⟩⟩

theorem coe_polarGaussianDualCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (x : Fin n → RationalAdele) :
    ((polarGaussianDualCore L b).val x : ℂ) = rationalAdeleVectorPolarGaussianDualTest L (b : ℂ) x := by
  change ((realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realFinitePolarDualLatticeIndicator L (rationalAdeleVectorFinitePart n x) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, coe_realFinitePolarDualLatticeIndicator, rationalAdeleVectorPolarGaussianDualTest]
  congr 1
  simp only [realShiftedGaussian, sub_zero, polarRealGaussian_eq_quadraticShiftedGaussian,
    Complex.ofReal_re]

theorem polarGaussianDualCore_nonneg (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (x : Fin n → RationalAdele) :
    0 ≤ (polarGaussianDualCore L b).val x := by
  change 0 ≤ realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
      realFinitePolarDualLatticeIndicator L (rationalAdeleVectorFinitePart n x)
  refine mul_nonneg (realShiftedGaussian_pos L b _ _).le ?_
  rcases realFinitePolarDualLatticeIndicator_eq_zero_or_one L (rationalAdeleVectorFinitePart n x)
    with h | h <;> rw [h]; exact zero_le_one

theorem rationalAdeleVectorPolarGaussianDualTestENNReal_eq_ofReal (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianDualTestENNReal L b x =
      ENNReal.ofReal ((polarGaussianDualCore L b).val x) := by
  rw [rationalAdeleVectorPolarGaussianDualTestENNReal, ← coe_polarGaussianDualCore,
    Complex.norm_real, Real.norm_of_nonneg (polarGaussianDualCore_nonneg L b x)]

theorem realValueDensity_polarGaussianDualCore (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.realValueDensity (polarGaussianDualCore L b).val a =
      (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianDualTest L (b : ℂ)) a).re := by
  change (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
      (fun x ↦ ((polarGaussianDualCore L b).val x : ℂ)) a).re = _
  simp_rw [coe_polarGaussianDualCore]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
