import SMSFormula.AdelicGaussianFiberDetermination
import SMSFormula.RationalAdeleTranslatedCarrierSandwich

/-!
# The actual fixed-width real core is stable under the adelic action

The real shift moves by the inverse real isometry. On the finite side the
matrix-denominator sandwich supplies carrier and period scales. No width, Haar,
character or conductor changes; the finite scales depend on the acting matrix.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice
variable {n : ℕ}

/-- Pullback by a finite matrix unit stays in the standard family. The
same denominator N gives explicit scales c*N and d*N, with no uniform bound. -/
theorem standardFamily_matrixUnit_pullback_scales
    (M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ)
    {c d : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcar : IsStandardCarried c f) (hper : IsStandardPeriodic d f) :
    ∃ N : ℕ, N ≠ 0 ∧
      IsStandardCarried (c*N) (fun x ↦ f (M.val.mulVec x)) ∧
      IsStandardPeriodic (d*N) (fun x ↦ f (M.val.mulVec x)) := by
  obtain ⟨N, hN, hlow, hhigh⟩ := exists_natScale_translatedCarrier_sandwich M
  have hlow' (u : Fin n → RationalFiniteAdele) (hu : u ∈ integralFiniteAdeleVectors n) :
      M.val.mulVec (N • u) ∈ integralFiniteAdeleVectors n := by
    simpa only [Pi.smul_apply, nsmul_eq_mul] using hlow u hu
  have hhigh' (y : Fin n → RationalFiniteAdele)
      (hy : M.val.mulVec y ∈ integralFiniteAdeleVectors n) :
      N • y ∈ integralFiniteAdeleVectors n := by
    simpa only [Pi.smul_apply, nsmul_eq_mul] using hhigh y hy
  refine ⟨N, hN, ?_, ?_⟩
  · intro x hx
    apply hcar
    intro hMx
    apply hx
    have hm : M.val.mulVec (c • x) ∈ integralFiniteAdeleVectors n := by
      rw [Matrix.mulVec_smul]
      exact hMx
    have h := hhigh' (c • x) hm
    simpa only [smul_smul, mul_comm N c] using h
  · intro x u hu
    dsimp only
    rw [Matrix.mulVec_add, mul_smul, Matrix.mulVec_smul]
    exact hper _ _ (hlow' u hu)

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- Orthogonal pullback keeps the real width and moves the center by the inverse.
This is the centered invariance theorem applied after subtracting that center. -/
theorem realShiftedGaussian_realSpecialOrthogonal (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (h : L.rationalQuadraticSpaceMatrix.RealSpecialOrthogonalGroup)
    (u x : Fin n → ℝ) :
    realShiftedGaussian L b u (h.1.1.1.mulVec x) =
      realShiftedGaussian L b ((h.1.1⁻¹).val.mulVec u) x := by
  have hinv : h.1.1.1.mulVec ((h.1.1⁻¹).val.mulVec u) = u := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsub : h.1.1.1.mulVec x - u =
      h.1.1.1.mulVec (x - (h.1.1⁻¹).val.mulVec u) := by
    rw [Matrix.mulVec_sub, hinv]
  unfold realShiftedGaussian
  rw [hsub, polarRealGaussian_realSpecialOrthogonal]

/-- The whole real core, not just its standard generator, is stable under
every full-adelic special orthogonal action. No rank or width sign is needed
for this structural fact; those hypotheses enter only analytic admissibility. -/
theorem mem_realGaussianCore_comp_specialOrthogonal (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    (fun x ↦ f (h.1.1.1.mulVec x)) ∈ realGaussianCore L b := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, c, d, g, hc, hd, hcar, hper, rfl⟩ := hf
    let hR := (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1
    let hF := (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2
    obtain ⟨N, hN, hc', hd'⟩ := standardFamily_matrixUnit_pullback_scales hF.1.1 hcar hper
    apply Submodule.subset_span
    refine ⟨(hR.1.1⁻¹).val.mulVec u, c*N, d*N, fun y ↦ g (hF.1.1.1.mulVec y),
      mul_ne_zero hc hN, mul_ne_zero hd hN, hc', hd', ?_⟩
    funext x
    dsimp only
    rw [L.rationalQuadraticSpaceMatrix.rationalAdeleVectorRealPart_fullAdelicSpecialOrthogonal_mulVec,
      L.rationalQuadraticSpaceMatrix.rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec,
      realShiftedGaussian_realSpecialOrthogonal]
  | zero => exact (realGaussianCore L b).zero_mem
  | add f g _ _ hf hg => exact (realGaussianCore L b).add_mem hf hg
  | smul r f _ hf => exact (realGaussianCore L b).smul_mem r hf

/-- Structural stability in the acting group's own matrix-point interface. -/
theorem mem_realGaussianCore_comp_generalSpin (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L b) :
    (fun x ↦ f (g.matrixPoint.1.mulVec x)) ∈ realGaussianCore L b := by
  simpa only [CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe] using
    mem_realGaussianCore_comp_specialOrthogonal L b g.matrixGroup hf

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
