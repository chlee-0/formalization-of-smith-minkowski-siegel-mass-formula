import SMSFormula.AdelicSpinDiagonalBlockProductFormulaReduction
import SMSFormula.AdelicSpinDiagonalBlockRealMass
import SMSFormula.PadicSpinDiagonalBlockIntegrality
import SMSFormula.AdelicGaussianRationalShellFactorProductFormula
import SMSFormula.AdelicGaussianCapstoneSimpleInputs
import SMSFormula.RationalCliffordGeneralSpinHorizontalOrbitMassValue

/-!
# The local block measure data, and the diagonal product formula

For a positive diagonal ternary space `T = ⟨f₀, f₁, f₂⟩` with real surjectivity of `Spin → SO` for
`T` and `U = T ⊥ ⟨f₀f₁f₂⟩`, every input of `DiagonalBlockLocalMeasureData` is proved with the
single rational constant `κ = 8 e_T² / (e_U f₀f₁f₂)`:

* (HL) `c_v = ‖κ‖_v` at every finite place (`map_diagonalBlock_padicChartGluedMeasure`);
* (HK) the integral loci match off `S₀` = lifting bad places of `T, U` and the places where
  `2, f₀, f₁, f₂` or `κ` is not a unit (`diagonalBlock_heightOne_isIntegral_iff`);
* (hr) `μ_T,∞(1)² = |κ|_∞ μ_U,∞(1)` (`diagonalBlock_real_mass`);
* (Hprod) `|κ|_∞ ∏_{S₀} ‖κ‖_v = 1` (rational product formula).

For the diagonal lattices `⟨a, b, c⟩` real surjectivity is already proved, so
`DiagonalSpinProductFormula` holds. Nothing is chosen: `S₀` is the displayed finite set of bad
places and non-unit places.
-/

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

local instance diagonalLocalDataFinalPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance diagonalLocalDataFinalDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- The places where a rational number is not a unit. -/
def rationalNonunitPlaces (q : ℚ) : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  (Rat.padicNormPrimeSupport q).map Rat.HeightOneSpectrum.primesEquiv.symm.toEmbedding

theorem nnnorm_eq_one_of_not_mem_rationalNonunitPlaces {q : ℚ} (hq : q ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum ℤ} (hv : v ∉ rationalNonunitPlaces q) :
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] q‖₊ = 1 := by
  have hv' : Rat.HeightOneSpectrum.primesEquiv v ∉ Rat.padicNormPrimeSupport q := by
    intro h
    apply hv
    exact Finset.mem_map.2 ⟨_, h, by simp⟩
  exact Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport hq _ hv'

theorem norm_eq_one_of_not_mem_rationalNonunitPlaces {q : ℚ} (hq : q ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum ℤ} (hv : v ∉ rationalNonunitPlaces q) :
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] q‖ = 1 := by
  have h := congrArg NNReal.toReal (nnnorm_eq_one_of_not_mem_rationalNonunitPlaces hq hv)
  simpa using h

theorem padicNormPrimeSupport_subset_map_rationalNonunitPlaces (q : ℚ)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hS : rationalNonunitPlaces q ⊆ S) :
    Rat.padicNormPrimeSupport q ⊆ S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding := by
  intro r hr
  exact Finset.mem_map.2 ⟨Rat.HeightOneSpectrum.primesEquiv.symm r, hS (Finset.mem_map.2 ⟨r, hr, rfl⟩),
    Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply r⟩

section LocalData

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

/-- The finite exceptional set: lifting bad places and the non-unit places of `2, fᵢ, κ`. -/
def diagonalBlockExceptionalPlaces : Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  T.cliffordSpinCandidateIntegralLiftingBadPlaces ∪ (UU).cliffordSpinCandidateIntegralLiftingBadPlaces ∪
    rationalNonunitPlaces 2 ∪ rationalNonunitPlaces (f 0) ∪ rationalNonunitPlaces (f 1) ∪
      rationalNonunitPlaces (f 2) ∪ rationalNonunitPlaces (T.diagonalBlockLocalConstant hδ)

include hT in
/-- The local block measure data of a positive diagonal ternary space with real surjectivity. -/
theorem diagonalBlockLocalMeasureData (hTpos : (T.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef)
    (hδpos : 0 < f 0 * f 1 * f 2)
    (hsT : Function.Surjective T.realCliffordSpinCandidateToSpecialOrthogonalHom)
    (hsU : Function.Surjective (UU).realCliffordSpinCandidateToSpecialOrthogonalHom) :
    T.DiagonalBlockLocalMeasureData hT hδ := by
  have hκ := T.diagonalBlockLocalConstant_ne_zero hδ
  have hf : ∀ i, f i ≠ 0 := fun i ↦ diagonalBlock_f_ne_zero hδ i
  refine ⟨T.diagonalBlockExceptionalPlaces hδ,
    fun v ↦ ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (T.diagonalBlockLocalConstant hδ)‖₊,
    ⟨|((T.diagonalBlockLocalConstant hδ : ℚ) : ℝ)|, abs_nonneg _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonvanishing
    intro v
    rw [ne_eq, nnnorm_eq_zero, map_eq_zero]
    exact hκ
  · -- one off the exceptional set
    intro v hv
    refine nnnorm_eq_one_of_not_mem_rationalNonunitPlaces hκ fun h ↦ hv ?_
    exact Finset.mem_union_right _ h
  · -- (HL)
    intro v
    exact T.map_diagonalBlock_padicChartGluedMeasure hT hδ (Rat.HeightOneSpectrum.primesEquiv v).1
  · -- (HK)
    intro v hv a b
    simp only [diagonalBlockExceptionalPlaces, Finset.mem_union, not_or] at hv
    obtain ⟨⟨⟨⟨⟨⟨hvT, hvU⟩, hv2⟩, hv0⟩, hv1⟩, hv2'⟩, -⟩ := hv
    refine T.diagonalBlock_heightOne_isIntegral_iff hT hδ v hvT hvU ?_ ?_ a b
    · intro i
      fin_cases i
      · exact norm_eq_one_of_not_mem_rationalNonunitPlaces (hf 0) hv0
      · exact norm_eq_one_of_not_mem_rationalNonunitPlaces (hf 1) hv1
      · exact norm_eq_one_of_not_mem_rationalNonunitPlaces (hf 2) hv2'
    · have := norm_eq_one_of_not_mem_rationalNonunitPlaces (two_ne_zero : (2 : ℚ) ≠ 0) hv2
      rwa [map_ofNat] at this
  · -- (hr)
    rw [ENNReal.coe_nnreal_eq]
    exact T.diagonalBlock_real_mass hT hδ hTpos hδpos hsT hsU
  · -- the real `U`-mass is nonzero
    have hUpos := T.posDef_nonisotropicLastExtension_map_real hTpos hδ hδpos
    rw [(UU).realCliffordSpinCandidateChartGluedMeasure_univ_eq_two_mul hsU]
    exact mul_ne_zero two_ne_zero ((UU).realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hUpos).1
  · -- the real `U`-mass is finite
    have hUpos := T.posDef_nonisotropicLastExtension_map_real hTpos hδ hδpos
    rw [(UU).realCliffordSpinCandidateChartGluedMeasure_univ_eq_two_mul hsU]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      ((UU).realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hUpos).2
  · -- (Hprod)
    have hsub : rationalNonunitPlaces (T.diagonalBlockLocalConstant hδ) ⊆ T.diagonalBlockExceptionalPlaces hδ :=
      fun v hv ↦ Finset.mem_union_right _ hv
    have h := Rat.ofReal_abs_mul_prod_padicNormENNRealAtPrime_eq_one_of_subset hκ
      (padicNormPrimeSupport_subset_map_rationalNonunitPlaces _ hsub)
    rw [Finset.prod_map] at h
    rw [ENNReal.coe_nnreal_eq, ← h]
    rfl

end LocalData

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

theorem diagLattice3_blockConstant_pos {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < (![(a : ℚ), b, c] 0) * (![(a : ℚ), b, c] 1) * (![(a : ℚ), b, c] 2) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have : (0 : ℚ) < a := by exact_mod_cast ha
  have : (0 : ℚ) < b := by exact_mod_cast hb
  have : (0 : ℚ) < c := by exact_mod_cast hc
  positivity

/-- The local block measure data of every positive diagonal ternary lattice. -/
theorem diagLattice3_diagonalBlockLocalMeasureData {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.DiagonalBlockLocalMeasureData
      (diagLattice3_pairingMatrix ha hb hc) (diagLattice3_blockConstant_ne_zero ha hb hc) := by
  refine (diagLattice3 ha hb hc).rationalQuadraticSpaceMatrix.diagonalBlockLocalMeasureData
    (diagLattice3_pairingMatrix ha hb hc) (diagLattice3_blockConstant_ne_zero ha hb hc)
    (posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real _) (diagLattice3_blockConstant_pos ha hb hc)
    (realCliffordSpinCandidateToSpecialOrthogonalHom_surjective _) ?_
  rw [← blockLattice_eq_nonisotropicLastExtension ha hb hc]
  exact realCliffordSpinCandidateToSpecialOrthogonalHom_surjective _

/-- The diagonal product formula `τ(Spin⟨a, b, c, abc⟩) = τ(Spin⟨a, b, c⟩)²`, proved. -/
theorem diagonalSpinProductFormula : DiagonalSpinProductFormula :=
  diagonalSpinProductFormula_of_local fun _ _ _ ha hb hc ↦ diagLattice3_diagonalBlockLocalMeasureData ha hb hc

end PositiveDefiniteIntegralLattice
