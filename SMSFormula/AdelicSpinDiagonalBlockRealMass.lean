import SMSFormula.PadicSpinDiagonalBlockLocalMass
import SMSFormula.RationalCliffordSpinCandidateLatticeRealSurjectivity
import SMSFormula.RationalSpecialOrthogonalRealMassRatio
import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar

/-!
# The real total masses of the diagonal block

With real surjectivity of `Spin → SO` (positive-definite lattices), the two-sheet law gives
`μ_Spin(1) = 2 μ_SO(1)`, and the Schulze-Pillot mass formula
`μ_SO(1) · SP(n) = |e_V| 2ⁿ √|det|^{n−1}` evaluates both masses.  With `SP(3) = π⁻²`, `SP(4) = π⁻⁴`:

`μ_T,∞(1)² = |κ|_∞ · μ_U,∞(1)`,  `κ = 8 e_T² / (e_U f₀f₁f₂)`,

the same rational constant whose p-adic norms are the local block constants.
-/

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

theorem archimedeanMassFactor_three : archimedeanMassFactor 3 = (Real.pi ^ 2)⁻¹ := by
  unfold archimedeanMassFactor
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Real.rpow_eq_pow]
  have h32 : (((2 + 1 : ℕ) : ℝ) / 2) = 1 / 2 + 1 := by norm_num
  have h12 : (((0 + 1 : ℕ) : ℝ) / 2) = 1 / 2 := by norm_num
  have h1 : (((1 + 1 : ℕ) : ℝ) / 2) = 1 := by norm_num
  have hexp : -(((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 1) / 4) = ((-3 : ℤ) : ℝ) := by norm_num
  rw [h32, h12, h1, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq, Real.Gamma_one, hexp,
    Real.rpow_intCast, _root_.zpow_neg, zpow_ofNat]
  have hπ := Real.pi_pos
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hπ.le
  rw [show Real.sqrt Real.pi * 1 * (1 / 2 * Real.sqrt Real.pi) = Real.pi / 2 by linear_combination (1 / 2 : ℝ) * hs]
  field_simp

theorem archimedeanMassFactor_four : archimedeanMassFactor 4 = (Real.pi ^ 4)⁻¹ := by
  have h := archimedeanMassFactor_succ 3
  rw [show (3 + 1 : ℕ) = 4 from rfl] at h
  rw [h, archimedeanMassFactor_three]
  have h2 : (((3 : ℕ) : ℝ) + 1) / 2 = 2 := by norm_num
  rw [h2, Real.Gamma_two, show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, _root_.zpow_neg,
    zpow_ofNat]
  field_simp

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

noncomputable local instance realMassSpecialOrthogonalMeasurableSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

noncomputable local instance realMassSpecialOrthogonalBorelSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

noncomputable local instance realMassSOGroupMeasurableSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) := borel _

noncomputable local instance realMassSOGroupBorelSpace {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The real two-sheet law: under real surjectivity the real Spin total mass is twice the real
special-orthogonal total mass. -/
theorem realCliffordSpinCandidateChartGluedMeasure_univ_eq_two_mul {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (hs : Function.Surjective V.realCliffordSpinCandidateToSpecialOrthogonalHom) :
    V.realCliffordSpinCandidateChartGluedMeasure Set.univ = 2 * V.realInvariantDifferentialGroupMeasure Set.univ := by
  have h := congrArg (fun μ : Measure V.RealCliffordSpinCandidateImage ↦ μ Set.univ)
    V.map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_imageMeasure
  simp only at h
  have hmeas : Measurable V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict :=
    ((V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).subtype_mk _).measurable
  rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, Measure.smul_apply, realCliffordSpinCandidateImageDifferentialMeasure]
  have hrange : ((V.RealCliffordSpinCandidateImage : Set V.RealSpecialOrthogonalGroup)) = Set.univ := by
    ext g
    simp only [Set.mem_univ, iff_true, SetLike.mem_coe, MonoidHom.mem_range]
    exact hs g
  have hemb : MeasurableEmbedding (V.RealCliffordSpinCandidateImage.subtype :
      V.RealCliffordSpinCandidateImage → V.RealSpecialOrthogonalGroup) :=
    MeasurableEmbedding.subtype_coe V.isOpen_realCliffordSpinCandidateImage.measurableSet
  rw [hemb.comap_apply, Set.image_univ, Subgroup.coe_subtype, Subtype.range_coe, hrange, ENNReal.smul_def,
    smul_eq_mul, ENNReal.coe_ofNat]
  congr 1

theorem two_mul_ofReal_sq_eq (x y k : ℝ) (hx : 0 ≤ x) (hk : 0 ≤ k)
    (h : 2 * x * (2 * x) = k * (2 * y)) :
    2 * ENNReal.ofReal x * (2 * ENNReal.ofReal x) = ENNReal.ofReal k * (2 * ENNReal.ofReal y) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hk, h]

section RealMass

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

local notation "UU" => T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ

theorem realInvariantDifferentialGroupMeasure_univ_eq_ofReal {n : ℕ} [NeZero n] (V : RationalQuadraticSpaceMatrix n)
    (hpos : (V.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) :
    V.realInvariantDifferentialGroupMeasure Set.univ =
      ENNReal.ofReal ((|(Matrix.skewAdjointFixedFormElementaryDetScalar V.pairingMatrix V.form_symm V.form_det_ne_zero : ℝ)| *
          ((2 : ℝ) ^ n * (Real.sqrt |((V.pairingMatrix.det : ℚ) : ℝ)|) ^ (n - 1))) /
        PositiveDefiniteIntegralLattice.archimedeanMassFactor n) := by
  have h := V.realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor hpos
  have hSP := PositiveDefiniteIntegralLattice.archimedeanMassFactor_pos n
  rw [ENNReal.ofReal_div_of_pos hSP, ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hSP).ne' ENNReal.ofReal_ne_top,
    mul_comm, h]

include hT in
/-- The real block mass relation `μ_T,∞(1)² = |κ| μ_U,∞(1)`. -/
theorem diagonalBlock_real_mass (hTpos : (T.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef)
    (hδpos : 0 < f 0 * f 1 * f 2)
    (hsT : Function.Surjective T.realCliffordSpinCandidateToSpecialOrthogonalHom)
    (hsU : Function.Surjective (UU).realCliffordSpinCandidateToSpecialOrthogonalHom) :
    T.realCliffordSpinCandidateChartGluedMeasure Set.univ * T.realCliffordSpinCandidateChartGluedMeasure Set.univ =
      ENNReal.ofReal |((T.diagonalBlockLocalConstant hδ : ℚ) : ℝ)| *
        (UU).realCliffordSpinCandidateChartGluedMeasure Set.univ := by
  have hUpos := T.posDef_nonisotropicLastExtension_map_real hTpos hδ hδpos
  rw [T.realCliffordSpinCandidateChartGluedMeasure_univ_eq_two_mul hsT,
    (UU).realCliffordSpinCandidateChartGluedMeasure_univ_eq_two_mul hsU,
    T.realInvariantDifferentialGroupMeasure_univ_eq_ofReal hTpos,
    (UU).realInvariantDifferentialGroupMeasure_univ_eq_ofReal hUpos]
  have hdetT : ((T.pairingMatrix.det : ℚ) : ℝ) = ((f 0 * f 1 * f 2 : ℚ) : ℝ) := by
    rw [hT, det_diagonal, Fin.prod_univ_three]
  have hdetU : (((UU).pairingMatrix.det : ℚ) : ℝ) = ((f 0 * f 1 * f 2 : ℚ) : ℝ) ^ 2 := by
    rw [T.nonisotropicLastExtension_pairingMatrix_eq_diagonal hT hδ, det_diagonal, Fin.prod_univ_four]
    simp only [diagonalBlockWeights, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    ring
  have heU : ((Matrix.skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm
      (UU).form_det_ne_zero : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.2 (Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero _ _ _)
  have hδr : (0 : ℝ) < ((f 0 * f 1 * f 2 : ℚ) : ℝ) := by exact_mod_cast hδpos
  have hSP3 := PositiveDefiniteIntegralLattice.archimedeanMassFactor_pos 3
  refine two_mul_ofReal_sq_eq _ _ _ (div_nonneg (by positivity) hSP3.le) (abs_nonneg _) ?_
  have hsqT : Real.sqrt |((f 0 * f 1 * f 2 : ℚ) : ℝ)| ^ (3 - 1) = ((f 0 * f 1 * f 2 : ℚ) : ℝ) := by
    rw [abs_of_pos hδr, show (3 - 1 : ℕ) = 2 from rfl, Real.sq_sqrt hδr.le]
  have hsqU : Real.sqrt |((f 0 * f 1 * f 2 : ℚ) : ℝ) ^ 2| ^ (3 + 1 - 1) = ((f 0 * f 1 * f 2 : ℚ) : ℝ) ^ 3 := by
    rw [abs_of_pos (pow_pos hδr 2), Real.sqrt_sq hδr.le]
  rw [PositiveDefiniteIntegralLattice.archimedeanMassFactor_three,
    show PositiveDefiniteIntegralLattice.archimedeanMassFactor (3 + 1) = (Real.pi ^ 4)⁻¹ from
      PositiveDefiniteIntegralLattice.archimedeanMassFactor_four, hdetT, hdetU, hsqT, hsqU]
  unfold diagonalBlockLocalConstant
  have hδr' : (0 : ℝ) < (f 0 : ℝ) * f 1 * f 2 := by exact_mod_cast hδpos
  have heU' : |((Matrix.skewAdjointFixedFormElementaryDetScalar (UU).pairingMatrix (UU).form_symm
      (UU).form_det_ne_zero : ℚ) : ℝ)| ≠ 0 := abs_ne_zero.2 heU
  have hπ := Real.pi_pos
  push_cast at hδr heU ⊢
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hδr', show |(8 : ℝ)| = 8 from abs_of_pos (by norm_num), abs_sq,
    ← sq_abs ((Matrix.skewAdjointFixedFormElementaryDetScalar T.pairingMatrix T.form_symm T.form_det_ne_zero : ℚ) : ℝ)]
  field_simp
  ring

end RealMass

end RationalQuadraticSpaceMatrix
