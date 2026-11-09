import SMSFormula.RationalSpecialOrthogonalRealArchimedeanNormalization
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitSigmaCompact

/-!
# Real special-orthogonal total mass for positive-definite rational forms

The lattice computation of the real differential total mass uses only that the rational
Gram matrix is positive definite over `ℝ`.  Here it is restated for every rational quadratic
space matrix whose real scalar extension is positive definite: after multiplying by the
Schulze-Pillot archimedean factor, the carrier-independent real differential mass is

`|e(F)| * 2^n * sqrt|det F|^(n-1)`,

with `e(F)` the fixed-to-elementary skew-adjoint determinant scalar of the form.

The positive rational diagonalization is an existential witness of the reduction and is
not retained in the statement.  For the nonisotropic last extension `W ⊕ ⟨a⟩` with `a > 0`
the extension is positive definite, and the two real total masses enter the full-SO
bad-place orbit identity through explicit real factors only.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The carrier-independent real differential total mass of a positive-definite rational form,
times the Schulze-Pillot archimedean factor, is `|e(F)| * 2^n * sqrt|det F|^(n-1)`. -/
theorem realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor
    (V : RationalQuadraticSpaceMatrix n) [NeZero n]
    (hpos : (V.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) :
    V.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (PositiveDefiniteIntegralLattice.archimedeanMassFactor n) =
      ENNReal.ofReal
        (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              V.pairingMatrix V.form_symm V.form_det_ne_zero : ℝ)| *
          ((2 : ℝ) ^ n * (Real.sqrt |((V.pairingMatrix.det : ℚ) : ℝ)|) ^ (n - 1))) := by
  obtain ⟨d, W, hd, hdiag, hmass⟩ :=
    PositiveDefiniteIntegralLattice.exists_positive_diagonal_realDifferentialMeasure_mass
      V.pairingMatrix V.form_symm hpos
  have hmass' :
      V.realInvariantDifferentialGroupMeasure Set.univ =
        (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W|)⁻¹) : ℝ≥0∞) *
          PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure
            (Matrix.diagonal d) (PositiveDefiniteIntegralLattice.positiveDiagonalForm_isSymm d)
            (PositiveDefiniteIntegralLattice.positiveDiagonalForm_det_ne_zero d hd) Set.univ := by
    rw [realInvariantDifferentialGroupMeasure, hmass]
    congr 1
    have key : ∀ (F' : Matrix (Fin n) (Fin n) ℚ) (hFF' : F' = Matrix.diagonal d)
        (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0),
        PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
            Set.univ =
          PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure
            (Matrix.diagonal d) (PositiveDefiniteIntegralLattice.positiveDiagonalForm_isSymm d)
            (PositiveDefiniteIntegralLattice.positiveDiagonalForm_det_ne_zero d hd) Set.univ := by
      intro F' hFF' _ _
      subst hFF'
      rfl
    exact key _ hdiag _ _
  rw [hmass', PositiveDefiniteIntegralLattice.positiveDiagonalSmoothRealDifferentialMeasure_univ_eq_det_mul_gamma_rank
    n d hd]
  have hcong :
      (↑((Real.toNNReal
          |Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W|)⁻¹) : ℝ≥0∞) =
        ENNReal.ofReal |Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W|⁻¹ := by
    simp only [ENNReal.ofReal]
    congr
    rw [Real.toNNReal_inv]
  have hdiagScale :
      (↑((Real.toNNReal |PositiveDefiniteIntegralLattice.positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) :
          ℝ≥0∞) =
        ENNReal.ofReal |PositiveDefiniteIntegralLattice.positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ := by
    simp only [ENNReal.ofReal]
    congr
    rw [Real.toNNReal_inv]
  rw [hcong, hdiagScale]
  change
    (ENNReal.ofReal |Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W|⁻¹ *
      (ENNReal.ofReal |PositiveDefiniteIntegralLattice.positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ *
        (ENNReal.ofReal
            |(PositiveDefiniteIntegralLattice.identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
          ENNReal.ofReal (PositiveDefiniteIntegralLattice.specialOrthogonalRealGammaFactor n)))) *
        ENNReal.ofReal (PositiveDefiniteIntegralLattice.archimedeanMassFactor n) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg
    (PositiveDefiniteIntegralLattice.identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ))]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr
    (abs_nonneg (PositiveDefiniteIntegralLattice.positiveDiagonalSkewAdjointDetScalar d hd)))]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr
    (abs_nonneg (Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W)))]
  have hreal_nonneg :
      0 ≤ |Matrix.skewAdjointRealCongruenceDetScalar V.pairingMatrix W|⁻¹ *
        (|PositiveDefiniteIntegralLattice.positiveDiagonalSkewAdjointDetScalar d hd|⁻¹ *
          (|(PositiveDefiniteIntegralLattice.identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| *
            PositiveDefiniteIntegralLattice.specialOrthogonalRealGammaFactor n)) :=
    mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
        (mul_nonneg (abs_nonneg _)
          (le_of_lt (PositiveDefiniteIntegralLattice.specialOrthogonalRealGammaFactor_pos n))))
  rw [← ENNReal.ofReal_mul hreal_nonneg]
  exact congrArg ENNReal.ofReal
    (PositiveDefiniteIntegralLattice.skewAdjointRealDeterminantGammaArchimedeanFactor_closed
      V.pairingMatrix V.form_symm V.form_det_ne_zero W d hd hdiag)

/-- The real block matrix `F ⊕ ⟨a⟩` is positive definite when `F` is and `a > 0`. -/
theorem posDef_nonisotropicLastBlockMatrix {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef)
    {a : ℝ} (ha : 0 < a) :
    (nonisotropicLastBlockMatrix F a).PosDef := by
  have hsymm : (nonisotropicLastBlockMatrix F a).IsHermitian := by
    ext i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Matrix.conjTranspose_apply]
    exact congrFun (congrFun hF.isHermitian.eq _) _
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hsymm ?_
  intro x hx
  have hmul : ∀ i : Fin n,
      (nonisotropicLastBlockMatrix F a *ᵥ x) i.castSucc = (F *ᵥ (x ∘ Fin.castSucc)) i := by
    intro i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hlast : (nonisotropicLastBlockMatrix F a *ᵥ x) (Fin.last n) = a * x (Fin.last n) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hsplit : x ⬝ᵥ (nonisotropicLastBlockMatrix F a *ᵥ x) =
      (x ∘ Fin.castSucc) ⬝ᵥ (F *ᵥ (x ∘ Fin.castSucc)) + a * x (Fin.last n) ^ 2 := by
    rw [dotProduct, Fin.sum_univ_castSucc, hlast]
    simp only [hmul, dotProduct, Function.comp_apply]
    ring
  change 0 < x ⬝ᵥ (nonisotropicLastBlockMatrix F a *ᵥ x)
  rw [hsplit]
  by_cases h0 : x ∘ Fin.castSucc = 0
  · have hl : x (Fin.last n) ≠ 0 := by
      intro hl
      apply hx
      funext i
      cases i using Fin.lastCases with
      | last => exact hl
      | cast i => exact congrFun h0 i
    rw [h0]
    simp only [Matrix.mulVec_zero, dotProduct_zero, zero_add]
    exact mul_pos ha (pow_pos (abs_pos.mpr hl) 2 |>.trans_eq (sq_abs _))
  · exact add_pos_of_pos_of_nonneg (hF.dotProduct_mulVec_pos h0)
      (mul_nonneg ha.le (sq_nonneg _))

/-- For positive-definite `W` and `a > 0`, the nonisotropic last extension is positive
definite over `ℝ`. -/
theorem posDef_nonisotropicLastExtension_map_real (W : RationalQuadraticSpaceMatrix n)
    (hW : (W.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) {a : ℚ} (ha : a ≠ 0) (ha0 : 0 < a) :
    ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℝ)).PosDef := by
  have h := W.nonisotropicLastExtension_mappedFormMatrix a ha ℝ
  simp only [specialOrthogonalMappedFormMatrix] at h
  rw [h]
  exact posDef_nonisotropicLastBlockMatrix hW (by simpa using ha0)

/-- Pure rearrangement: substitute two evaluated masses into a cross-multiplied identity. -/
theorem _root_.ENNReal.mul_mul_mul_eq_of_mass_eval {N μW μV PW PV sW sV RW RV : ℝ≥0∞}
    (h : N * (μW * PW) = μV * PV) (hW : μW * sW = RW) (hV : μV * sV = RV) :
    N * (RW * sV * PW) = RV * sW * PV := by
  subst hW hV
  calc N * (μW * sW * sV * PW) = N * (μW * PW) * (sW * sV) := by ring
    _ = μV * sV * sW * PV := by rw [h]; ring

/-- The full-SO bad-place orbit identity with both real total masses evaluated.  For
positive-definite `W`, `a > 0` and compact supplied bad-place subgroups, the orbit mass of the
central-cutoff cylinder satisfies

`N(K•x) * (|e_W| 2^n sqrt|det W|^(n-1)) * SP(n+1) * ∏_B s_W Haar_W(ι⁻¹t_v)
  = (|e_V| 2^(n+1) sqrt|a det W|^n) * SP(n) * ∏_B s_V Haar_V(t_v)`,

with `SP` the Schulze-Pillot archimedean factor and `e` the fixed-to-elementary
skew-adjoint determinant scalars of `W` and `V = W ⊕ ⟨a⟩`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_realMass
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (hW : (W.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (a : ℚ) (ha : a ≠ 0) (ha0 : 0 < a)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (t : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))
    (ht : ∀ v, MeasurableSet
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (htW : ∀ v, MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))))
    (htc : ∀ v, IsCompact
      (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S t)) : Set _)) *
      (ENNReal.ofReal
          (|(Matrix.skewAdjointFixedFormElementaryDetScalar
                W.pairingMatrix W.form_symm W.form_det_ne_zero : ℝ)| *
            ((2 : ℝ) ^ n * (Real.sqrt |((W.pairingMatrix.det : ℚ) : ℝ)|) ^ (n - 1))) *
        ENNReal.ofReal (PositiveDefiniteIntegralLattice.archimedeanMassFactor (n + 1)) *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
              (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
                (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                  v.1)))) =
      ENNReal.ofReal
          (|(Matrix.skewAdjointFixedFormElementaryDetScalar
                (W.nonisotropicLastExtension a ha).pairingMatrix
                (W.nonisotropicLastExtension a ha).form_symm
                (W.nonisotropicLastExtension a ha).form_det_ne_zero : ℝ)| *
            ((2 : ℝ) ^ (n + 1) *
              (Real.sqrt |((W.pairingMatrix.det * a : ℚ) : ℝ)|) ^ n)) *
        ENNReal.ofReal (PositiveDefiniteIntegralLattice.archimedeanMassFactor n) *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
              v.1 (t v : Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup
                v.1)) := by
  have hV := (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor
    (W.posDef_nonisotropicLastExtension_map_real hW ha ha0)
  have hdet : (W.nonisotropicLastExtension a ha).pairingMatrix.det = W.pairingMatrix.det * a := by
    rw [nonisotropicLastExtension_pairingMatrix, nonisotropicLastBlockMatrix_det]
  rw [hdet, Nat.add_sub_cancel] at hV
  exact ENNReal.mul_mul_mul_eq_of_mass_eval
    (W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_top_of_isCompact a ha hT hneg
      hT0 hTtop hSB t ht htW htc)
    (W.realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor hW) hV

end RationalQuadraticSpaceMatrix
