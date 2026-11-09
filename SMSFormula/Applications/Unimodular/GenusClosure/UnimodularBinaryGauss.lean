import SMSFormula.Applications.Unimodular.GenusClosure.BinaryDualQuotient
import SMSFormula.Applications.Unimodular.GenusClosure.DiagonalClassification
import SMSFormula.Applications.Unimodular.TypeIIObstruction

noncomputable section

namespace UnimodularGenusClosure
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Matrix
open scoped BigOperators

def binaryFormMatrixEquiv {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) : (Fin n → R2) ≃+ (Fin n → R2) where
  toFun := (lattice.pairingMatrix.map (Int.castRingHom R2)).mulVec
  invFun := (lattice.pairingMatrix.adjugate.map (Int.castRingHom R2)).mulVec
  left_inv := by
    intro vector
    have hdet : lattice.pairingMatrix.det = 1 := hunimodular
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul, hdet, one_smul]
    simp
  right_inv := by
    intro vector
    have hdet : lattice.pairingMatrix.det = 1 := hunimodular
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_adjugate, hdet, one_smul]
    simp
  map_add' := Matrix.mulVec_add _

def binaryFormPolarQuotientEquiv {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    (Fin n → R2) ≃+ ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup lattice 1) :=
  (binaryFormMatrixEquiv lattice hunimodular).trans
    (binaryPolarQuotientEquiv lattice hunimodular)

theorem binaryFormPolarQuotientEquiv_intCast {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (vector : Fin n → ℤ) :
    binaryFormPolarQuotientEquiv lattice hunimodular (fun index => (vector index : R2)) =
      (fun index => integerToIntegralFiniteAdele (lattice.pairingMatrix.mulVec vector index) :
        (Fin n → IntegralFiniteAdele) ⧸
          integralFiniteAdelePolarDenDilationAddSubgroup lattice 1) := by
  have hcast : binaryFormMatrixEquiv lattice hunimodular
      (fun index => (vector index : R2)) =
        fun index => (lattice.pairingMatrix.mulVec vector index : R2) := by
    funext index
    simp [binaryFormMatrixEquiv, Matrix.mulVec, dotProduct]
  rw [binaryFormPolarQuotientEquiv, AddEquiv.trans_apply, hcast,
    binaryPolarQuotientEquiv_intCast]

theorem inversePolarValue_pairingMatrix {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (vector : Fin n → ℤ) :
    integerVectorMatrixQuadraticValue lattice.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
      (lattice.pairingMatrix.mulVec vector) = (2 : ℝ)⁻¹ * (lattice.quadForm vector : ℝ) := by
  let form : Matrix (Fin n) (Fin n) ℝ := lattice.pairingMatrix.map (Int.cast : ℤ → ℝ)
  have hpolar : lattice.rationalQuadraticSpaceMatrix.realPolarMatrix = (2 : ℝ) • form := by
    ext row col
    simp [RationalQuadraticSpaceMatrix.realPolarMatrix,
      RationalQuadraticSpaceMatrix.polarMatrix, PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix,
      PositiveDefiniteIntegralLattice.rationalFormMatrix, form]
  have hleft : form * form⁻¹ = 1 :=
    lattice.real_pairingMatrix_mul_inv_of_isUnimodular hunimodular
  have hinverse : lattice.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹ =
      (2 : ℝ)⁻¹ • form⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hpolar, Matrix.smul_mul, Matrix.mul_smul, hleft]
    simp [smul_smul]
  have hvalue : integerVectorReal vector ⬝ᵥ form.mulVec (integerVectorReal vector) =
      (lattice.quadForm vector : ℝ) := by
    rw [lattice.quadForm_eq_dotProduct]
    simp [integerVectorReal, form, Matrix.mulVec, dotProduct]
  unfold integerVectorMatrixQuadraticValue
  rw [hinverse, lattice.integerVectorReal_pairingMatrix_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul,
    PositiveDefiniteIntegralLattice.dotProduct_mulVec_inv_mulVec_mulVec_eq hleft
      (lattice.real_pairingMatrix_isSymm) (integerVectorReal vector), hvalue]

theorem polarQuotientPhase_pairingMatrix_intCast {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (vector : Fin n → ℤ) :
    rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient lattice 1
      (fun index => integerToIntegralFiniteAdele (lattice.pairingMatrix.mulVec vector index) :
        (Fin n → IntegralFiniteAdele) ⧸
          integralFiniteAdelePolarDenDilationAddSubgroup lattice 1) =
      quarticPhase (-(lattice.quadForm vector : R4)) := by
  have hphase := lattice.rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues_intCast_eq_oscillation
    (1 : ℚ) (lattice.pairingMatrix.mulVec vector)
  unfold rationalFiniteAdelePolarDualQuadraticPhaseOnRectangularResidues at hphase
  rw [rectangularResidueToPolarMatrixQuotient_apply_intCast] at hphase
  calc
    _ = quadraticOscillation lattice.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
        1 (lattice.pairingMatrix.mulVec vector) := by simpa only [Rat.cast_one] using hphase
    _ = _ := by
      rw [quadraticOscillation, inversePolarValue_pairingMatrix lattice hunimodular,
        quarticPhase_eq_stdAddChar,
        show -(lattice.quadForm vector : R4) = ((-lattice.quadForm vector : ℤ) : R4) by simp,
        ZMod.stdAddChar_coe]
      congr 1
      push_cast
      ring

theorem dualGaussIntegral_one_eq_binaryPhaseSum {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral 1 =
      ∑ vector : Fin n → R2,
        quarticPhase (-(lattice.quadForm (fun index => (vector index).val) : R4)) := by
  rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarMatrixQuotientSum]
  calc
    _ = ∑ vector : Fin n → R2,
        rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient lattice 1
          (binaryFormPolarQuotientEquiv lattice hunimodular vector) := by
      simpa using (Equiv.sum_comp (binaryFormPolarQuotientEquiv lattice hunimodular).toEquiv
        (rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient lattice 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro vector _
      let lifted : Fin n → ℤ := fun index => (vector index).val
      have hcast : (fun index => (lifted index : R2)) = vector := by
        funext index
        dsimp [lifted]
        exact_mod_cast ZMod.natCast_zmod_val (vector index)
      change _ = quarticPhase (-(lattice.quadForm lifted : R4))
      rw [← hcast, binaryFormPolarQuotientEquiv_intCast,
        polarQuotientPhase_pairingMatrix_intCast lattice hunimodular]

theorem matrixNorm_integral {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n) (vector : Fin n → ℤ) :
    matrixNorm ((lattice.pairingMatrix.map (Int.cast : ℤ → R8)).map modFour)
      (fun index => (vector index : R4)) = (lattice.quadForm vector : R4) := by
  rw [lattice.quadForm_eq_dotProduct]
  simp [matrixNorm, Matrix.mulVec, dotProduct]

theorem binaryMatrixGauss_integral {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n) :
    binaryMatrixGauss (lattice.pairingMatrix.map (Int.cast : ℤ → R8)) =
      ∑ vector : Fin n → R2,
        quarticPhase (lattice.quadForm (fun index => (vector index).val) : R4) := by
  unfold binaryMatrixGauss
  apply Finset.sum_congr rfl
  intro vector _
  have hlift : (fun index => bitLift (vector index)) =
      fun index => (((vector index).val : ℤ) : R4) := by
    funext index
    simp [bitLift]
  rw [hlift, matrixNorm_integral]

theorem star_quarticPhase_neg (value : R4) :
    (starRingEnd ℂ) (quarticPhase (-value)) = quarticPhase value := by
  simp only [quarticPhase_eq_stdAddChar]
  have hchar : 0 < ringChar (ZMod 4) := by rw [ZMod.ringChar_zmod_n]; decide
  rw [AddChar.starComp_apply hchar]
  simp only [AddChar.inv_apply, neg_neg]

theorem unimodular_binaryGauss {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    binaryMatrixGauss (lattice.pairingMatrix.map (Int.cast : ℤ → R8)) =
      (1 + Complex.I) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [binaryMatrixGauss, matrixNorm, dotProduct, quarticPhase]
  have hdual := dualGaussIntegral_one_eq_binaryPhaseSum lattice hunimodular
  rw [dualGaussIntegral_one_of_unimodular lattice hn hunimodular] at hdual
  have hconjugate := congrArg (starRingEnd ℂ) hdual
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by simp
  simp only [map_pow, map_sub, map_one, hI, sub_neg_eq_add, map_sum,
    star_quarticPhase_neg] at hconjugate
  rw [binaryMatrixGauss_integral]
  exact hconjugate.symm

theorem normalizes_unimodular_of_diagonal_certificate (word : List R8)
    (lattice : PositiveDefiniteIntegralLattice word.length) (hunimodular : lattice.IsUnimodular)
    (certificate : TypeIIModEightCertificates.GramCongruenceCertificate
      (lattice.pairingMatrix.map (Int.cast : ℤ → R8)) (wordMatrix word)) :
    Normalizes (lattice.pairingMatrix.map (Int.cast : ℤ → R8)) := by
  have hdetGram : (lattice.pairingMatrix.map (Int.cast : ℤ → R8)).det = 1 := by
    have hdet : lattice.pairingMatrix.det = 1 := hunimodular
    calc
      _ = (lattice.pairingMatrix.det : R8) := (Int.cast_det lattice.pairingMatrix).symm
      _ = 1 := by rw [hdet]; rfl
  have hdetWord : (wordMatrix word).det = 1 := certificate.det_eq.trans hdetGram
  have hunits : ∀ value ∈ word, IsUnit value := by
    apply List.prod_isUnit_iff.mp
    rw [← wordMatrix_det, hdetWord]
    exact isUnit_one
  have hsymm : (lattice.pairingMatrix.map (Int.cast : ℤ → R8)).IsSymm :=
    lattice.form_symm.map _
  have hphase : binaryWordGauss word = (1 + Complex.I) ^ word.length := by
    rw [← binaryMatrixGauss_wordMatrix,
      ← binaryMatrixGauss_eq_of_certificate hsymm certificate]
    exact unimodular_binaryGauss lattice hunimodular
  exact normalizes_of_certificate certificate
    (normalizes_word_of_units_det_binaryGauss word hunits hdetWord hphase)

#assert_standard_axioms binaryFormPolarQuotientEquiv
#assert_standard_axioms polarQuotientPhase_pairingMatrix_intCast
#assert_standard_axioms dualGaussIntegral_one_eq_binaryPhaseSum
#assert_standard_axioms unimodular_binaryGauss
#assert_standard_axioms normalizes_unimodular_of_diagonal_certificate

end UnimodularGenusClosure
