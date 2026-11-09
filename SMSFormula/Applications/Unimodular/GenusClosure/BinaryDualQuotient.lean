import SMSFormula.Applications.Unimodular.GenusClosure.GaussSpecialization

noncomputable section

namespace UnimodularGenusClosure
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped BigOperators

def integralMatrixAction {n : ℕ} (matrix : Matrix (Fin n) (Fin n) ℤ)
    (vector : Fin n → IntegralFiniteAdele) : Fin n → IntegralFiniteAdele :=
  fun index => ∑ col, matrix index col • vector col

theorem integralMatrixAction_mul {n : ℕ} (left right : Matrix (Fin n) (Fin n) ℤ)
    (vector : Fin n → IntegralFiniteAdele) :
    integralMatrixAction left (integralMatrixAction right vector) =
      integralMatrixAction (left * right) vector := by
  funext index
  simp only [integralMatrixAction, Matrix.mul_apply, Finset.smul_sum,
    smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem integralMatrixAction_one {n : ℕ} (vector : Fin n → IntegralFiniteAdele) :
    integralMatrixAction 1 vector = vector := by
  funext index
  simp [integralMatrixAction, Matrix.one_apply]

theorem integralMatrixAction_surjective {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    Function.Surjective (integralMatrixAction lattice.pairingMatrix) := by
  intro vector
  refine ⟨integralMatrixAction lattice.pairingMatrix.adjugate vector, ?_⟩
  have hdet : lattice.pairingMatrix.det = 1 := hunimodular
  rw [integralMatrixAction_mul, Matrix.mul_adjugate, hdet, one_smul,
    integralMatrixAction_one]

theorem coordinateDilation_one (n : ℕ) (vector : Fin n → IntegralFiniteAdele) :
    integralFiniteAdeleCoordinateNatDilation n 1 vector = vector := by
  funext index
  apply Subtype.ext
  simp [integralFiniteAdeleCoordinateNatDilation, integralFiniteAdeleNatDilation]

theorem integralPolarMatrixEnd_eq_action {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (vector : Fin n → IntegralFiniteAdele) :
    integralFiniteAdelePolarMatrixEnd lattice vector =
      integralMatrixAction lattice.polarGramMatrix vector := by
  funext index
  apply Subtype.ext
  change lattice.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
      (fun index => (vector index : RationalFiniteAdele)) index = _
  rw [lattice.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix]
  simp [integralMatrixAction, Matrix.mulVec, dotProduct, zsmul_eq_mul]

theorem integralMatrixAction_gram {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (vector : Fin n → IntegralFiniteAdele) :
    integralMatrixAction lattice.polarGramMatrix vector =
      integralFiniteAdeleCoordinateNatDilation n 2
        (integralMatrixAction lattice.pairingMatrix vector) := by
  funext index
  apply Subtype.ext
  simp [integralMatrixAction, lattice.polarGramMatrix_eq_two_smul_pairingMatrix,
    integralFiniteAdeleCoordinateNatDilation,
    integralFiniteAdeleNatDilation, nsmul_eq_mul, zsmul_eq_mul, Finset.mul_sum, mul_assoc]

theorem polarDenDilation_one_eq_two_range {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    integralFiniteAdelePolarDenDilationAddSubgroup lattice 1 =
      (integralFiniteAdeleCoordinateNatDilation n 2).range := by
  ext vector
  change (∃ preimage, integralFiniteAdelePolarMatrixEnd lattice
      (integralFiniteAdeleCoordinateNatDilation n 1 preimage) = vector) ↔
    ∃ preimage, integralFiniteAdeleCoordinateNatDilation n 2 preimage = vector
  simp only [coordinateDilation_one, integralPolarMatrixEnd_eq_action,
    integralMatrixAction_gram]
  constructor
  · rintro ⟨preimage, heq⟩
    exact ⟨integralMatrixAction lattice.pairingMatrix preimage, heq⟩
  · rintro ⟨preimage, heq⟩
    obtain ⟨lift, hlift⟩ := integralMatrixAction_surjective lattice hunimodular preimage
    exact ⟨lift, by rw [hlift]; exact heq⟩

def binaryPolarQuotientEquiv {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    (Fin n → R2) ≃+ ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup lattice 1) :=
  (coordinateResidueEquivIntegralFiniteAdeleModDilation n 2 (by decide)).trans
    (QuotientAddGroup.quotientAddEquivOfEq
      (polarDenDilation_one_eq_two_range lattice hunimodular).symm)

theorem binaryPolarQuotientEquiv_intCast {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) (vector : Fin n → ℤ) :
    binaryPolarQuotientEquiv lattice hunimodular (fun index => (vector index : R2)) =
      (fun index => integerToIntegralFiniteAdele (vector index) :
        (Fin n → IntegralFiniteAdele) ⧸
          integralFiniteAdelePolarDenDilationAddSubgroup lattice 1) := by
  rw [binaryPolarQuotientEquiv, AddEquiv.trans_apply,
    coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
  rfl

theorem dualGaussIntegral_one_eq_binaryQuotientSum {n : ℕ} (lattice : PositiveDefiniteIntegralLattice n)
    (hunimodular : lattice.IsUnimodular) :
    lattice.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral 1 =
      ∑ vector : Fin n → R2,
        rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient lattice 1
          (binaryPolarQuotientEquiv lattice hunimodular vector) := by
  rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarMatrixQuotientSum]
  simpa using (Equiv.sum_comp (binaryPolarQuotientEquiv lattice hunimodular).toEquiv
    (rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient lattice 1)).symm

#assert_standard_axioms integralMatrixAction_surjective
#assert_standard_axioms polarDenDilation_one_eq_two_range
#assert_standard_axioms binaryPolarQuotientEquiv
#assert_standard_axioms binaryPolarQuotientEquiv_intCast
#assert_standard_axioms dualGaussIntegral_one_eq_binaryQuotientSum

end UnimodularGenusClosure
