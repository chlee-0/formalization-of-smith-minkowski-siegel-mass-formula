import SMSFormula.Applications.Unimodular.PadicLifting.DyadicClassification
import SMSFormula.FiniteOrthogonalGroupStandardModelTransport

noncomputable section

namespace UnimodularPadicLift

theorem finiteField_det_one_normalizer {field : Type*} [Field field] [Fintype field]
    (hchar : ringChar field ≠ 2) {rank : ℕ}
    (gram : Matrix (Fin rank) (Fin rank) field) (hsymm : gram.IsSymm) (hdet : gram.det = 1) :
    ∃ change : (Matrix (Fin rank) (Fin rank) field)ˣ,
      (change : Matrix _ _ field).transpose * gram * (change : Matrix _ _ field) = 1 := by
  cases rank with
  | zero =>
    refine ⟨1, ?_⟩
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    ext row col
    exact Fin.elim0 row
  | succ rank =>
    obtain ⟨weight, root, basis, hweight, hroot, hcongr, hsquare⟩ :=
      PositiveDefiniteIntegralLattice.exists_congr_finSuccIdentityGramMatrix_with_det_square rank hchar gram
        hsymm (hdet.trans_ne one_ne_zero)
    let scale : Matrix (Fin (rank + 1)) (Fin (rank + 1)) field :=
      Matrix.diagonal (Fin.cases root⁻¹ (fun _ => 1))
    let inverse : Matrix (Fin (rank + 1)) (Fin (rank + 1)) field :=
      Matrix.diagonal (Fin.cases root (fun _ => 1))
    have hright : scale * inverse = 1 := by
      ext row col
      refine Fin.cases ?_ (fun row => ?_) row <;> refine Fin.cases ?_ (fun col => ?_) col <;>
        simp [scale, inverse, Matrix.diagonal_apply,
          Matrix.one_apply, Fin.ext_iff, hroot]
    have hleft : inverse * scale = 1 := by
      ext row col
      refine Fin.cases ?_ (fun row => ?_) row <;> refine Fin.cases ?_ (fun col => ?_) col <;>
        simp [scale, inverse, Matrix.diagonal_apply,
          Matrix.one_apply, Fin.ext_iff, hroot]
    let unitScale : (Matrix (Fin (rank + 1)) (Fin (rank + 1)) field)ˣ :=
      ⟨scale, inverse, hright, hleft⟩
    have hscaled : scale.transpose *
        PositiveDefiniteIntegralLattice.finSuccIdentityGramMatrix (n := rank) weight * scale = 1 := by
      have hdiagonal : PositiveDefiniteIntegralLattice.finSuccIdentityGramMatrix (n := rank) weight =
          Matrix.diagonal (Fin.cases weight (fun _ : Fin rank => 1)) := by
        ext row col
        refine Fin.cases ?_ (fun row => ?_) row <;> refine Fin.cases ?_ (fun col => ?_) col <;>
          simp [PositiveDefiniteIntegralLattice.finSuccIdentityGramMatrix, PositiveDefiniteIntegralLattice.finSuccGramBlock,
            Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff]
      rw [hdiagonal]
      ext row col
      refine Fin.cases ?_ (fun row => ?_) row <;> refine Fin.cases ?_ (fun col => ?_) col <;>
        simp [scale, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff,
          hsquare, hdet, hroot, pow_two]
    refine ⟨basis * unitScale, ?_⟩
    change ((basis : Matrix _ _ field) * scale).transpose * gram *
      ((basis : Matrix _ _ field) * scale) = 1
    calc
      _ = scale.transpose * ((basis : Matrix _ _ field).transpose * gram *
          (basis : Matrix _ _ field)) * scale := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hcongr]; exact hscaled

theorem finiteField_det_one_congruence {field : Type*} [Field field] [Fintype field]
    (hchar : ringChar field ≠ 2) {rank : ℕ}
    (gram target : Matrix (Fin rank) (Fin rank) field)
    (hgramSymm : gram.IsSymm) (htargetSymm : target.IsSymm)
    (hgramDet : gram.det = 1) (htargetDet : target.det = 1) :
    ∃ change : (Matrix (Fin rank) (Fin rank) field)ˣ,
      (change : Matrix _ _ field).transpose * gram * (change : Matrix _ _ field) = target := by
  obtain ⟨left, hleft⟩ := finiteField_det_one_normalizer hchar gram hgramSymm hgramDet
  obtain ⟨right, hright⟩ := finiteField_det_one_normalizer hchar target htargetSymm htargetDet
  let inverse : Matrix (Fin rank) (Fin rank) field := ↑(right⁻¹)
  have hinverse : (right : Matrix _ _ field) * inverse = 1 := by simp [inverse]
  refine ⟨left * right⁻¹, ?_⟩
  change ((left : Matrix _ _ field) * inverse).transpose * gram *
    ((left : Matrix _ _ field) * inverse) = target
  calc
    _ = inverse.transpose *
        ((left : Matrix _ _ field).transpose * gram * (left : Matrix _ _ field)) *
          inverse := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = inverse.transpose * 1 * inverse := by rw [hleft]
    _ = inverse.transpose *
        ((right : Matrix _ _ field).transpose * target * (right : Matrix _ _ field)) *
          inverse := by rw [hright]
    _ = ((right : Matrix _ _ field) * inverse).transpose * target *
        ((right : Matrix _ _ field) * inverse) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = target := by rw [hinverse]; simp

end UnimodularPadicLift

namespace PositiveDefiniteIntegralLattice
open UnimodularPadicLift

theorem isLocallyIsometricAt_odd_prime_of_unimodular {rank : ℕ}
    (lattice reference : PositiveDefiniteIntegralLattice rank)
    (hlattice : lattice.IsUnimodular) (hreference : reference.IsUnimodular)
    (prime : ℕ) [Fact prime.Prime] (hodd : prime ≠ 2) :
    lattice.IsLocallyIsometricAt reference prime := by
  letI : Fact (prime ^ 1).Prime := ⟨by simpa using (Fact.out : prime.Prime)⟩
  have hchar : ringChar (ZMod (prime ^ 1)) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n, pow_one] using hodd
  have det_one (model : PositiveDefiniteIntegralLattice rank) (hmodel : model.IsUnimodular) :
      ((model.pairingMatrix_padic prime).map (PadicInt.toZModPow 1)).det = 1 := by
    have hdet : (model.pairingMatrix_padic prime).det = 1 := by
      change (model.pairingMatrix.map (Int.cast : ℤ → ℤ_[prime])).det = 1
      rw [← Int.cast_det, show model.pairingMatrix.det = 1 from hmodel]
      simp
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, map_one] using
      congrArg (PadicInt.toZModPow 1) hdet
  obtain ⟨change, hcongr⟩ := finiteField_det_one_congruence hchar
    ((reference.pairingMatrix_padic prime).map (PadicInt.toZModPow 1))
    ((lattice.pairingMatrix_padic prime).map (PadicInt.toZModPow 1))
    ((reference.form_symm.map _).map _) ((lattice.form_symm.map _).map _)
    (det_one reference hreference) (det_one lattice hlattice)
  exact exists_odd_prime_unit_isometry_of_residue_congruence hodd
    (reference.pairingMatrix_padic prime) (lattice.pairingMatrix_padic prime)
    (reference.form_symm.map _) (lattice.form_symm.map _)
    (pairingMatrix_padic_isUnit_of_unimodular reference hreference prime)
    change (↑change⁻¹) hcongr (by simp)

#assert_standard_axioms UnimodularPadicLift.finiteField_det_one_normalizer
#assert_standard_axioms UnimodularPadicLift.finiteField_det_one_congruence
#assert_standard_axioms isLocallyIsometricAt_odd_prime_of_unimodular

end PositiveDefiniteIntegralLattice
