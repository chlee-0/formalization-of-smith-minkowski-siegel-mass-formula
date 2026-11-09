import SMSFormula.Applications.Unimodular.PadicLifting.IntegralMatrixLift
import SMSFormula.Applications.Unimodular.ModEightTransport.FiniteCertificates

noncomputable section

namespace UnimodularPadicLift

variable {p n : ℕ} [Fact p.Prime]

theorem matrix_isUnit_of_unit_reduction_det (precision : ℕ) (hprecision : 0 < precision)
    (matrix : Mat p n)
    (hdet : IsUnit (matrix.map (PadicInt.toZModPow precision)).det) : IsUnit matrix := by
  letI : Fact (p ^ 1).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  apply (Matrix.isUnit_iff_isUnit_det matrix).mpr
  have hfinite : IsUnit (PadicInt.toZModPow precision matrix.det) := by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hdet
  let reduction : ZMod (p ^ precision) →+* ZMod (p ^ 1) :=
    ZMod.castHom (pow_dvd_pow p (by omega : 1 ≤ precision)) _
  have hunit : IsUnit (PadicInt.toZModPow 1 matrix.det) := by
    have hmap := hfinite.map reduction
    change IsUnit ((reduction.comp (PadicInt.toZModPow precision)) matrix.det) at hmap
    rw [show reduction.comp (PadicInt.toZModPow precision) = PadicInt.toZModPow 1 from
      PadicInt.zmod_cast_comp_toZModPow 1 precision (by omega)] at hmap
    exact hmap
  by_contra hnot
  have hzero : PadicInt.toZModPow 1 matrix.det = 0 := by
    change matrix.det ∈ RingHom.ker (PadicInt.toZModPow 1)
    rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
      IsLocalRing.mem_maximalIdeal]
    exact hnot
  exact (isUnit_iff_ne_zero.mp hunit) hzero

def residueMatrixLift (precision : ℕ)
    (matrix : Matrix (Fin n) (Fin n) (ZMod (p ^ precision))) : Mat p n :=
  matrix.map (fun value => (value.val : ℤ_[p]))

theorem residueMatrixLift_reduces (precision : ℕ)
    (matrix : Matrix (Fin n) (Fin n) (ZMod (p ^ precision))) :
    (residueMatrixLift precision matrix).map (PadicInt.toZModPow precision) = matrix := by
  ext row col
  simp [residueMatrixLift]

theorem powDiv_of_reduction_zero (precision : ℕ) (matrix : Mat p n)
    (hzero : matrix.map (PadicInt.toZModPow precision) = 0) : PowDiv precision matrix := by
  intro row col
  apply Ideal.mem_span_singleton.mp
  rw [← PadicInt.ker_toZModPow]
  change PadicInt.toZModPow precision (matrix row col) = 0
  exact congrFun (congrFun hzero row) col

theorem exists_unit_isometry_of_residue_congruence (precision : ℕ)
    (hprecision : 0 < precision) (hthreshold : 4 * (p : ℤ_[p]) ∣ (p : ℤ_[p]) ^ precision)
    (gram target : Mat p n) (hgramSymm : gram.IsSymm) (htargetSymm : target.IsSymm)
    (hgram : IsUnit gram)
    (change inverse : Matrix (Fin n) (Fin n) (ZMod (p ^ precision)))
    (hcongr : change.transpose * gram.map (PadicInt.toZModPow precision) * change =
      target.map (PadicInt.toZModPow precision))
    (hinverse : change * inverse = 1) :
    ∃ lifted : Mat p n, IsUnit lifted ∧ lifted.transpose * gram * lifted = target := by
  let initial := residueMatrixLift precision change
  have hreduce : initial.map (PadicInt.toZModPow precision) = change :=
    residueMatrixLift_reduces precision change
  have hchangeDet : IsUnit change.det := by
    apply IsUnit.of_mul_eq_one inverse.det
    simp only [← Matrix.det_mul, hinverse, Matrix.det_one]
  have hinitial : IsUnit initial := matrix_isUnit_of_unit_reduction_det precision hprecision
    initial (hreduce ▸ hchangeDet)
  let current := initial.transpose * gram * initial
  have hcurrentSymm : current.IsSymm := by
    change (initial.transpose * gram * initial).transpose = initial.transpose * gram * initial
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hgramSymm.eq, Matrix.mul_assoc]
  have hcurrent : IsUnit current := by
    apply (Matrix.isUnit_iff_isUnit_det current).mpr
    dsimp [current]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det initial).mp hinitial).mul
      ((Matrix.isUnit_iff_isUnit_det gram).mp hgram) |>.mul
      ((Matrix.isUnit_iff_isUnit_det initial).mp hinitial)
  have herror : PowDiv precision (target - current) := by
    apply powDiv_of_reduction_zero
    have hcurrentReduce : current.map (PadicInt.toZModPow precision) =
        target.map (PadicInt.toZModPow precision) := by
      dsimp [current]
      rw [Matrix.map_mul, Matrix.map_mul]
      change (initial.map (PadicInt.toZModPow precision)).transpose *
        gram.map (PadicInt.toZModPow precision) * initial.map (PadicInt.toZModPow precision) = _
      rw [hreduce, hcongr]
    ext row col
    change PadicInt.toZModPow precision (target row col - current row col) = 0
    rw [map_sub, show PadicInt.toZModPow precision (current row col) =
      PadicInt.toZModPow precision (target row col) from
        congrFun (congrFun hcurrentReduce row) col, sub_self]
  obtain ⟨correction, hcorrection, hexact⟩ := exists_unit_isometry_of_four_prime_dvd
    current target hcurrentSymm htargetSymm hcurrent
    (fun row col => dvd_trans hthreshold (herror row col))
  refine ⟨initial * correction, hinitial.mul hcorrection, ?_⟩
  simpa only [current, Matrix.transpose_mul, Matrix.mul_assoc] using hexact

theorem exists_dyadic_unit_isometry_of_gram_certificate (gram target : Mat 2 n)
    (hgramSymm : gram.IsSymm) (htargetSymm : target.IsSymm) (hgram : IsUnit gram)
    (certificate : TypeIIModEightCertificates.GramCongruenceCertificate
      (gram.map (PadicInt.toZModPow 3)) (target.map (PadicInt.toZModPow 3))) :
    ∃ lifted : Mat 2 n, IsUnit lifted ∧ lifted.transpose * gram * lifted = target := by
  exact exists_unit_isometry_of_residue_congruence 3 (by omega) (by norm_num)
    gram target hgramSymm htargetSymm hgram certificate.changeMatrix certificate.inverseMatrix
    certificate.congruence certificate.mul_inverse

theorem four_prime_dvd_prime_of_ne_two (hodd : p ≠ 2) :
    4 * (p : ℤ_[p]) ∣ (p : ℤ_[p]) := by
  have hcoprime : p.Coprime 4 := by
    have htwo := (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hodd
    simpa using htwo.pow_right 2
  have hfour : IsUnit (4 : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcoprime)
  simpa using mul_dvd_mul (isUnit_iff_dvd_one.mp hfour) (dvd_refl (p : ℤ_[p]))

theorem exists_odd_prime_unit_isometry_of_residue_congruence (hodd : p ≠ 2)
    (gram target : Mat p n) (hgramSymm : gram.IsSymm) (htargetSymm : target.IsSymm)
    (hgram : IsUnit gram)
    (change inverse : Matrix (Fin n) (Fin n) (ZMod (p ^ 1)))
    (hcongr : change.transpose * gram.map (PadicInt.toZModPow 1) * change =
      target.map (PadicInt.toZModPow 1)) (hinverse : change * inverse = 1) :
    ∃ lifted : Mat p n, IsUnit lifted ∧ lifted.transpose * gram * lifted = target :=
  exists_unit_isometry_of_residue_congruence 1 (by omega)
    (by simpa using four_prime_dvd_prime_of_ne_two hodd)
    gram target hgramSymm htargetSymm hgram change inverse hcongr hinverse

#assert_standard_axioms matrix_isUnit_of_unit_reduction_det
#assert_standard_axioms exists_unit_isometry_of_residue_congruence
#assert_standard_axioms exists_dyadic_unit_isometry_of_gram_certificate
#assert_standard_axioms exists_odd_prime_unit_isometry_of_residue_congruence

end UnimodularPadicLift
