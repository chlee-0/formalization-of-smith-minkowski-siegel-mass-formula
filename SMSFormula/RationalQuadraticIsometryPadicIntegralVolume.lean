import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralPadicGroupHaar
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization

/-!
# Integral special-orthogonal volumes under a rational isometry

Let `e : U → V` be a supplied rational quadratic isometry with matrix `M` (inverse `M⁻¹`).  The
transport `map φ_e μ_U = ‖c_e‖_p⁻¹ • μ_V` of the p-adic invariant-differential SO measures
(`map_rationalIsometryPadicInvariantDifferentialGroupMeasure`, `c_e` the rational tangent
determinant) specialises at every prime where `M` and `M⁻¹` are `p`-integral: conjugation by `M`
then maps the integral subgroup of `U` onto that of `V`, so

`vol_V(SO_V(ℤ_p)) = ‖c_e‖_p · vol_U(SO_U(ℤ_p))`.

This compares the integral volume of an ambient lattice with that of a congruent (block) form at
all primes where the congruence is integral in both directions.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {m : ℕ} (U V : RationalQuadraticSpaceMatrix (m + 1))
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance ipvPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem matrix_mul_mem_padicIntSubring {k : ℕ} {p : ℕ} [Fact (Nat.Prime p)]
    {A B : Matrix (Fin k) (Fin k) ℚ_[p]} (hA : ∀ i j, A i j ∈ PadicInt.subring p)
    (hB : ∀ i j, B i j ∈ PadicInt.subring p) (i j : Fin k) :
    (A * B) i j ∈ PadicInt.subring p := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ ↦ Subring.mul_mem _ (hA i k) (hB k j)

/-- Conjugation by an integral matrix with integral inverse preserves integrality in both
directions. -/
theorem integral_conj_iff {k : ℕ} {p : ℕ} [Fact (Nat.Prime p)]
    {M N : Matrix (Fin k) (Fin k) ℚ_[p]} (_hMN : M * N = 1) (hNM : N * M = 1)
    (hM : ∀ i j, M i j ∈ PadicInt.subring p) (hN : ∀ i j, N i j ∈ PadicInt.subring p)
    (X : Matrix (Fin k) (Fin k) ℚ_[p]) :
    (∀ i j, (M * X * N) i j ∈ PadicInt.subring p) ↔ ∀ i j, X i j ∈ PadicInt.subring p := by
  constructor
  · intro h i j
    have hX : X = N * (M * X * N) * M := by
      rw [show N * (M * X * N) * M = (N * M) * X * (N * M) by simp only [Matrix.mul_assoc], hNM,
        Matrix.one_mul, Matrix.mul_one]
    rw [hX]
    exact matrix_mul_mem_padicIntSubring (matrix_mul_mem_padicIntSubring hN h) hM i j
  · intro h i j
    exact matrix_mul_mem_padicIntSubring (matrix_mul_mem_padicIntSubring hM h) hN i j

theorem padic_rationalIsometryMatrix_mul_inverseMatrix (p : ℕ) [Fact (Nat.Prime p)] :
    (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
        (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) = 1 := by
  rw [← Matrix.map_mul, rationalIsometryMatrix_mul_inverseMatrix]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem padic_rationalIsometryInverseMatrix_mul_matrix (p : ℕ) [Fact (Nat.Prime p)] :
    (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
        (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) = 1 := by
  rw [← Matrix.map_mul, rationalIsometryInverseMatrix_mul_matrix]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The inverse matrix of the transported group element is the conjugate of the inverse. -/
theorem coe_inv_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply
    (p : ℕ) [Fact (Nat.Prime p)] (g : U.specialOrthogonalMatrixGroup ℚ_[p]) :
    (((rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e ℚ_[p] g).1.1)⁻¹).1 =
      (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) * (g.1.1⁻¹).1 *
        (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply]
  calc (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) * g.1.1.1 *
          (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
        ((rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) * (g.1.1⁻¹).1 *
          (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p])) =
        (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p]) * (g.1.1.1 *
          (((rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) *
            (rationalIsometryMatrix U V e).map (algebraMap ℚ ℚ_[p])) * (g.1.1⁻¹).1)) *
          (rationalIsometryInverseMatrix U V e).map (algebraMap ℚ ℚ_[p]) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [padic_rationalIsometryInverseMatrix_mul_matrix, Matrix.one_mul, Units.mul_inv,
        Matrix.mul_one, padic_rationalIsometryMatrix_mul_inverseMatrix]

set_option backward.isDefEq.respectTransparency false in
/-- At a prime where the isometry matrix and its inverse are integral, the isometry transport maps
the integral subgroup of `U` onto that of `V`. -/
theorem rationalIsometry_mem_heightOneIntegralSubgroup_iff
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hM : ∀ i j, algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (rationalIsometryMatrix U V e i j) ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (hMinv : ∀ i j, algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (rationalIsometryInverseMatrix U V e i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (g : U.HeightOnePadicSpecialOrthogonalGroup v) :
    rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v ↔
      g ∈ U.heightOnePadicSpecialOrthogonalIntegralSubgroup v := by
  rw [mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic,
    mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic,
    coe_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply,
    coe_inv_rationalIsometryPadicSpecialOrthogonalGroupContinuousMulEquiv_apply,
    integral_conj_iff (padic_rationalIsometryMatrix_mul_inverseMatrix U V e _)
      (padic_rationalIsometryInverseMatrix_mul_matrix U V e _) (fun i j ↦ hM i j) (fun i j ↦ hMinv i j),
    integral_conj_iff (padic_rationalIsometryMatrix_mul_inverseMatrix U V e _)
      (padic_rationalIsometryInverseMatrix_mul_matrix U V e _) (fun i j ↦ hM i j) (fun i j ↦ hMinv i j)]

/-- The measure form of the transport on an open set and its preimage. -/
theorem padicInvariantDifferentialGroupMeasure_eq_of_rationalIsometry_preimage
    (p : ℕ) [Fact (Nat.Prime p)] (SU : Set (U.specialOrthogonalMatrixGroup ℚ_[p]))
    (SV : Set (V.specialOrthogonalMatrixGroup ℚ_[p])) (hSV : IsOpen SV)
    (hpre : rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e ℚ_[p] ⁻¹' SV = SU) :
    V.padicInvariantDifferentialGroupMeasure p SV =
      (‖algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e)‖₊ : ℝ≥0∞) *
        U.padicInvariantDifferentialGroupMeasure p SU := by
  have hc0 : ‖algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e)‖₊ ≠ 0 := by
    simp only [ne_eq, nnnorm_eq_zero, map_eq_zero]
    exact rationalIsometrySkewAdjointDetScalar_ne_zero U V e
  have hmap := map_rationalIsometryPadicInvariantDifferentialGroupMeasure U V e p
  have h1 := congrArg (fun μ ↦ μ SV) hmap
  simp only at h1
  rw [Measure.map_apply ?hf ?hs, hpre] at h1
  erw [Measure.smul_apply] at h1
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hc0] at h1
  case hf =>
    exact (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e _).continuous.borel_measurable
  case hs => exact MeasurableSpace.measurableSet_generateFrom hSV
  have h2 : U.padicInvariantDifferentialGroupMeasure p SU =
      (‖algebraMap ℚ ℚ_[p] (rationalIsometrySkewAdjointDetScalar U V e)‖₊ : ℝ≥0∞)⁻¹ *
        V.padicInvariantDifferentialGroupMeasure p SV := h1
  rw [h2, ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top,
    one_mul]

set_option maxHeartbeats 8000000 in
/-- Integral volumes under an integral isometry: `vol_V(SO_V(ℤ_p)) = ‖c_e‖_p · vol_U(SO_U(ℤ_p))`. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_eq_of_rationalIsometry
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hM : ∀ i j, algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (rationalIsometryMatrix U V e i j) ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (hMinv : ∀ i j, algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
      (rationalIsometryInverseMatrix U V e i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) :
    V.heightOnePadicSpecialOrthogonalIntegralVolume v =
      (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (rationalIsometrySkewAdjointDetScalar U V e)‖₊ : ℝ≥0∞) *
        U.heightOnePadicSpecialOrthogonalIntegralVolume v := by
  have hpre :
      rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ⁻¹'
        (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
          Set (V.HeightOnePadicSpecialOrthogonalGroup v)) =
        (U.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
          Set (U.HeightOnePadicSpecialOrthogonalGroup v)) := by
    ext g
    exact rationalIsometry_mem_heightOneIntegralSubgroup_iff U V e v hM hMinv g
  change V.padicInvariantDifferentialGroupMeasure
      (Rat.HeightOneSpectrum.primesEquiv v).1
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
        Set (V.HeightOnePadicSpecialOrthogonalGroup v)) = _
  exact padicInvariantDifferentialGroupMeasure_eq_of_rationalIsometry_preimage U V e
    (Rat.HeightOneSpectrum.primesEquiv v).1
    (U.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
      Set (U.HeightOnePadicSpecialOrthogonalGroup v))
    (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v :
      Set (V.HeightOnePadicSpecialOrthogonalGroup v))
    (isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup V v)
    hpre

end RationalQuadraticSpaceMatrix
