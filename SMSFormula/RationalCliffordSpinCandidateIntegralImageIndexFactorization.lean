import SMSFormula.RationalCliffordSpinCandidateIntegralFiniteSheetHaar

/-!
# Factoring the integral Spin image index

The integral Spin image is contained in the kernel of the restricted p-adic
spinor norm.  This file inserts that intermediate subgroup into the local
image index.  The result is the exact factorization

```text
integral image index = lifting defect * restricted spinor-range degree.
```

The lifting defect is the relative index of the integral image in the
restricted spinor kernel.  It is one exactly when the
integral lifting predicate holds.  The second factor is the cardinality of
the restricted spinor-norm range.  Both factors are positive and the
range is finite, but neither factor is evaluated here.

Combining the factorization with the two-sheet Haar calculation
gives an exact three-factor local volume identity.  Conditional equality of
the Spin and `SO` integral volumes then requires the two independent
arithmetic statements: integral lifting and spinor-range degree two.  Kernel
degree two alone proves neither one.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

local instance integralImageIndexFactorizationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The two arithmetic factors -/

/-- Cardinality of the actual restricted integral spinor-norm range. -/
def heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℕ :=
  Nat.card (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v).range

/-- Relative index of the actual integral Spin image inside the restricted
integral spinor-norm kernel. -/
def heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) : ℕ :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range.relIndex
    (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).ker

/-- Exact subgroup-index factorization through the restricted spinor kernel. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v =
      V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v *
        V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 := by
  simpa [heightOnePadicCliffordSpinCandidateIntegralImageIndex,
    heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex,
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree,
    Subgroup.index_ker] using
    (Subgroup.relIndex_mul_index
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range_le_spinorNorm_ker
        S v)).symm

/-- The lifting defect is one exactly when every integral point of trivial
spinor norm has an integral Clifford--Spin lift. -/
theorem
    cliffordSpinCandidateIntegralLiftingAt_iff_liftingDefectIndex_eq_one
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.CliffordSpinCandidateIntegralLiftingAt S v ↔
      V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v = 1 := by
  constructor
  · intro h
    rw [heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex,
      Subgroup.relIndex_eq_one]
    simpa [CliffordSpinCandidateIntegralLiftingAt] using h.ge
  · intro h
    apply le_antisymm
    · exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range_le_spinorNorm_ker
          S v
    · exact (Subgroup.relIndex_eq_one.mp (by
        simpa [heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex]
          using h))

/-- The restricted integral spinor-norm range degree is positive. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 < V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 := by
  have hprod :
      0 < V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v *
        V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 := by
    rw [←
      V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
        S v]
    exact V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_pos S v
  exact Nat.pos_of_mul_pos_left hprod

/-- The actual restricted integral spinor-norm range is finite. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRange_finite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Finite
      (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).range := by
  exact (Nat.card_pos_iff.mp (by
    simpa [heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree] using
      V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_pos S v)).2

/-- The integral lifting-defect index is positive. -/
theorem heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex_pos
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    0 < V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v := by
  have hprod :
      0 < V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v *
        V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 := by
    rw [←
      V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
        S v]
    exact V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_pos S v
  exact Nat.pos_of_mul_pos_right hprod

/-- There is no hidden lifting defect exactly when the full image index is the
cardinality of the restricted spinor-norm range. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_spinorRangeDegree_iff_lifting
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v =
        V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 ↔
      V.CliffordSpinCandidateIntegralLiftingAt S v := by
  constructor
  · intro h
    apply
      (V.cliffordSpinCandidateIntegralLiftingAt_iff_liftingDefectIndex_eq_one
        S v).2
    apply Nat.eq_of_mul_eq_mul_right
      (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_pos S v)
    rw [←
      V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
        S v,
      h, one_mul]
  · intro h
    rw [
      V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
        S v,
      (V.cliffordSpinCandidateIntegralLiftingAt_iff_liftingDefectIndex_eq_one
        S v).1 h,
      one_mul]

/-! ## Exact and conditional volume consequences -/

/-- The local two-sheet identity with the image index split into its exact
lifting-defect and spinor-range factors. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_liftingDefect_mul_spinorRangeDegree
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.heightOnePadicCliffordSpinCandidateIntegralLiftingDefectIndex S v : ℝ≥0∞) *
          (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 : ℝ≥0∞) *
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      (2 : ℝ≥0∞) *
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  rw [← Nat.cast_mul, ←
    V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_liftingDefect_mul_spinorRangeDegree
      S v]
  exact
    V.heightOnePadicCliffordSpinCandidateIntegralVolume_index_mul_eq_two_mul_soIntegralVolume
      S v

/-- Integral lifting together with a two-element restricted spinor range
evaluates the actual integral image index as two. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_two_of_lifting_of_spinorRangeDegree_eq_two
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hlift : V.CliffordSpinCandidateIntegralLiftingAt S v)
    (hrange :
      V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 = 2) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v = 2 := by
  exact
    ((V.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_spinorRangeDegree_iff_lifting
      S v).2 hlift).trans hrange

/-- Under the two independent good-place arithmetic inputs, the completed
Spin and `SO` integral differential Haar volumes agree exactly. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_lifting_of_spinorRangeDegree_eq_two
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hlift : V.CliffordSpinCandidateIntegralLiftingAt S v)
    (hrange :
      V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1 = 2) :
    V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  have h :=
    V.heightOnePadicCliffordSpinCandidateIntegralVolume_liftingDefect_mul_spinorRangeDegree
      S v
  rw [
    (V.cliffordSpinCandidateIntegralLiftingAt_iff_liftingDefectIndex_eq_one
      S v).1 hlift,
    hrange] at h
  norm_num only [Nat.cast_ofNat, one_mul] at h
  have h' :
      V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 *
          (2 : ℝ≥0∞) =
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 * 2 := by
    simpa [mul_comm] using h
  exact (ENNReal.mul_left_inj (by norm_num) (by norm_num)).mp h'

end RationalQuadraticSpaceMatrix
