import SMSFormula.RationalSpecialOrthogonalNormalizedOrdinaryMassEvaluation
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
import SMSFormula.SpecialOrthogonalRealLatticeDifferentialMass
import SMSFormula.Product

/-!
# Reduce the mass product side to global differential normalization

The corrected evaluated ordinary-mass theorem gives the inverse real
differential mass times the finite stabilizer inverse volume.  The classical
Schulze--Pillot product side gives the archimedean factor times the cutoff
limit `P`.  This module rewrites the latter in `ENNReal` and uses the
definition of the finite differential stabilizer inverse volume to cancel
that common scale safely.

The corrected ordinary-mass equivalence reduces the comparison to a global
product-formula statement: real differential mass times the archimedean factor
and the finite local-correction product equals one.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The real Schulze--Pillot product side maps to the literal product of its
positive archimedean factor and cutoff limit. -/
theorem ENNReal_ofReal_massFormulaProductSide
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    ENNReal.ofReal (massFormulaProductSide L P) =
      ENNReal.ofReal (archimedeanMassFactor n) *
        ENNReal.ofReal P := by
  unfold massFormulaProductSide
  rw [ENNReal.ofReal_mul (archimedeanMassFactor_pos n).le]

/-- The cutoff limit is the local-correction product times the named finite
inverse volume.  Cancellation uses only the proved nonzero finite correction
product. -/
theorem ENNReal_ofReal_eq_localCorrectionFiniteProduct_mul_finiteStabilizerInverseVolume
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    ENNReal.ofReal P =
      L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct *
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
          P := by
  let C : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let p : ℝ≥0∞ := ENNReal.ofReal P
  change p = C * (C⁻¹ * p)
  calc
    p = 1 * p := by rw [one_mul]
    _ = (C * C⁻¹) * p := by
      rw [ENNReal.mul_inv_cancel
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_zero
        L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct_ne_top]
    _ = C * (C⁻¹ * p) := by rw [mul_assoc]

/-- The desired product-side comparison is equivalent to one exact global
real/finite differential normalization identity. -/
theorem ENNReal_ofReal_massFormulaProductSide_eq_inv_realDifferentialMass_iff
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (massFormulaProductSide L P) =
        (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ ↔
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  let R : ℝ≥0∞ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ
  let A : ℝ≥0∞ := ENNReal.ofReal (archimedeanMassFactor n)
  let C : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let p : ℝ≥0∞ := ENNReal.ofReal P
  let I : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  have hR0 : R ≠ 0 :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  have hRtop : R ≠ ⊤ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  have hI0 : I ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
      hP
  have hItop : I ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
      P
  have hp : p = C * I := by
    exact
      L.ENNReal_ofReal_eq_localCorrectionFiniteProduct_mul_finiteStabilizerInverseVolume
        P
  have hproduct :
      ENNReal.ofReal (massFormulaProductSide L P) = A * p := by
    exact L.ENNReal_ofReal_massFormulaProductSide P
  rw [hproduct,
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_eq_inv_inverseVolume]
  change A * p = R⁻¹ ↔ R * (A * C) = I⁻¹
  constructor
  · intro h
    have hcore : A * (C * I) = R⁻¹ := by
      rw [← hp]
      exact h
    have hunit : (R * (A * C)) * I = 1 := by
      calc
        (R * (A * C)) * I = R * (A * (C * I)) := by ac_rfl
        _ = R * R⁻¹ := by rw [hcore]
        _ = 1 := ENNReal.mul_inv_cancel hR0 hRtop
    calc
      R * (A * C) = (R * (A * C)) * 1 := by rw [mul_one]
      _ = (R * (A * C)) * (I * I⁻¹) := by
        rw [ENNReal.mul_inv_cancel hI0 hItop]
      _ = ((R * (A * C)) * I) * I⁻¹ := by ac_rfl
      _ = I⁻¹ := by rw [hunit, one_mul]
  · intro h
    have hunit : (R * (A * C)) * I = 1 := by
      calc
        (R * (A * C)) * I = I⁻¹ * I := by rw [h]
        _ = 1 := ENNReal.inv_mul_cancel hI0 hItop
    have hcore : A * (C * I) = R⁻¹ := by
      calc
        A * (C * I) = 1 * (A * (C * I)) := by rw [one_mul]
        _ = (R⁻¹ * R) * (A * (C * I)) := by
          rw [ENNReal.inv_mul_cancel hR0 hRtop]
        _ = R⁻¹ * ((R * (A * C)) * I) := by ac_rfl
        _ = R⁻¹ := by rw [hunit, mul_one]
    rw [hp]
    exact hcore

/-- After positive rational diagonalization, the remaining global
normalization statement is literally the equality between the full
determinant-and-Gamma real product times the archimedean/local correction and
the finite differential stabilizer volume. -/
theorem
    exists_ENNReal_ofReal_massFormulaProductSide_eq_inv_realDifferentialMass_iff_detGamma_mul_archimedeanCorrection_eq_finiteVolume
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {P : ℝ} (hP : 0 < P) :
    ∃ (d : Fin n → ℚ) (W : GL (Fin n) ℚ)
        (hd : ∀ i, 0 < d i),
      Matrix.skewAdjointCongruenceForm L.rationalFormMatrix W =
        Matrix.diagonal d ∧
      (ENNReal.ofReal (massFormulaProductSide L P) =
          (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ ↔
        ((↑((Real.toNNReal
              |Matrix.skewAdjointRealCongruenceDetScalar
                L.rationalFormMatrix W|)⁻¹) : ℝ≥0∞) *
            ((↑((Real.toNNReal
                |positiveDiagonalSkewAdjointDetScalar d hd|)⁻¹) : ℝ≥0∞) *
              ((Real.toNNReal
                  |(identitySpecialOrthogonalFixedElementaryDetScalar n : ℝ)| :
                  ℝ≥0∞) *
                ENNReal.ofReal
                  ((2 : ℝ) ^ (n - 1) *
                      Real.pi ^
                        (((n - 1 : ℕ) : ℝ) *
                          (((n - 1 : ℕ) : ℝ) + 3) / 4) /
                    (∏ k ∈ Finset.range (n - 1),
                      Real.Gamma (((k + 2 : ℕ) : ℝ) / 2)))))) *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P) := by
  letI : NeZero n := ⟨by
    intro hn0
    subst n
    exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))⟩
  obtain ⟨d, W, hd, hdiag, hreal⟩ :=
    L.exists_concreteRealSpecialOrthogonalDifferentialMeasure_univ_eq_det_mul_gamma
  refine ⟨d, W, hd, hdiag, ?_⟩
  rw [← hreal]
  exact
    L.ENNReal_ofReal_massFormulaProductSide_eq_inv_realDifferentialMass_iff
      hP

/-- With the corrected raw Tamagawa normalization, the finite inverse-volume
factor occurs on both the ordinary-mass and product sides.  Safe cancellation
reduces their equality to a cutoff-independent unit normalization. -/
theorem ordinaryGenusMassENNReal_eq_ofReal_massFormulaProductSide_iff_globalDifferentialUnitNormalization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ENNReal.ofReal (((L.ordinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal (massFormulaProductSide L P) ↔
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
          (ENNReal.ofReal (archimedeanMassFactor n) *
            L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct) = 1 := by
  let R : ℝ≥0∞ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ
  let A : ℝ≥0∞ := ENNReal.ofReal (archimedeanMassFactor n)
  let C : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let p : ℝ≥0∞ := ENNReal.ofReal P
  let I : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  have hR0 : R ≠ 0 :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  have hRtop : R ≠ ⊤ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  have hI0 : I ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
      hP
  have hItop : I ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
      P
  have hp : p = C * I :=
    L.ENNReal_ofReal_eq_localCorrectionFiniteProduct_mul_finiteStabilizerInverseVolume
      P
  have hproduct :
      ENNReal.ofReal (massFormulaProductSide L P) = A * p :=
    L.ENNReal_ofReal_massFormulaProductSide P
  rw [L.ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume
    hn inst hP hconv, hproduct]
  change R⁻¹ * I = A * p ↔ R * (A * C) = 1
  rw [hp]
  constructor
  · intro h
    have hcore : R⁻¹ = A * C := by
      calc
        R⁻¹ = R⁻¹ * 1 := by rw [mul_one]
        _ = R⁻¹ * (I * I⁻¹) := by
          rw [ENNReal.mul_inv_cancel hI0 hItop]
        _ = (R⁻¹ * I) * I⁻¹ := by ac_rfl
        _ = (A * (C * I)) * I⁻¹ := by rw [h]
        _ = (A * C) * (I * I⁻¹) := by ac_rfl
        _ = A * C := by rw [ENNReal.mul_inv_cancel hI0 hItop, mul_one]
    calc
      R * (A * C) = R * R⁻¹ := by rw [hcore]
      _ = 1 := ENNReal.mul_inv_cancel hR0 hRtop
  · intro h
    have hcore : A * C = R⁻¹ := by
      calc
        A * C = 1 * (A * C) := by rw [one_mul]
        _ = (R⁻¹ * R) * (A * C) := by
          rw [ENNReal.inv_mul_cancel hR0 hRtop]
        _ = R⁻¹ * (R * (A * C)) := by ac_rfl
        _ = R⁻¹ := by rw [h, mul_one]
    calc
      R⁻¹ * I = (A * C) * I := by rw [hcore]
      _ = A * (C * I) := by ac_rfl

end PositiveDefiniteIntegralLattice
