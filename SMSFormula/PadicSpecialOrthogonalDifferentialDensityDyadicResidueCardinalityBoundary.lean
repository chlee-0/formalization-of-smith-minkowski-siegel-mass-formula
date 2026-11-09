import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicFormCoordinateMass
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicGaugeBoundary
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceResidueCardinalityPrimePower

/-!
# The dyadic gauge identity as a natural residue-cardinality identity

The prescribed dyadic form-coordinate mass is transported to the
fixed-coordinate measure by the rational basis-comparison norm.  That same
finite nonzero norm is cancelled from the dyadic gauge identity.  The
remaining positive powers of two are then cancelled without passing through
`ENNReal.toReal`, leaving one natural-number cardinality identity.

This module proves only equivalences with that identity.  It does not prove
the identity or construct the required dyadic finite correspondence.
-/

noncomputable section

open Matrix
open scoped ENNReal Matrix NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem ennreal_eq_iff_mul_left_finite_dyadic
    {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    a = b ↔ c * a = c * b := by
  constructor
  · exact fun h ↦ congrArg (fun z : ℝ≥0∞ ↦ c * z) h
  · intro h
    calc
      a = 1 * a := (one_mul a).symm
      _ = (c⁻¹ * c) * a := by
        rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ * (c * a) := by rw [mul_assoc]
      _ = c⁻¹ * (c * b) := by rw [h]
      _ = (c⁻¹ * c) * b := by rw [mul_assoc]
      _ = 1 * b := by
        rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = b := one_mul b

private theorem ennreal_mul_inv_mul_eq_inv_mul_iff_dyadic
    {a b c p v : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    (a * (p * v)⁻¹) * b = p⁻¹ * c ↔ a * b = v * c := by
  have hpv0 : p * v ≠ 0 := mul_ne_zero hp0 hv0
  have hpvtop : p * v ≠ ⊤ := ENNReal.mul_ne_top hptop hvtop
  constructor
  · intro h
    calc
      a * b = ((a * (p * v)⁻¹) * b) * (p * v) := by
        rw [show ((a * (p * v)⁻¹) * b) * (p * v) =
            (a * b) * ((p * v)⁻¹ * (p * v)) by ac_rfl,
          ENNReal.inv_mul_cancel hpv0 hpvtop, mul_one]
      _ = (p⁻¹ * c) * (p * v) := by rw [h]
      _ = v * c := by
        rw [show (p⁻¹ * c) * (p * v) =
            (p⁻¹ * p) * (v * c) by ac_rfl,
          ENNReal.inv_mul_cancel hp0 hptop, one_mul]
  · intro h
    have hmul :
        ((a * (p * v)⁻¹) * b) * (p * v) =
          (p⁻¹ * c) * (p * v) := by
      calc
        ((a * (p * v)⁻¹) * b) * (p * v) = a * b := by
          rw [show ((a * (p * v)⁻¹) * b) * (p * v) =
              (a * b) * ((p * v)⁻¹ * (p * v)) by ac_rfl,
            ENNReal.inv_mul_cancel hpv0 hpvtop, mul_one]
        _ = v * c := h
        _ = (p⁻¹ * c) * (p * v) := by
          rw [show (p⁻¹ * c) * (p * v) =
              (p⁻¹ * p) * (v * c) by ac_rfl,
            ENNReal.inv_mul_cancel hp0 hptop, one_mul]
    calc
      (a * (p * v)⁻¹) * b =
          ((a * (p * v)⁻¹) * b) * 1 := (mul_one _).symm
      _ = ((a * (p * v)⁻¹) * b) * ((p * v) * (p * v)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hpv0 hpvtop]
      _ = ((a * (p * v)⁻¹) * b) * (p * v) * (p * v)⁻¹ := by
        rw [← mul_assoc]
      _ = (p⁻¹ * c) * (p * v) * (p * v)⁻¹ := by rw [hmul]
      _ = p⁻¹ * c := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hpv0 hpvtop, mul_one]

/-- On the dyadic density source, the fixed-coordinate measure is
the comparison norm times the explicit attained-residue mass. -/
theorem
    skewAdjointPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_residueImage_ncard_mul_inv_pow
    (L : PositiveDefiniteIntegralLattice n) :
    skewAdjointPadicCoordinateMeasure L.rationalFormMatrix 2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2) =
      L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
            2).ncard *
          ((2 : ℝ≥0∞) ^
            ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
                padicValInt 2 L.pairingDeterminant) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix)))⁻¹) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [
    L.skewAdjointPadicCoordinateMeasure_densityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_formCoordinateMeasure
      localPadicSpecialOrthogonalDifferentialDyadicPrime,
    L.skewAdjointFormElementaryPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_residueImage_ncard_mul_explicit]

/-- After inserting the dyadic residue mass, the dyadic gauge identity is
equivalent to the same ENNReal equality with the finite comparison norm
cancelled. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicResidueCoordinateMass
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime ↔
      (((((2 : ℝ≥0)⁻¹) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
            ℝ≥0) : ℝ≥0∞) *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              2).ncard *
            ((2 : ℝ≥0∞) ^
              ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
                  padicValInt 2 L.pairingDeterminant) *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        ((2 : ℝ≥0∞) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicCoordinateMass,
    L.skewAdjointPadicCoordinateMeasure_dyadicDensityCongruenceSourceAmbientSet_eq_comparisonNorm_mul_residueImage_ncard_mul_inv_pow]
  let c :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  let A : ℝ≥0∞ :=
    ((((2 : ℝ≥0)⁻¹) ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0) :
          ℝ≥0∞)
  let M : ℝ≥0∞ :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
        2).ncard *
      ((2 : ℝ≥0∞) ^
        ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
            padicValInt 2 L.pairingDeterminant) *
          Module.finrank ℚ
            (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹
  let O : ℝ≥0∞ :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let P : ℝ≥0∞ :=
    ((2 : ℝ≥0∞) ^
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹
  let Q : ℝ≥0∞ :=
    associatedBilinearDualQuotientCount L 2
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2)
  have hc0 : c ≠ 0 :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_zero
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  have hctop : c ≠ ⊤ :=
    L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime_ne_top
      localPadicSpecialOrthogonalDifferentialDyadicPrime
  change (A * (c * M)) * O = (P * c) * Q ↔
    (A * M) * O = P * Q
  constructor
  · intro h
    apply (ennreal_eq_iff_mul_left_finite_dyadic hc0 hctop).mpr
    calc
      c * ((A * M) * O) = (A * (c * M)) * O := by ac_rfl
      _ = (P * c) * Q := h
      _ = c * (P * Q) := by ac_rfl
  · intro h
    have hc : c * ((A * M) * O) = c * (P * Q) :=
      (ennreal_eq_iff_mul_left_finite_dyadic hc0 hctop).mp h
    calc
      (A * (c * M)) * O = c * ((A * M) * O) := by ac_rfl
      _ = c * (P * Q) := hc
      _ = (P * c) * Q := by ac_rfl

/-- The residual dyadic ENNReal coordinate-mass equality is equivalent to the
natural cardinality identity with the additional one-power Cayley loss made
literal in the exponent. -/
theorem
    dyadicResidueCoordinateMass_eq_iff_ncard_mul_natCard_eq_two_pow_succ_pairingDeterminantVal_mul_quotientCount
    (L : PositiveDefiniteIntegralLattice n) :
    (((((2 : ℝ≥0)⁻¹) ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) :
            ℝ≥0) : ℝ≥0∞) *
          ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
              2).ncard *
            ((2 : ℝ≥0∞) ^
              ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 +
                  padicValInt 2 L.pairingDeterminant) *
                Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹)) *
          (Nat.card
              (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
                2) : ℝ≥0∞) =
        ((2 : ℝ≥0∞) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)))⁻¹ *
          (associatedBilinearDualQuotientCount L 2
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                2) : ℝ≥0∞) ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              2) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 1) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let d :=
    Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let v := padicValInt 2 L.pairingDeterminant
  let N :=
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
      2).ncard
  let O :=
    Nat.card
      (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
        2)
  let Q :=
    associatedBilinearDualQuotientCount L 2 k
  let P : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (k * d)
  let V : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((v + 1) * d)
  have htwoA :
      (((((2 : ℝ≥0)⁻¹) ^ d : ℝ≥0) : ℝ≥0∞)) =
        ((2 : ℝ≥0∞) ^ d)⁻¹ := by
    change
      (↑(((2 : ℝ≥0)⁻¹) ^ d) : ℝ≥0∞) =
        (↑((2 : ℝ≥0) ^ d) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by positivity : (2 : ℝ≥0) ^ d ≠ 0)]
    congr 1
    exact inv_pow (2 : ℝ≥0) d
  have hpow :
      ((2 : ℝ≥0∞) ^ d) *
          ((2 : ℝ≥0∞) ^ (v * d)) = V := by
    dsimp only [V]
    rw [Nat.add_mul, one_mul, pow_add]
    ac_rfl
  have hP0 : P ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hPtop : P ≠ ⊤ := by
    exact ENNReal.pow_ne_top (by simp)
  have hV0 : V ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hVtop : V ≠ ⊤ := by
    exact ENNReal.pow_ne_top (by simp)
  have hVnat : V = ((2 ^ ((v + 1) * d) : ℕ) : ℝ≥0∞) := by
    dsimp only [V]
    norm_cast
  rw [htwoA]
  rw [Nat.add_mul, pow_add]
  change
    ((((2 : ℝ≥0∞) ^ d)⁻¹ *
          ((N : ℝ≥0∞) *
            (P * (2 : ℝ≥0∞) ^ (v * d))⁻¹)) *
        (O : ℝ≥0∞) =
      P⁻¹ * (Q : ℝ≥0∞)) ↔
      N * O = 2 ^ ((v + 1) * d) * Q
  have hnormalize :
      (((2 : ℝ≥0∞) ^ d)⁻¹ *
          ((N : ℝ≥0∞) *
            (P * (2 : ℝ≥0∞) ^ (v * d))⁻¹)) *
          (O : ℝ≥0∞) =
        ((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) := by
    have hpowInv :
        ((2 : ℝ≥0∞) ^ d)⁻¹ *
            ((2 : ℝ≥0∞) ^ (v * d))⁻¹ = V⁻¹ := by
      calc
        ((2 : ℝ≥0∞) ^ d)⁻¹ *
              ((2 : ℝ≥0∞) ^ (v * d))⁻¹ =
            (((2 : ℝ≥0∞) ^ d) *
              ((2 : ℝ≥0∞) ^ (v * d)))⁻¹ := by
                rw [ENNReal.mul_inv (Or.inl (by positivity))
                  (Or.inl (by simp))]
        _ = V⁻¹ := congrArg Inv.inv hpow
    have hPVInv : (P * V)⁻¹ = P⁻¹ * V⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hP0) (Or.inl hPtop)]
    rw [ENNReal.mul_inv (Or.inl hP0) (Or.inl hPtop)]
    calc
      ((2 : ℝ≥0∞) ^ d)⁻¹ *
            ((N : ℝ≥0∞) *
              (P⁻¹ * ((2 : ℝ≥0∞) ^ (v * d))⁻¹)) *
          (O : ℝ≥0∞) =
        ((N : ℝ≥0∞) *
          (P⁻¹ *
            (((2 : ℝ≥0∞) ^ d)⁻¹ *
              ((2 : ℝ≥0∞) ^ (v * d))⁻¹))) *
            (O : ℝ≥0∞) := by ac_rfl
      _ = ((N : ℝ≥0∞) * (P⁻¹ * V⁻¹)) * (O : ℝ≥0∞) := by
        rw [hpowInv]
      _ = ((N : ℝ≥0∞) * (P * V)⁻¹) * (O : ℝ≥0∞) := by
        rw [hPVInv]
  rw [hnormalize]
  rw [ennreal_mul_inv_mul_eq_inv_mul_iff_dyadic hP0 hPtop hV0 hVtop]
  rw [hVnat]
  norm_cast

/-- The dyadic pointwise gauge target itself is equivalent exactly to the
remaining natural residue-cardinality identity. -/
theorem
    localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicResidueCardinalityPrimePower
    (L : PositiveDefiniteIntegralLattice n) :
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime *
        (L.localPadicSpecialOrthogonalDifferentialComparisonNormAtPrime
          localPadicSpecialOrthogonalDifferentialDyadicPrime)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialExplicitTwoGramGaugeFactorAtPrime
        localPadicSpecialOrthogonalDifferentialDyadicPrime ↔
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueImage
          2).ncard *
          Nat.card
            (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange
              2) =
        2 ^
            ((padicValInt 2 L.pairingDeterminant + 1) *
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix)) *
          associatedBilinearDualQuotientCount L 2
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              2) := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialGaugeDefect_eq_explicitTwoGramGaugeFactor_iff_dyadicResidueCoordinateMass,
    L.dyadicResidueCoordinateMass_eq_iff_ncard_mul_natCard_eq_two_pow_succ_pairingDeterminantVal_mul_quotientCount]

end PositiveDefiniteIntegralLattice
