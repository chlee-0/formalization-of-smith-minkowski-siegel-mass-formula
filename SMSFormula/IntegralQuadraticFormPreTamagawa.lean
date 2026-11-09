import SMSFormula.IntegralQuadraticFormProduct
import SMSFormula.IntegralQuadraticFormMassTransport

/-!
# Direct mass formula for integral quadratic forms before evaluating the Tamagawa number

The direct local product has already been assembled from `Q_H`, the polar
`A`-dual, and `det(A)`.  This module inserts that product into the symbolic
ordinary-mass identity while retaining the full differential Tamagawa number.
The latter is the datum to which the general theorem `tau(SO)=2` eventually
applies; it is not evaluated here.

The reciprocal-volume-scaled datum called `Normalized` in the integral API has
already absorbed the finite inverse-volume factor.  Consequently the literal
product-times-Tamagawa formula is correctly stated with the full differential
datum, while the earlier normalized-datum theorem remains the equivalent
real-volume form.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

theorem transportedOrdinaryGenusMass_eq_latticeOfPolarForm :
    H.transportedOrdinaryGenusMass = H.latticeOfPolarForm.ordinaryGenusMass :=
  rfl

/-- The reciprocal-finite-volume-scaled datum called `Normalized` in the
integral implementation, transported transparently to the integral-quadratic-form API.
This accessor is useful for the inverse-real-volume symbolic formula, but it
is distinct from the full datum in the product-times-Tamagawa formula below. -/
def reciprocalVolumeNormalizedDifferentialTamagawaNumberENNReal
    (hnpos : 0 < n)
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) : ℝ≥0∞ :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  (H.latticeOfPolarForm
    |>.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal

/-- Direct integral-quadratic-form restatement of the existing symbolic theorem for the
reciprocal-volume-scaled normalized datum. -/
theorem transportedOrdinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_reciprocalVolumeNormalizedTamagawaNumber
    (hnpos : 0 < n)
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      (H.latticeOfPolarForm.concreteRealSpecialOrthogonalDifferentialMeasure
          Set.univ)⁻¹ *
        ((2 : ℝ≥0∞)⁻¹ *
          H.reciprocalVolumeNormalizedDifferentialTamagawaNumberENNReal
            hnpos inst hP) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  simpa [transportedOrdinaryGenusMass,
    reciprocalVolumeNormalizedDifferentialTamagawaNumberENNReal] using
      H.transportedOrdinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_normalizedTamagawaNumber
        inst hP

/-- The full differential Tamagawa number attached to the common rational
special-orthogonal group.  This is a theorem-facing transparent transport of
the full datum of the scaled integral model, whose group was explicitly identified
with the direct group of the integral quadratic form before this definition was introduced. -/
def fullAdelicDifferentialTamagawaNumberENNReal
    (hnpos : 0 < n)
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) : ℝ≥0∞ :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  (H.latticeOfPolarForm
    |>.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hP).tamagawaNumberENNReal

/-- The direct product side of the integral quadratic form is the inverse real differential
mass times the finite differential stabilizer inverse volume.  This is the
small algebraic normalization lemma needed before any Tamagawa evaluation. -/
theorem ENNReal_ofReal_massFormulaProductSide_eq_inv_realDifferentialMass_mul_finiteInverseVolume
    [NeZero n] (P : ℝ) :
    ENNReal.ofReal (H.massFormulaProductSide P) =
      (H.latticeOfPolarForm.concreteRealSpecialOrthogonalDifferentialMeasure
          Set.univ)⁻¹ *
        H.latticeOfPolarForm.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
          P := by
  let L := H.latticeOfPolarForm
  let R : ℝ≥0∞ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ
  let A : ℝ≥0∞ :=
    ENNReal.ofReal (PositiveDefiniteIntegralLattice.archimedeanMassFactor n)
  let C : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialLocalCorrectionFiniteProduct
  let p : ℝ≥0∞ := ENNReal.ofReal P
  let I : ℝ≥0∞ :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  have hR0 : R ≠ 0 :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_zero
  have hRtop : R ≠ ⊤ :=
    L.concreteRealSpecialOrthogonalDifferentialMeasure_univ_ne_top
  have hunit : R * (A * C) = 1 :=
    L.globalDifferentialUnitNormalization
  have hcore : A * C = R⁻¹ := by
    calc
      A * C = 1 * (A * C) := by rw [one_mul]
      _ = (R⁻¹ * R) * (A * C) := by
        rw [ENNReal.inv_mul_cancel hR0 hRtop]
      _ = R⁻¹ * (R * (A * C)) := by ac_rfl
      _ = R⁻¹ := by rw [hunit, mul_one]
  have hp : p = C * I :=
    L.ENNReal_ofReal_eq_localCorrectionFiniteProduct_mul_finiteStabilizerInverseVolume
      P
  have hproduct :
      ENNReal.ofReal (H.massFormulaProductSide P) = A * p := by
    rw [H.massFormulaProductSide_eq_latticeOfPolarForm]
    exact L.ENNReal_ofReal_massFormulaProductSide P
  change ENNReal.ofReal (H.massFormulaProductSide P) = R⁻¹ * I
  calc
    ENNReal.ofReal (H.massFormulaProductSide P) = A * p :=
      hproduct
    _ = A * (C * I) := by rw [hp]
    _ = (A * C) * I := by ac_rfl
    _ = R⁻¹ * I := by rw [hcore]

/-- The direct ordinary mass of the integral quadratic form before evaluating `tau(SO)`.  The
product is built from the intrinsic `Q_H`/`A`-dual local densities, and the
full differential Tamagawa number remains symbolic. -/
theorem transportedOrdinaryGenusMassENNReal_eq_massFormulaProductSide_mul_inv_two_mul_fullTamagawaNumber
    (hnpos : 0 < n) [NeZero n]
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (H.massFormulaProductSide P) *
        ((2 : ℝ≥0∞)⁻¹ *
          H.fullAdelicDifferentialTamagawaNumberENNReal hnpos inst hP) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  let L := H.latticeOfPolarForm
  let τ : ℝ≥0∞ :=
    H.fullAdelicDifferentialTamagawaNumberENNReal hnpos inst hP
  have hproper :=
    L.properClassGenusMassENNReal_eq_inv_realDifferentialMass_mul_finiteInverseVolume_mul_differentialTamagawaNumber
      inst hP
  have hsplit :=
    L.properClassGenusMassENNReal_eq_two_mul_ordinaryGenusMassENNReal
  have hproduct :=
    ENNReal_ofReal_massFormulaProductSide_eq_inv_realDifferentialMass_mul_finiteInverseVolume
      (H := H) P
  have htwo :
      (2 : ℝ≥0∞) * ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        ENNReal.ofReal (H.massFormulaProductSide P) * τ := by
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) := by
            rw [transportedOrdinaryGenusMass]
            exact hsplit.symm
      _ =
          (L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
            (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
                P * τ) := by
          simpa [τ, fullAdelicDifferentialTamagawaNumberENNReal] using hproper
      _ =
          ((L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
              L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
                P) * τ := by ac_rfl
      _ = ENNReal.ofReal (H.massFormulaProductSide P) * τ := by
        rw [hproduct]
  change ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
    ENNReal.ofReal (H.massFormulaProductSide P) *
      ((2 : ℝ≥0∞)⁻¹ * τ)
  calc
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
        ((2 : ℝ≥0∞)⁻¹ * 2) *
          ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) := by
      rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ = (2 : ℝ≥0∞)⁻¹ *
          (2 * ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ))) := by
      rw [mul_assoc]
    _ = (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (H.massFormulaProductSide P) * τ) := by
      rw [htwo]
    _ = ENNReal.ofReal (H.massFormulaProductSide P) *
          ((2 : ℝ≥0∞)⁻¹ * τ) := by ac_rfl

/-- The canonical-rank direct pre-Tamagawa endpoint.  The convergence
hypothesis identifies `P` as the intrinsic local product of the integral quadratic form; no
Tamagawa-number evaluation is used. -/
theorem transportedOrdinaryGenusMass_eq_massFormulaProductSide_mul_tamagawa_ENNReal
    (hn : 3 ≤ n)
    (inst : Fintype
      H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : H.massLocalInverseProductTendsTo P) :
    ENNReal.ofReal (((H.transportedOrdinaryGenusMass : ℚ) : ℝ)) =
      ENNReal.ofReal (H.massFormulaProductSide P) *
        ((2 : ℝ≥0∞)⁻¹ *
          H.fullAdelicDifferentialTamagawaNumberENNReal
            (lt_of_lt_of_le (by norm_num) hn) inst hP) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have _hconvIntegralModel :
      PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo
        H.latticeOfPolarForm P :=
    (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm
      P).mp hconv
  exact
    H.transportedOrdinaryGenusMassENNReal_eq_massFormulaProductSide_mul_inv_two_mul_fullTamagawaNumber
      hnpos inst hP

end PositiveDefiniteIntegralQuadraticForm

end
