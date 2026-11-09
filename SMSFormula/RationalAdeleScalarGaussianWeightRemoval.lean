import SMSFormula.RationalAdeleScalarGaussianWeight
import SMSFormula.RationalAdeleAdditiveQuotient

noncomputable section

open MeasureTheory Set

namespace PositiveDefiniteIntegralLattice

theorem rationalAdele_measure_eq_of_gaussian_weight_eq
    {left right : Measure RationalAdele}
    (heq : ∀ shift : RationalAdele,
      left.withDensity (fun value => ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value)) =
        right.withDensity (fun value => ENNReal.ofReal (rationalAdeleScalarGaussianWeight shift value))) :
    left = right := by
  let weight (rational : ℚ) (value : RationalAdele) :=
    ENNReal.ofReal (rationalAdeleScalarGaussianWeight (-algebraMap ℚ RationalAdele rational) value)
  let carrier (rational : ℚ) := {value | weight rational value ≠ 0}
  have hweight (rational : ℚ) : Measurable (weight rational) :=
    (measurable_rationalAdeleScalarGaussianWeight _).ennreal_ofReal
  have hcarrier (rational : ℚ) : MeasurableSet (carrier rational) :=
    (measurableSet_eq_fun (hweight rational) measurable_const).compl
  have hcover : ⋃ rational : ℚ, carrier rational = univ := by
    apply eq_univ_of_forall
    intro value
    obtain ⟨rational, hrational⟩ := exists_rational_sub_mem_rationalAdeleStandardBlock value
    rw [rationalAdeleStandardBlock_eq] at hrational
    apply mem_iUnion.mpr
    refine ⟨rational, ?_⟩
    change ENNReal.ofReal (rationalAdeleScalarGaussianWeight _ value) ≠ 0
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply rationalAdeleScalarGaussianWeight_pos_of_mem
    simpa only [sub_eq_add_neg] using hrational.2
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro rational
  have hrestricted : (left.restrict (carrier rational)).withDensity (weight rational) =
      (right.restrict (carrier rational)).withDensity (weight rational) := by
    rw [← restrict_withDensity (hcarrier rational), ← restrict_withDensity (hcarrier rational)]
    exact congrArg (fun measure => measure.restrict (carrier rational)) (heq _)
  have hinverse := congrArg
    (fun measure : Measure RationalAdele => measure.withDensity (fun value => (weight rational value)⁻¹))
    hrestricted
  have hcancel (measure : Measure RationalAdele) :
      ((measure.restrict (carrier rational)).withDensity (weight rational)).withDensity
        (fun value => (weight rational value)⁻¹) = measure.restrict (carrier rational) := by
    apply withDensity_inv_same (hweight rational)
    · exact (ae_restrict_mem (hcarrier rational)).mono fun _ hmem => hmem
    · filter_upwards [] with value
      exact ENNReal.ofReal_ne_top
  dsimp only at hinverse
  rw [hcancel left, hcancel right] at hinverse
  exact hinverse

end PositiveDefiniteIntegralLattice
