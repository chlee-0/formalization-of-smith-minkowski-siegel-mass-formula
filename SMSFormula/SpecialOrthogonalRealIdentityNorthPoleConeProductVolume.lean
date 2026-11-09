import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeChangeOfVariables

/-!
# Product-volume normalization for the identity north-pole cone

This module proves that the pulled-back Euclidean Haar measure used in the
square-carrier cone change of variables is the ordinary product volume.  The
proof factors the fixed coordinate equivalence through Mathlib's canonical
volume-preserving `PiLp`, product, swap, and final-coordinate equivalences.
-/

open scoped ENNReal
noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

theorem
    measurePreserving_identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv
    (n : ℕ) :
    MeasurePreserving
      (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n)
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ))
      (volume : Measure (Fin (n + 1) → ℝ)) := by
  let hOfLp :=
    (PiLp.volume_preserving_ofLp (ι := Fin n)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  let hSwap := Measure.measurePreserving_swap
    (μ := (volume : Measure (Fin n → ℝ)))
    (ν := (volume : Measure ℝ))
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let hLast := (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm e
  have h := hLast.comp (hSwap.comp hOfLp)
  convert h using 1
  funext p i
  cases i using Fin.lastCases <;>
    simp [e,
      identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv]

theorem
    measurePreserving_identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv
    (n : ℕ) :
    MeasurePreserving
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n)
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have h :=
    (PiLp.volume_preserving_toLp (ι := Fin (n + 1))).comp
      (measurePreserving_identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv
        n)
  convert h using 1

theorem identitySpecialOrthogonalNorthPoleConePulledBackVolume_eq_volume
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConePulledBackVolume n =
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) := by
  exact
    ((measurePreserving_identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv
        n).symm
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).toHomeomorph.toMeasurableEquiv).map_eq

theorem map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap_volume
    (n : ℕ) :
    Measure.map (identitySpecialOrthogonalNorthPoleConeSquareMap n)
        (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
          (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
          fun p => ENNReal.ofReal
            (p.2 ^ n /
              identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) =
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
        ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
          ).symm ''
          identitySpecialOrthogonalNorthPoleRadialSector n) := by
  simpa [identitySpecialOrthogonalNorthPoleConePulledBackVolume_eq_volume]
    using
      map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap_radial n

theorem identitySpecialOrthogonalNorthPoleConeJacobian_factor
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    ENNReal.ofReal
        (p.2 ^ n /
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.1) =
      identitySpecialOrthogonalNorthPoleCoordinateDensity p.1 *
        ENNReal.ofReal (p.2 ^ n) := by
  have ht :
      0 < identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 :=
    identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hp.1
  rw [ENNReal.ofReal_div_of_pos ht]
  simp [identitySpecialOrthogonalNorthPoleCoordinateDensity,
    ENNReal.ofReal_inv_of_pos ht, div_eq_mul_inv, mul_comm]

theorem
    withDensity_identitySpecialOrthogonalNorthPoleConeDomain_eq_prod
    (n : ℕ) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
      (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
      fun p => ENNReal.ofReal
        (p.2 ^ n /
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n))).prod
      (((volume : Measure ℝ).restrict (Set.Ioo 0 1)).withDensity
        fun r => ENNReal.ofReal (r ^ n)) := by
  have hdensity :
      (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
        (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
        fun p => ENNReal.ofReal
          (p.2 ^ n /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) =
        (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
          (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
          fun p =>
            identitySpecialOrthogonalNorthPoleCoordinateDensity p.1 *
              ENNReal.ofReal (p.2 ^ n)) := by
    apply withDensity_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleConeDomainSet n)
      ] with p hp
    exact identitySpecialOrthogonalNorthPoleConeJacobian_factor n hp
  rw [hdensity, identitySpecialOrthogonalNorthPoleConeDomainSet,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (MeasureTheory.prod_withDensity
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ν := (volume : Measure ℝ).restrict (Set.Ioo 0 1))
      (f := identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n))
      (g := fun r => ENNReal.ofReal (r ^ n))
      (measurable_identitySpecialOrthogonalNorthPoleCoordinateDensity n)
      (by fun_prop)).symm

end PositiveDefiniteIntegralLattice
