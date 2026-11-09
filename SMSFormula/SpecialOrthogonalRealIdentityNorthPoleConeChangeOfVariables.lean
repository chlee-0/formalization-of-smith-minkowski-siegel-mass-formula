import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeDeterminant

/-!
# Square-carrier change of variables for the identity north-pole cone

This module conjugates the cone to a self-map of its product source, applies
the finite-dimensional nonlinear change-of-variables theorem with ambient
Euclidean volume pulled back through the conjugating linear equivalence, and
keeps the resulting Haar measure distinct from ordinary product volume.
-/

open scoped Matrix ENNReal
noncomputable section

open Metric Set MeasureTheory

namespace PositiveDefiniteIntegralLattice

noncomputable def
    identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n
    ).toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (n + 1) => ℝ)).symm

def identitySpecialOrthogonalNorthPoleConeSquareMap
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    EuclideanSpace ℝ (Fin n) × ℝ :=
  (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n).symm
    (identitySpecialOrthogonalNorthPoleCone n p)

noncomputable def identitySpecialOrthogonalNorthPoleConeSquareDerivative
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
    ).symm.toContinuousLinearMap.comp
    (identitySpecialOrthogonalNorthPoleConeDerivative n p)

theorem hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleConeSquareMap
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    HasFDerivWithinAt
      (identitySpecialOrthogonalNorthPoleConeSquareMap n)
      (identitySpecialOrthogonalNorthPoleConeSquareDerivative n p)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) p := by
  exact
    (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
      ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt
      p (hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleCone n hp)

theorem identitySpecialOrthogonalNorthPoleConeSquareDerivative_conj
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n
        ).toLinearMap.comp
        ((identitySpecialOrthogonalNorthPoleConeSquareDerivative n p).toLinearMap.comp
          (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n
            ).symm.toLinearMap) =
      identitySpecialOrthogonalNorthPoleConeCoordinateDerivative n p := by
  apply LinearMap.ext
  intro f
  funext i
  simp [identitySpecialOrthogonalNorthPoleConeSquareDerivative,
    identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv,
    identitySpecialOrthogonalNorthPoleConeCoordinateDerivative,
    LinearMap.comp_apply]

theorem abs_det_identitySpecialOrthogonalNorthPoleConeSquareDerivative
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    |LinearMap.det
        (identitySpecialOrthogonalNorthPoleConeSquareDerivative n p).toLinearMap| =
      p.2 ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  have hconj := LinearMap.det_conj
    (identitySpecialOrthogonalNorthPoleConeSquareDerivative n p).toLinearMap
    (identitySpecialOrthogonalNorthPoleConeSourceCoordinateLinearEquiv n)
  rw [identitySpecialOrthogonalNorthPoleConeSquareDerivative_conj n p] at hconj
  rw [← hconj]
  exact abs_identitySpecialOrthogonalNorthPoleConeCoordinateDerivative_det
    n p hp

noncomputable def
    identitySpecialOrthogonalNorthPoleConePulledBackVolume (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Measure.map
    (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n).symm
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))

theorem injOn_identitySpecialOrthogonalNorthPoleConeSquareMap (n : ℕ) :
    Set.InjOn (identitySpecialOrthogonalNorthPoleConeSquareMap n)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) :=
  fun _x hx _y hy hxy =>
    identitySpecialOrthogonalNorthPoleCone_injOn n hx hy
      ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm.injective hxy)

theorem image_identitySpecialOrthogonalNorthPoleConeSquareMap_domain (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConeSquareMap n ''
        identitySpecialOrthogonalNorthPoleConeDomainSet n =
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ''
        identitySpecialOrthogonalNorthPoleRadialSector n := by
  change
    ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ∘ identitySpecialOrthogonalNorthPoleCone n) ''
      identitySpecialOrthogonalNorthPoleConeDomainSet n = _
  calc
    ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ∘ identitySpecialOrthogonalNorthPoleCone n) ''
        identitySpecialOrthogonalNorthPoleConeDomainSet n =
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ''
        (identitySpecialOrthogonalNorthPoleCone n ''
          identitySpecialOrthogonalNorthPoleConeDomainSet n) :=
      by
        simpa [Function.comp_def] using
          (Set.image_image
            (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
              ).symm
            (identitySpecialOrthogonalNorthPoleCone n)
            (identitySpecialOrthogonalNorthPoleConeDomainSet n)).symm
    _ = _ := by
      rw [identitySpecialOrthogonalNorthPoleCone_image_domain]

theorem
    map_identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv_pulledBackVolume
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n)
        (identitySpecialOrthogonalNorthPoleConePulledBackVolume n) =
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rw [identitySpecialOrthogonalNorthPoleConePulledBackVolume,
    Measure.map_map
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).continuous.measurable
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm.continuous.measurable]
  simp [Function.comp_def]

theorem map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap
    (n : ℕ) :
    Measure.map (identitySpecialOrthogonalNorthPoleConeSquareMap n)
        (((identitySpecialOrthogonalNorthPoleConePulledBackVolume n).restrict
          (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
          fun p => ENNReal.ofReal
            (p.2 ^ n /
              identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) =
      (identitySpecialOrthogonalNorthPoleConePulledBackVolume n).restrict
        (identitySpecialOrthogonalNorthPoleConeSquareMap n ''
          identitySpecialOrthogonalNorthPoleConeDomainSet n) := by
  let μ := identitySpecialOrthogonalNorthPoleConePulledBackVolume n
  let U := identitySpecialOrthogonalNorthPoleConeDomainSet n
  let f := identitySpecialOrthogonalNorthPoleConeSquareMap n
  let f' := identitySpecialOrthogonalNorthPoleConeSquareDerivative n
  letI : μ.IsAddHaarMeasure := by
    dsimp [μ, identitySpecialOrthogonalNorthPoleConePulledBackVolume]
    infer_instance
  have hmap := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    μ
    (measurableSet_identitySpecialOrthogonalNorthPoleConeDomainSet n
      ).nullMeasurableSet
    (fun p hp =>
      hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleConeSquareMap n hp)
    (injOn_identitySpecialOrthogonalNorthPoleConeSquareMap n)
  have hdensity :
      ((μ.restrict U).withDensity fun p =>
          ENNReal.ofReal |LinearMap.det (f' p).toLinearMap|) =
        ((μ.restrict U).withDensity fun p =>
          ENNReal.ofReal
            (p.2 ^ n /
              identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) := by
    apply withDensity_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleConeDomainSet n)
      ] with p hp
    rw [abs_det_identitySpecialOrthogonalNorthPoleConeSquareDerivative n p hp]
  rw [hdensity] at hmap
  simpa [μ, U, f, f'] using hmap

theorem map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap_radial
    (n : ℕ) :
    Measure.map (identitySpecialOrthogonalNorthPoleConeSquareMap n)
        (((identitySpecialOrthogonalNorthPoleConePulledBackVolume n).restrict
          (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
          fun p => ENNReal.ofReal
            (p.2 ^ n /
              identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)) =
      (identitySpecialOrthogonalNorthPoleConePulledBackVolume n).restrict
        ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
          ).symm ''
          identitySpecialOrthogonalNorthPoleRadialSector n) := by
  rw [← image_identitySpecialOrthogonalNorthPoleConeSquareMap_domain n]
  exact map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap n

end PositiveDefiniteIntegralLattice
