import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleConeRadialIntegral

/-!
# Radial-sector transport for identity north-pole coordinates

This module localizes the square cone change-of-variables theorem to
rectangles over open subsets of the north-pole coordinate ball.  Combining
that transport with the evaluated radial factor and the radial definition of
`Measure.toSphere` proves that the sphere-coordinate measure is exactly the
inverse-square-root density measure.
-/

open scoped ENNReal Pointwise
noncomputable section

open MeasureTheory Metric Set

namespace PositiveDefiniteIntegralLattice

def identitySpecialOrthogonalNorthPoleCoordinateAmbientSet (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Subtype.val '' s

def identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Set (identitySpecialOrthogonalLastColumnSphere n) :=
  identitySpecialOrthogonalNorthPoleInverse n '' s

def identitySpecialOrthogonalNorthPoleCoordinateRadialSector (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Ioo (0 : ℝ) 1 •
    ((↑) '' identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet n s :
      Set (EuclideanSpace ℝ (Fin (n + 1))))

theorem identitySpecialOrthogonalNorthPoleCoordinateAmbientSet_isOpen
    (n : ℕ) {s : Set _} (hs : IsOpen s) :
    IsOpen (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) :=
  (Metric.isOpen_ball.isOpenMap_subtype_val s hs)

theorem identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet_isOpen
    (n : ℕ) {s : Set _} (hs : IsOpen s) :
    IsOpen (identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet n s) := by
  have himage :
      identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet n s =
        Subtype.val ''
          ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm ''
            s) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm v,
        ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  rw [himage]
  exact
    (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n
      ).isOpenMap_subtype_val _
      ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n
        ).symm.isOpenMap _ hs)

theorem identitySpecialOrthogonalNorthPoleCoordinateRadialSector_isOpen
    (n : ℕ) {s : Set _} (hs : IsOpen s) :
    IsOpen (identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) := by
  exact isOpen_Ioo.smul_sphere one_ne_zero (by simp)
    (identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet_isOpen n hs)

theorem identitySpecialOrthogonalNorthPoleCoordinateRadialSector_subset
    (n : ℕ) (s : Set _) :
    identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s ⊆
      identitySpecialOrthogonalNorthPoleRadialSector n := by
  rintro _ ⟨r, hr, _, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
  exact ⟨r, hr, _, ⟨identitySpecialOrthogonalNorthPoleInverse n v,
    identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere n v, rfl⟩, rfl⟩

theorem image_identitySpecialOrthogonalNorthPoleCone_coordinateRectangle
    (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    identitySpecialOrthogonalNorthPoleCone n ''
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1) =
      identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s := by
  ext x
  constructor
  · rintro ⟨⟨v, r⟩, ⟨⟨u, hu, rfl⟩, hr⟩, rfl⟩
    refine ⟨r, hr, _, ?_, rfl⟩
    exact ⟨identitySpecialOrthogonalNorthPoleInverse n u,
      ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(u.1, r), ⟨⟨u, hu, rfl⟩, hr⟩, ?_⟩
    rw [identitySpecialOrthogonalNorthPoleCone]
    rfl

theorem
    image_identitySpecialOrthogonalNorthPoleConeSquareMap_coordinateRectangle
    (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    identitySpecialOrthogonalNorthPoleConeSquareMap n ''
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1) =
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s := by
  change
    ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
      ).symm ∘ identitySpecialOrthogonalNorthPoleCone n) '' _ = _
  calc
    ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ∘ identitySpecialOrthogonalNorthPoleCone n) ''
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1) =
      (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm ''
        (identitySpecialOrthogonalNorthPoleCone n ''
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1)) := by
      simpa [Function.comp_def] using
        (Set.image_image
          (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
            ).symm
          (identitySpecialOrthogonalNorthPoleCone n)
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1)).symm
    _ = _ := by rw [image_identitySpecialOrthogonalNorthPoleCone_coordinateRectangle]

theorem
    inter_preimage_identitySpecialOrthogonalNorthPoleConeSquareMap_coordinateRadialSector
    (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    identitySpecialOrthogonalNorthPoleConeDomainSet n ∩
        identitySpecialOrthogonalNorthPoleConeSquareMap n ⁻¹'
          ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
            ).symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) =
      identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1 := by
  let U := identitySpecialOrthogonalNorthPoleConeDomainSet n
  let f := identitySpecialOrthogonalNorthPoleConeSquareMap n
  let R := identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1
  let T :=
    (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
      ).symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s
  have hR : R ⊆ U := by
    rintro ⟨v, r⟩ ⟨⟨u, hu, rfl⟩, hr⟩
    exact ⟨u.2, hr⟩
  have himage : f '' R = T := image_identitySpecialOrthogonalNorthPoleConeSquareMap_coordinateRectangle n s
  ext p
  constructor
  · rintro ⟨hpU, hpT⟩
    have hfp : f p ∈ f '' R := by
      rw [himage]
      exact hpT
    rcases hfp with ⟨q, hqR, hqp⟩
    have hqU := hR hqR
    have hqp' : q = p :=
      injOn_identitySpecialOrthogonalNorthPoleConeSquareMap n hqU hpU hqp
    simpa [hqp'] using hqR
  · intro hpR
    refine ⟨hR hpR, ?_⟩
    change f p ∈ T
    rw [← himage]
    exact ⟨p, hpR, rfl⟩

theorem
    identitySpecialOrthogonalNorthPoleConeWeightedMeasure_preimage_coordinateRadialSector
    (n : ℕ)
    {s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : IsOpen s) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
        (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
        fun p => ENNReal.ofReal
          (p.2 ^ n /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1))
        (identitySpecialOrthogonalNorthPoleConeSquareMap n ⁻¹'
          ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
            ).symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s)) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
        (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
        fun p => ENNReal.ofReal
          (p.2 ^ n /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1))
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1) := by
  let U := identitySpecialOrthogonalNorthPoleConeDomainSet n
  let f := identitySpecialOrthogonalNorthPoleConeSquareMap n
  let R := identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1
  let T :=
    (identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
      ).symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s
  let ρ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal
      (p.2 ^ n /
        identitySpecialOrthogonalNorthPoleFinalCoordinate p.1)
  have hR : MeasurableSet R :=
    ((identitySpecialOrthogonalNorthPoleCoordinateAmbientSet_isOpen n hs).prod isOpen_Ioo).measurableSet
  have hRsub : R ⊆ U := by
    rintro ⟨v, r⟩ ⟨⟨u, hu, rfl⟩, hr⟩
    exact ⟨u.2, hr⟩
  have hT : MeasurableSet T :=
    ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
      ).symm.toHomeomorph.isOpenMap _
        (identitySpecialOrthogonalNorthPoleCoordinateRadialSector_isOpen n hs)).measurableSet
  have hpre : MeasurableSet (f ⁻¹' T) :=
    hT.preimage
      ((identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
        ).symm.continuous.comp
          (continuous_identitySpecialOrthogonalNorthPoleCone n)).measurable
  have hrestrict :
      (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict U
        ).withDensity ρ).restrict (f ⁻¹' T) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict U
        ).withDensity ρ).restrict R := by
    rw [restrict_withDensity hpre, restrict_withDensity hR,
      Measure.restrict_restrict hpre, Measure.restrict_restrict hR]
    congr 2
    calc
      f ⁻¹' T ∩ U = U ∩ f ⁻¹' T := inter_comm _ _
      _ = R := inter_preimage_identitySpecialOrthogonalNorthPoleConeSquareMap_coordinateRadialSector n s
      _ = R ∩ U := (inter_eq_left.mpr hRsub).symm
  change
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict U
      ).withDensity ρ) (f ⁻¹' T) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict U
      ).withDensity ρ) R
  simpa [Measure.restrict_apply, hpre, hR] using
    congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n) × ℝ) => μ univ)
      hrestrict

theorem identitySpecialOrthogonalNorthPoleConeRadialMeasure_Ioo (n : ℕ) :
    identitySpecialOrthogonalNorthPoleConeRadialMeasure n
        (Ioo (0 : ℝ) 1) =
      identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ := by
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure,
    withDensity_apply _ measurableSet_Ioo,
    withDensity_apply _ MeasurableSet.univ]
  congr 1
  rw [Measure.restrict_univ]
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_restrict_mem
      (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)))

theorem identitySpecialOrthogonalNorthPoleConeWeightedMeasure_coordinateRectangle (n : ℕ)
    (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
        (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
        fun p => ENNReal.ofReal
          (p.2 ^ n /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1))
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s ×ˢ Ioo (0 : ℝ) 1) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) *
        identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ := by
  rw [withDensity_identitySpecialOrthogonalNorthPoleConeDomain_eq_prod,
    Measure.prod_prod]
  change _ *
      identitySpecialOrthogonalNorthPoleConeRadialMeasure n (Ioo 0 1) =
    _ * identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ
  rw [identitySpecialOrthogonalNorthPoleConeRadialMeasure_Ioo]

theorem volume_identitySpecialOrthogonalNorthPoleCoordinateRadialSector (n : ℕ)
    {s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : IsOpen s) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        (identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) *
        identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ := by
  let f := identitySpecialOrthogonalNorthPoleConeSquareMap n
  let E :=
    identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv n
  let T := E.symm '' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s
  let T₀ := E.symm ''
    identitySpecialOrthogonalNorthPoleRadialSector n
  let μw :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict
      (identitySpecialOrthogonalNorthPoleConeDomainSet n)).withDensity
      fun p => ENNReal.ofReal
        (p.2 ^ n /
          identitySpecialOrthogonalNorthPoleFinalCoordinate p.1))
  have hT : MeasurableSet T :=
    (E.symm.toHomeomorph.isOpenMap _
      (identitySpecialOrthogonalNorthPoleCoordinateRadialSector_isOpen n hs)).measurableSet
  have hTsub : T ⊆ T₀ :=
    Set.image_mono (identitySpecialOrthogonalNorthPoleCoordinateRadialSector_subset n s)
  have hf : Measurable f :=
    (E.symm.continuous.comp
      (continuous_identitySpecialOrthogonalNorthPoleCone n)).measurable
  have hcov := congrArg
    (fun μ : Measure (EuclideanSpace ℝ (Fin n) × ℝ) => μ T)
    (map_withDensity_identitySpecialOrthogonalNorthPoleConeSquareMap_volume n)
  change Measure.map f μw T =
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).restrict T₀ T
    at hcov
  rw [Measure.map_apply hf hT, Measure.restrict_apply hT,
    inter_eq_left.mpr hTsub] at hcov
  have hsource :
      μw (f ⁻¹' T) =
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
          (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
            (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) *
          identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ := by
    change _ = _
    rw [identitySpecialOrthogonalNorthPoleConeWeightedMeasure_preimage_coordinateRadialSector n hs,
      identitySpecialOrthogonalNorthPoleConeWeightedMeasure_coordinateRectangle n s]
  have hTpre : E ⁻¹' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s = T := by
    ext p
    constructor
    · intro hp
      exact ⟨E p, hp, E.symm_apply_apply p⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  have hE :=
    (measurePreserving_identitySpecialOrthogonalNorthPoleConeAmbientContinuousLinearEquiv
      n).measure_preimage
      (identitySpecialOrthogonalNorthPoleCoordinateRadialSector_isOpen n hs).measurableSet.nullMeasurableSet
  change
    (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ))
        (E ⁻¹' identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) =
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        (identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) at hE
  rw [hTpre] at hE
  rw [← hE, ← hcov, hsource]

theorem identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_apply_isOpen (n : ℕ)
    {s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : IsOpen s) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n s =
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        (identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet n s) := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure,
    Measure.map_apply
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).measurable
      hs.measurableSet]
  rw [identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure,
    comap_subtype_coe_apply
      (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere n)]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨
      identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n y,
      ?_, ?_⟩
    · exact hy
    · apply Subtype.ext
      exact identitySpecialOrthogonalNorthPoleInverse_coordinate n y.1 y.2
  · rintro ⟨v, hv, rfl⟩
    refine ⟨
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm v,
      ?_, rfl⟩
    simpa using hv

theorem identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure_apply
    (n : ℕ) (s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure n s =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure,
    comap_subtype_coe_apply Metric.isOpen_ball.measurableSet]
  rfl

theorem
    restrict_withDensity_identitySpecialOrthogonalNorthPoleCoordinateAmbientSet
    (n : ℕ)
    {s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : IsOpen s) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).withDensity
      (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
        (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) := by
  have hball : MeasurableSet (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s) :=
    (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet_isOpen n hs).measurableSet
  rw [← restrict_withDensity Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply hball,
    inter_eq_left.mpr]
  rintro _ ⟨v, _hv, rfl⟩
  exact v.2

theorem
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_eq_densityMeasure
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n =
      identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure n := by
  apply Measure.ext_of_generateFrom_of_iUnion
    {s : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) | IsOpen s}
    (fun _ => univ)
    (BorelSpace.measurable_eq.trans (by rfl))
    isPiSystem_isOpen
  · ext x
    simp
  · intro _
    change IsOpen (univ : Set
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    exact isOpen_univ
  · intro _
    exact
      (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top n
        ).ne
  · intro s hs
    change IsOpen s at hs
    rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_apply_isOpen n hs,
      identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure_apply n s,
      Measure.toSphere_apply'
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        (identitySpecialOrthogonalNorthPoleCoordinateHemisphereSet_isOpen n hs).measurableSet]
    change
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) : ℝ≥0∞) *
          (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
            (identitySpecialOrthogonalNorthPoleCoordinateRadialSector n s) =
        _
    rw [volume_identitySpecialOrthogonalNorthPoleCoordinateRadialSector n hs]
    rw [restrict_withDensity_identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n hs]
    rw [finrank_euclideanSpace_fin]
    simp only [Nat.cast_add, Nat.cast_one]
    let A :=
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))
          (identitySpecialOrthogonalNorthPoleCoordinateAmbientSet n s)
    change
      (n + 1 : ℝ≥0∞) *
          (A * identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ) =
        A
    calc
      (n + 1 : ℝ≥0∞) * (A *
          identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ) =
        A * ((n + 1 : ℝ≥0∞) *
          identitySpecialOrthogonalNorthPoleConeRadialMeasure n univ) := by
            ac_rfl
      _ = A := by
        rw [
          identitySpecialOrthogonalNorthPoleConeRadialMeasure_finrankFactor]
        simp

end PositiveDefiniteIntegralLattice
