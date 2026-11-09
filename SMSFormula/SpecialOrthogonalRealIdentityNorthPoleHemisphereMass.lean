import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleSphereMeasure
import SMSFormula.SpecialOrthogonalRealIdentitySphereVolume

/-!
# The positive north-pole hemisphere has half the sphere mass

This module evaluates the already constructed north-pole coordinate sphere
measure.  Negation exchanges the open positive and negative hemispheres.  The
remaining equator has sphere measure zero because its radial sector lies in a
proper coordinate hyperplane.  Consequently the positive hemisphere has half
the full sphere mass, hence exactly
`identitySpecialOrthogonalSphereStep (n + 1)`.

The final definitions normalize the positive-hemisphere coordinate measure by
this proved mass.  No group recurrence or differential-fiber comparison is
asserted here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Pointwise

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

/-- The open hemisphere opposite the north-pole hemisphere. -/
def identitySpecialOrthogonalSouthPoleHemisphere (n : ℕ) :
    Set (identitySpecialOrthogonalLastColumnSphere n) :=
  {x | (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) < 0}

/-- The equator separating the positive and negative last-coordinate
hemispheres. -/
def identitySpecialOrthogonalNorthPoleEquator (n : ℕ) :
    Set (identitySpecialOrthogonalLastColumnSphere n) :=
  {x | (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = 0}

theorem isOpen_identitySpecialOrthogonalSouthPoleHemisphere (n : ℕ) :
    IsOpen (identitySpecialOrthogonalSouthPoleHemisphere n) := by
  apply isOpen_lt
  · exact
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ)
        (Fin.last n)).comp continuous_subtype_val
  · exact continuous_const

theorem isClosed_identitySpecialOrthogonalNorthPoleEquator (n : ℕ) :
    IsClosed (identitySpecialOrthogonalNorthPoleEquator n) := by
  apply isClosed_eq
  · exact
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ)
        (Fin.last n)).comp continuous_subtype_val
  · exact continuous_const

theorem identitySpecialOrthogonalNorthPoleEquator_radialSector_subset_ker
    (n : ℕ) :
    Set.Ioo (0 : ℝ) 1 •
        ((↑) '' identitySpecialOrthogonalNorthPoleEquator n :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).ker := by
  rintro x ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
  change r * y.1 (Fin.last n) = 0
  rw [hy]
  simp

theorem identitySpecialOrthogonalLastProjection_ker_ne_top
    (n : ℕ) :
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).ker ≠ ⊤ := by
  rw [Ne, Submodule.eq_top_iff']
  intro h
  have hnorth :=
    h (identitySpecialOrthogonalNorthPole n :
      EuclideanSpace ℝ (Fin (n + 1)))
  change
    (identitySpecialOrthogonalNorthPole n :
      EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = 0 at hnorth
  simp at hnorth

/-- The equator has zero additive-Haar-induced sphere measure. -/
theorem euclideanVolumeToSphere_identitySpecialOrthogonalNorthPoleEquator
    (n : ℕ) :
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        (identitySpecialOrthogonalNorthPoleEquator n) = 0 := by
  rw [Measure.toSphere_apply' _
    (isClosed_identitySpecialOrthogonalNorthPoleEquator n).measurableSet]
  rw [mul_eq_zero]
  right
  exact
    measure_mono_null
      (identitySpecialOrthogonalNorthPoleEquator_radialSector_subset_ker n)
      (Measure.addHaar_submodule
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).ker
        (identitySpecialOrthogonalLastProjection_ker_ne_top n))

theorem neg_preimage_identitySpecialOrthogonalNorthPoleHemisphere_radialSector
    (n : ℕ) :
    (fun x : EuclideanSpace ℝ (Fin (n + 1)) => -x) ⁻¹'
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
            Set (EuclideanSpace ℝ (Fin (n + 1))))) =
      Set.Ioo (0 : ℝ) 1 •
        ((↑) '' identitySpecialOrthogonalSouthPoleHemisphere n :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, hxy⟩
    let z : identitySpecialOrthogonalLastColumnSphere n :=
      ⟨-y.1, by simpa [norm_neg] using y.2⟩
    refine ⟨r, hr, _, ⟨z, ?_, rfl⟩, ?_⟩
    · change -y.1 (Fin.last n) < 0
      simpa using hy
    · simp [z, hxy]
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, hxy⟩
    let z : identitySpecialOrthogonalLastColumnSphere n :=
      ⟨-y.1, by simpa [norm_neg] using y.2⟩
    refine ⟨r, hr, _, ⟨z, ?_, rfl⟩, ?_⟩
    · change 0 < -y.1 (Fin.last n)
      simpa using hy
    · simp [z, hxy]

/-- Antipodal symmetry gives equal raw sphere mass to the two open
hemispheres. -/
theorem euclideanVolumeToSphere_southPoleHemisphere_eq_northPoleHemisphere
    (n : ℕ) :
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        (identitySpecialOrthogonalSouthPoleHemisphere n) =
      (volume :
        Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
          (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  rw [Measure.toSphere_apply' _
      (isOpen_identitySpecialOrthogonalSouthPoleHemisphere n).measurableSet,
    Measure.toSphere_apply' _
      (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n).measurableSet]
  congr 1
  have hopen :
      IsOpen
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
            Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isOpen_Ioo.smul_sphere one_ne_zero (by simp)
      (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n)
  calc
    volume
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' identitySpecialOrthogonalSouthPoleHemisphere n :
            Set (EuclideanSpace ℝ (Fin (n + 1))))) =
        volume
          ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => -x) ⁻¹'
            (Set.Ioo (0 : ℝ) 1 •
              ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
                Set (EuclideanSpace ℝ (Fin (n + 1)))))) := by
          rw [
            neg_preimage_identitySpecialOrthogonalNorthPoleHemisphere_radialSector]
    _ = Measure.map
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) => -x)
          volume
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
              Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
          rw [Measure.map_apply continuous_neg.measurable hopen.measurableSet]
    _ = volume
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
              Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
          rw [Measure.map_neg_eq_self]

/-- The full sphere is the two equal open hemispheres up to the null
equator. -/
theorem euclideanVolumeToSphere_univ_eq_two_mul_northPoleHemisphere
    (n : ℕ) :
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ =
      2 *
        (volume :
          Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
            (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  let μ :=
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
  have huniv :
      (Set.univ :
          Set (identitySpecialOrthogonalLastColumnSphere n)) =
        (identitySpecialOrthogonalNorthPoleHemisphere n ∪
            identitySpecialOrthogonalSouthPoleHemisphere n) ∪
          identitySpecialOrthogonalNorthPoleEquator n := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    rcases lt_trichotomy
        ((x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) 0 with
      hneg | hzero | hpos
    · exact Or.inl (Or.inr hneg)
    · exact Or.inr hzero
    · exact Or.inl (Or.inl hpos)
  have hdisjPS :
      Disjoint
        (identitySpecialOrthogonalNorthPoleHemisphere n)
        (identitySpecialOrthogonalSouthPoleHemisphere n) := by
    refine Set.disjoint_left.2 ?_
    intro x hpos hneg
    change
      0 < (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) at hpos
    change
      (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) < 0 at hneg
    exact (not_lt_of_ge (le_of_lt hpos)) hneg
  have hdisjPSE :
      Disjoint
        (identitySpecialOrthogonalNorthPoleHemisphere n ∪
          identitySpecialOrthogonalSouthPoleHemisphere n)
        (identitySpecialOrthogonalNorthPoleEquator n) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hzero
    change
      (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = 0 at hzero
    rcases hx with hpos | hneg
    · change
        0 < (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) at hpos
      exact (ne_of_gt hpos) hzero
    · change
        (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) < 0 at hneg
      exact (ne_of_lt hneg) hzero
  calc
    μ Set.univ =
        μ
          ((identitySpecialOrthogonalNorthPoleHemisphere n ∪
              identitySpecialOrthogonalSouthPoleHemisphere n) ∪
            identitySpecialOrthogonalNorthPoleEquator n) := by rw [huniv]
    _ =
        μ
            (identitySpecialOrthogonalNorthPoleHemisphere n ∪
              identitySpecialOrthogonalSouthPoleHemisphere n) +
          μ (identitySpecialOrthogonalNorthPoleEquator n) :=
      measure_union hdisjPSE
        (isClosed_identitySpecialOrthogonalNorthPoleEquator n).measurableSet
    _ =
        μ
            (identitySpecialOrthogonalNorthPoleHemisphere n ∪
              identitySpecialOrthogonalSouthPoleHemisphere n) := by
      rw [euclideanVolumeToSphere_identitySpecialOrthogonalNorthPoleEquator,
        add_zero]
    _ =
        μ (identitySpecialOrthogonalNorthPoleHemisphere n) +
          μ (identitySpecialOrthogonalSouthPoleHemisphere n) :=
      measure_union hdisjPS
        (isOpen_identitySpecialOrthogonalSouthPoleHemisphere n).measurableSet
    _ =
        μ (identitySpecialOrthogonalNorthPoleHemisphere n) +
          μ (identitySpecialOrthogonalNorthPoleHemisphere n) := by
      rw [euclideanVolumeToSphere_southPoleHemisphere_eq_northPoleHemisphere]
    _ =
        2 * μ (identitySpecialOrthogonalNorthPoleHemisphere n) := by
      rw [two_mul]

/-- The raw sphere mass of the positive north-pole hemisphere is precisely
the already defined consecutive-rank sphere step. -/
theorem euclideanVolumeToSphere_northPoleHemisphere_eq_sphereStep
    (n : ℕ) :
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        (identitySpecialOrthogonalNorthPoleHemisphere n) =
      identitySpecialOrthogonalSphereStep (n + 1) := by
  let μ :=
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
  calc
    μ (identitySpecialOrthogonalNorthPoleHemisphere n) =
        1 * μ (identitySpecialOrthogonalNorthPoleHemisphere n) := by simp
    _ =
        ((2 : ℝ≥0∞)⁻¹ * 2) *
          μ (identitySpecialOrthogonalNorthPoleHemisphere n) := by
      rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ =
        (2 : ℝ≥0∞)⁻¹ *
          (2 * μ (identitySpecialOrthogonalNorthPoleHemisphere n)) := by
      rw [mul_assoc]
    _ = (2 : ℝ≥0∞)⁻¹ * μ Set.univ := by
      rw [euclideanVolumeToSphere_univ_eq_two_mul_northPoleHemisphere]
    _ = identitySpecialOrthogonalSphereStep (n + 1) :=
      (identitySpecialOrthogonalSphereStep_eq_inv_two_mul_toSphere
        (n + 1) (by omega)).symm

/-- The total north-pole coordinate sphere measure is the sphere-step
factor, proved from the raw sphere measure rather than fixed by definition. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_eq_sphereStep
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n Set.univ =
      identitySpecialOrthogonalSphereStep (n + 1) := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ]
  exact euclideanVolumeToSphere_northPoleHemisphere_eq_sphereStep n

/-- Under the already normalized full-sphere measure, the positive
hemisphere has mass one half. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ_eq_inv_two
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure n
        Set.univ =
      (2 : ℝ≥0∞)⁻¹ := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_eq_smul,
    Measure.smul_apply,
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_eq_sphereStep,
    euclideanVolumeToSphere_univ_eq_two_mul_identitySpecialOrthogonalSphereStep
      (n + 1) (by omega),
    ENNReal.mul_inv]
  · change
      ((2 : ℝ≥0∞)⁻¹ *
          (identitySpecialOrthogonalSphereStep (n + 1))⁻¹) *
          identitySpecialOrthogonalSphereStep (n + 1) =
        (2 : ℝ≥0∞)⁻¹
    rw [mul_assoc,
      ENNReal.inv_mul_cancel
        (identitySpecialOrthogonalSphereStep_ne_zero (n + 1) (by omega))
        (identitySpecialOrthogonalSphereStep_ne_top (n + 1)),
      mul_one]
  · exact Or.inl (by norm_num)
  · exact Or.inl (by norm_num)

theorem
    identitySpecialOrthogonalNormalizedSphereMeasure_northPoleHemisphere_eq_inv_two
    (n : ℕ) :
    identitySpecialOrthogonalNormalizedSphereMeasure n
        (identitySpecialOrthogonalNorthPoleHemisphere n) =
      (2 : ℝ≥0∞)⁻¹ := by
  rw [←
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ]
  exact
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ_eq_inv_two
      n

/-- The positive-hemisphere coordinate sphere measure normalized by its
internally proved total mass. -/
def identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
    (n : ℕ) :
    Measure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (identitySpecialOrthogonalSphereStep (n + 1))⁻¹ •
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n

theorem
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure n
        Set.univ = 1 := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure,
    Measure.smul_apply,
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_eq_sphereStep]
  change
    (identitySpecialOrthogonalSphereStep (n + 1))⁻¹ *
        identitySpecialOrthogonalSphereStep (n + 1) =
      1
  exact ENNReal.inv_mul_cancel
    (identitySpecialOrthogonalSphereStep_ne_zero (n + 1) (by omega))
    (identitySpecialOrthogonalSphereStep_ne_top (n + 1))

/-- Recover the unnormalized hemisphere coordinate measure by multiplying its
probability normalization by the proved sphere-step mass. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_eq_sphereStep_smul_probability
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n =
      identitySpecialOrthogonalSphereStep (n + 1) •
        identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure
          n := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateHemisphereProbabilityMeasure,
    smul_smul]
  rw [ENNReal.mul_inv_cancel
      (identitySpecialOrthogonalSphereStep_ne_zero (n + 1) (by omega))
      (identitySpecialOrthogonalSphereStep_ne_top (n + 1)),
    one_smul]

end PositiveDefiniteIntegralLattice
