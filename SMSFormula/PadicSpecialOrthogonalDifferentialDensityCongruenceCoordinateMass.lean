import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruence
import SMSFormula.SkewAdjointPadicCoordinateBallFiniteDecomposition
import SMSFormula.SkewAdjointPadicUniformCoordinateBallMeasure

/-!
# Coordinate mass of the corrected-density-adapted congruence kernel

The inverse-Cayley source of the density-adapted principal kernel is included
literally in the transported skew-adjoint carrier.  Its ambient image is
compact-open, remains in the selected zero-centered constant-density ball,
and admits a finite pairwise-disjoint decomposition into translated uniform
coordinate balls at one common level.

Because the corrected source density is already constant on the whole kernel,
finite disjoint additivity and the explicit coordinate-ball mass give its
source differential mass as the zero-coordinate density times the number of
selected balls times the common coordinate-ball mass.

No finite-reduction index is cancelled and no raw congruence-solution set is
identified here.
-/

noncomputable section

open MeasureTheory
open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator Topology NNReal ENNReal Pointwise

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceCoordinateMassSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceCoordinateMassSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-! ## Literal ambient source -/

/-- The density-adapted inverse-Cayley kernel included literally in the
transported skew-adjoint carrier. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Subtype.val ''
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p

/-- Pulling the literal ambient density-adapted inverse source back through
the exact-source inclusion recovers the original exact-source set. -/
theorem
    preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ⁻¹'
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p := by
  ext X
  constructor
  · rintro ⟨Y, hY, hYX⟩
    have hYX' : Y = X := Subtype.ext hYX
    exact hYX' ▸ hY
  · intro hX
    exact ⟨X, hX, rfl⟩

/-- The literal ambient density-adapted inverse source is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p) := by
  exact
    (isOpen_skewAdjointPadicCayleySource L.rationalFormMatrix p)
      |>.isOpenEmbedding_subtypeVal.isOpenMap
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p)
        (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p)

/-- The literal ambient density-adapted inverse source is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p) :=
  (L.isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
    p).image continuous_subtype_val

/-- The literal ambient density-adapted inverse source is measurable. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    p).measurableSet

/-- The literal ambient density-adapted inverse source remains inside the
exact Cayley source. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_cayleySource
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ⊆
      skewAdjointPadicCayleySource L.rationalFormMatrix p := by
  rintro X ⟨x, hx, rfl⟩
  exact x.property

/-- The literal ambient density-adapted inverse source lies in the selected
zero-centered constant-density coordinate ball. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_densityBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ⊆
      skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p) := by
  rintro X ⟨x, hx, rfl⟩
  exact
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet_subset_densityBall
      p x hx

/-- Zero belongs to the literal ambient density-adapted inverse source. -/
theorem
    zero_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  let z :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
    ⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩
  refine ⟨z, ?_, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 z).1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        p
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  exact
    (L.coe_skewAdjointPadicCayleyTranslatedHomeomorph_one_zero p).symm

/-! ## Finite common-level coordinate decomposition -/

/-- The density-adapted inverse source is a finite pairwise-disjoint union of
translated uniform coordinate balls at one common level. -/
theorem
    exists_finite_pairwiseDisjoint_commonLevel_coordinateBall_cover_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ level : ℕ,
      ∃ balls : Set (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        balls.Finite ∧
        balls.PairwiseDisjoint id ∧
        (∀ B ∈ balls, ∃ x :
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              p,
          B = skewAdjointPadicTranslatedUniformCoordinateBall
            L.rationalFormMatrix p level x) ∧
        (∀ B ∈ balls,
          B ⊆
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              p) ∧
        (∀ B ∈ balls, IsCompact B) ∧
        (∀ B ∈ balls,
          B ⊆ skewAdjointPadicCayleySource L.rationalFormMatrix p) ∧
        ⋃₀ balls =
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
            p := by
  obtain ⟨level, balls, hfinite, hpairwise, hballs, hsubset, hcover⟩ :=
    exists_finite_pairwiseDisjoint_commonLevel_skewAdjointPadicTranslatedUniformCoordinateBall_cover
      L.rationalFormMatrix p
      (L.isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p)
      (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p)
  refine
    ⟨level, balls, hfinite, hpairwise, hballs, hsubset, ?_, ?_, hcover⟩
  · intro B hB
    obtain ⟨x, hx⟩ := hballs B hB
    rw [hx]
    exact
      isCompact_skewAdjointPadicTranslatedUniformCoordinateBall
        L.rationalFormMatrix p level x
  · intro B hB
    exact (hsubset B hB).trans
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_cayleySource
        p)

/-! ## Explicit corrected source mass -/

/-- The corrected source mass of the density-adapted inverse-Cayley kernel is
the explicit zero-coordinate density times the number of common-level balls
times their common coordinate-Haar mass.

The statement retains the exact finite common-level family and its chosen
centers, but does not combine this formula with the finite-index stabilizer
identity. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialDensityCongruenceSource_finite_mass_commonBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ level : ℕ,
      ∃ balls : Finset (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule),
        ∃ center :
            Set (skewAdjointMatricesLieSubalgebra
                (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
                p,
          (∀ B ∈ balls,
            B = skewAdjointPadicTranslatedUniformCoordinateBall
              L.rationalFormMatrix p level (center B)) ∧
          (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map
              (algebraMap ℚ ℚ_[p]))).toSubmodule)).PairwiseDisjoint id ∧
          (⋃ B ∈ balls, B) =
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
              p ∧
          skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
              p n L.rationalFormMatrix
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
                p) =
            (‖(2 : ℚ_[p])‖₊ ^
              Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix) : ℝ≥0∞) *
              (balls.card : ℝ≥0∞) *
              ((p : ℝ≥0∞) ^
                (level * Module.finrank ℚ
                  (skewAdjointMatricesLieSubalgebra
                    L.rationalFormMatrix)))⁻¹ := by
  classical
  let C :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      p
  let S := skewAdjointPadicCayleySource L.rationalFormMatrix p
  let density : S → ENNReal :=
    skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p n L.rationalFormMatrix
  let zeroDensity : ENNReal :=
    (‖(2 : ℚ_[p])‖₊ ^
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞)
  have hCS : C ⊆ S :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_cayleySource
      p
  obtain
      ⟨level, ballSet, hfinite, hpairwise, hball, hsubset, _hcompact,
        _hsource, hcover⟩ :=
    L.exists_finite_pairwiseDisjoint_commonLevel_coordinateBall_cover_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
      p
  let balls : Finset (Set (skewAdjointMatricesLieSubalgebra
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
    hfinite.toFinset
  let zeroCenter : C :=
    ⟨0,
      L.zero_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p⟩
  let center :
      Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        C := fun B =>
    if hB : B ∈ ballSet then Classical.choose (hball B hB) else zeroCenter
  have hmem_ballSet {B : Set (skewAdjointMatricesLieSubalgebra
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
      (hB : B ∈ balls) :
      B ∈ ballSet := by
    simpa only [balls, hfinite.mem_toFinset] using hB
  have hcenter : ∀ B ∈ balls,
      B = skewAdjointPadicTranslatedUniformCoordinateBall
        L.rationalFormMatrix p level (center B) := by
    intro B hB
    have hBset := hmem_ballSet hB
    simpa only [center, dif_pos hBset] using
      (Classical.choose_spec (hball B hBset))
  have hpairwise' :
      Set.PairwiseDisjoint
        (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule))
        id := by
    simpa only [balls, hfinite.coe_toFinset] using hpairwise
  have hsubset' : ∀ B ∈ balls, B ⊆ C := by
    intro B hB
    exact hsubset B (hmem_ballSet hB)
  have hcover' : (⋃ B ∈ balls, B) = C := by
    change
      (⋃ B ∈ balls, B) =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p
    rw [← hcover]
    ext X
    constructor
    · intro hX
      rcases Set.mem_iUnion.mp hX with ⟨B, hX⟩
      rcases Set.mem_iUnion.mp hX with ⟨hB, hXB⟩
      exact Set.mem_sUnion.mpr ⟨B, hmem_ballSet hB, hXB⟩
    · intro hX
      rcases Set.mem_sUnion.mp hX with ⟨B, hB, hXB⟩
      have hBballs : B ∈ balls := by
        change B ∈ hfinite.toFinset
        exact hfinite.mem_toFinset.mpr hB
      exact Set.mem_iUnion.mpr
        ⟨B, Set.mem_iUnion.mpr ⟨hBballs, hXB⟩⟩
  let internalBall :
      Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
        Set S := fun B => Subtype.val ⁻¹' B
  have hinternal_measurable : ∀ B ∈ balls,
      MeasurableSet (internalBall B) := by
    intro B hB
    rw [hcenter B hB]
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        L.rationalFormMatrix p level (center B)).1.measurableSet.preimage
          continuous_subtype_val.measurable
  have hinternal_pairwise :
      Set.PairwiseDisjoint
        (↑balls : Set (Set (skewAdjointMatricesLieSubalgebra
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule))
        internalBall := by
    intro B hB D hD hBD
    exact (hpairwise' hB hD hBD).preimage Subtype.val
  have hinternal_cover :
      (⋃ B ∈ balls, internalBall B) =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p := by
    rw [←
      L.preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_eq
        p]
    change
      (⋃ B ∈ balls, internalBall B) = Subtype.val ⁻¹' C
    rw [← hcover']
    ext X
    simp only [internalBall, Set.mem_iUnion, Set.mem_preimage]
  have hinternal_coordinateMass : ∀ B ∈ balls,
      skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p n L.rationalFormMatrix (internalBall B) =
        skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B := by
    intro B hB
    have himage : Subtype.val '' internalBall B = B := by
      ext X
      constructor
      · rintro ⟨Y, hY, rfl⟩
        exact hY
      · intro hX
        exact ⟨⟨X, hCS (hsubset' B hB hX)⟩, hX, rfl⟩
    rw [skewAdjointPadicCayleySourceCoordinateSubtypeMeasure,
      comap_subtype_coe_apply
        (isOpen_skewAdjointPadicCayleySource
          L.rationalFormMatrix p).measurableSet,
      himage]
  have hinternal_differentialMass : ∀ B ∈ balls,
      skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n L.rationalFormMatrix (internalBall B) =
        zeroDensity *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B := by
    intro B hB
    rw [skewAdjointPadicCayleySourceDifferentialSubtypeMeasure,
      withDensity_apply _ (hinternal_measurable B hB)]
    calc
      (∫⁻ X in internalBall B, density X
          ∂skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
            p n L.rationalFormMatrix) =
          ∫⁻ _ in internalBall B, zeroDensity
            ∂skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
              p n L.rationalFormMatrix := by
        apply setLIntegral_congr_fun (hinternal_measurable B hB)
        intro X hXB
        have hXC : X.1 ∈ C := hsubset' B hB hXB
        have hXsource :
            X ∈
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
                p := by
          rw [←
            L.preimage_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_eq
              p]
          exact hXC
        exact
          L.skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_zero_value_on_densityCongruenceSourceSet
            p X hXsource
      _ = zeroDensity *
          skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
            p n L.rationalFormMatrix (internalBall B) :=
        setLIntegral_const _ _
      _ = zeroDensity *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B := by
        rw [hinternal_coordinateMass B hB]
  have hmass :
      skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n L.rationalFormMatrix
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
            p) =
        ∑ B ∈ balls,
          zeroDensity *
            skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B := by
    calc
      skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p n L.rationalFormMatrix
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
            p) =
          skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
            p n L.rationalFormMatrix
            (⋃ B ∈ balls, internalBall B) := by
        rw [hinternal_cover]
      _ = ∑ B ∈ balls,
          skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
            p n L.rationalFormMatrix (internalBall B) :=
        measure_biUnion_finset hinternal_pairwise hinternal_measurable
      _ = ∑ B ∈ balls,
          zeroDensity *
            skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B := by
        apply Finset.sum_congr rfl
        intro B hB
        exact hinternal_differentialMass B hB
  refine ⟨level, balls, center, hcenter, hpairwise', hcover', ?_⟩
  rw [hmass]
  calc
    (∑ B ∈ balls,
        zeroDensity *
          skewAdjointPadicCoordinateMeasure L.rationalFormMatrix p B) =
        ∑ _B ∈ balls,
          zeroDensity *
            ((p : ℝ≥0∞) ^
              (level * Module.finrank ℚ
                (skewAdjointMatricesLieSubalgebra
                  L.rationalFormMatrix)))⁻¹ := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hcenter B hB,
        skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit]
    _ = (‖(2 : ℚ_[p])‖₊ ^
            Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix) : ℝ≥0∞) *
          (balls.card : ℝ≥0∞) *
          ((p : ℝ≥0∞) ^
            (level * Module.finrank ℚ
              (skewAdjointMatricesLieSubalgebra
                L.rationalFormMatrix)))⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, zeroDensity]
      ac_rfl

end PositiveDefiniteIntegralLattice
