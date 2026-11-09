import SMSFormula.PadicSpecialOrthogonalDifferentialCongruenceCoordinates
import SMSFormula.PadicCayleyTranslatedChartDifferentialZeroNeighborhood

/-!
# A corrected-density-adapted p-adic special congruence kernel

The corrected Cayley source density is constant at its zero-coordinate value
on one selected uniform coordinate ball.  Mapping this ball through the
identity-centered translated Cayley chart gives an open identity
neighborhood.  The direct principal-congruence neighborhood basis therefore
supplies a further kernel whose inverse Cayley image lies entirely in that
ball.

This module packages the compact-open exact source set, its direct kernel
mass, and the finite-index stabilizer-volume identity.  It does not evaluate
the coordinate mass of the source set.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-! ## The selected zero-density coordinate ball -/

/-- A chosen zero-centered coordinate-ball level on which the corrected
Cayley source density is constant at its zero-coordinate value. -/
def localPadicSpecialOrthogonalDifferentialDensityBallLevel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (Matrix.exists_skewAdjointPadicUniformCoordinateBall_subset_cayleySource_const_differentialDensity
      p n L.rationalFormMatrix)

/-- The selected zero-centered coordinate ball lies in the exact Cayley
source. -/
theorem localPadicSpecialOrthogonalDifferentialDensityBall_subset_cayleySource
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p) ⊆
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
  Classical.choose
    (Classical.choose_spec
      (Matrix.exists_skewAdjointPadicUniformCoordinateBall_subset_cayleySource_const_differentialDensity
        p n L.rationalFormMatrix))

/-- The corrected source density is the zero-coordinate value throughout the
selected coordinate ball. -/
theorem
    skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_zero_value_on_densityBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p)) :
    Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p n L.rationalFormMatrix
        ⟨X,
          L.localPadicSpecialOrthogonalDifferentialDensityBall_subset_cayleySource
            p hX⟩ =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞) := by
  exact
    Classical.choose_spec
      (Classical.choose_spec
        (Matrix.exists_skewAdjointPadicUniformCoordinateBall_subset_cayleySource_const_differentialDensity
          p n L.rationalFormMatrix)) X hX

/-- The selected coordinate ball represented inside the exact Cayley source. -/
def localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) :=
  Subtype.val ⁻¹'
    skewAdjointPadicUniformCoordinateBall
      L.rationalFormMatrix p
      (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p)

/-- The selected exact-source coordinate ball is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood p) :=
  (isClopen_skewAdjointPadicUniformCoordinateBall
    L.rationalFormMatrix p
    (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p)).2.preimage
      continuous_subtype_val

/-- Zero belongs to the selected exact-source coordinate ball. -/
theorem
    zero_mem_localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩ :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) ∈
        L.localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood p :=
  zero_mem_skewAdjointPadicUniformCoordinateBall
    L.rationalFormMatrix p
    (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p)

/-! ## The density-adapted principal-congruence depth -/

/-- The selected constant-density source ball transported to the ambient
p-adic special-orthogonal group. -/
def localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Subtype.val ''
    ((skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ''
      L.localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood p)

/-- The transported constant-density source ball is open in the ambient
p-adic special-orthogonal group. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood p) := by
  have htarget : IsOpen
      ((skewAdjointPadicCayleyTranslatedHomeomorph
          L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ''
        L.localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood p) :=
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).isOpenMap
        _
        (L.isOpen_localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood
          p)
  exact
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1).isOpenEmbedding_subtypeVal.isOpenMap _ htarget

/-- The ambient transported constant-density neighborhood contains the
identity. -/
theorem
    one_mem_localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (1 :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
      L.localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood p := by
  let z :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
    ⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
  refine ⟨e z, ⟨z, ?_, rfl⟩, ?_⟩
  · exact
      L.zero_mem_localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood
        p
  · exact L.coe_skewAdjointPadicCayleyTranslatedHomeomorph_one_zero p

/-- Some direct principal-congruence kernel at a Schulze--Pillot Hensel
exponent lies in the transported constant-density source ball. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ k, 2 ≤ k ∧
      localDensityHenselExponent L p ≤ k ∧
        IsLocalDensityHenselExponent L p k ∧
          ∀ g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p,
            g ∈
                L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
                  p k →
              (g :
                specialFormPreservingMatrixSubgroup
                  (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
                L.localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
                  p := by
  let U : Set
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :=
    {g |
      (g :
        specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
        L.localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood p}
  have hU : IsOpen U :=
    (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
      p).preimage continuous_subtype_val
  have hone : (1 :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) ∈ U :=
    L.one_mem_localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood
      p
  rcases
      L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset
        p hU hone with
    ⟨k, hk⟩
  let h := localDensityHenselExponent L p
  let K := max (max k 2) h
  have htwo : 2 ≤ K := by
    exact
      (Nat.le_max_right k 2).trans
        (Nat.le_max_left (max k 2) h)
  have hhK : h ≤ K :=
    Nat.le_max_right (max k 2) h
  have hHensel : IsLocalDensityHenselExponent L p K := by
    have hh : IsLocalDensityHenselExponent L p h := by
      simpa [h] using
        (isLocalDensityHenselExponent_preferred (n := n) L p)
    simpa only [Nat.add_sub_of_le hhK] using
      hh.add L p h (K - h)
  refine ⟨K, htwo, by simpa [h] using hhK, hHensel, ?_⟩
  intro g hg
  apply hk
  have hghistorical :=
    (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
      p K g).mp hg
  have hkK : k ≤ K :=
    (Nat.le_max_left k 2).trans
      (Nat.le_max_left (max k 2) h)
  have hghistorical' :=
    L.antitone_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup
      p hkK hghistorical
  exact
    (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
      p k g).mpr hghistorical'

/-- A chosen principal-congruence depth adapted to the constant-density
coordinate ball. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
      p)

/-- The chosen density-adapted principal-congruence depth is at least two. -/
theorem
    two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    2 ≤ L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
      p)).1

/-- The preferred determinant-depth Hensel exponent is no larger than the
chosen corrected differential density depth. -/
theorem
    localDensityHenselExponent_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    localDensityHenselExponent L p ≤
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
      p)).2.1

/-- The discriminant valuation is no larger than the chosen corrected
differential density depth. -/
theorem
    padicValInt_polarDeterminant_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicValInt p L.polarDeterminant ≤
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p := by
  have h :=
    L.localDensityHenselExponent_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
      p
  unfold localDensityHenselExponent at h
  omega

/-- The chosen density-adapted principal-congruence depth lies in the
Schulze--Pillot quantitative Hensel range. -/
theorem
    isLocalDensityHenselExponent_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalDensityHenselExponent L p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
      p)).2.2.1

/-- The chosen density-adapted kernel lies in the transported
constant-density neighborhood. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_spec
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :
    (g :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
      L.localPadicSpecialOrthogonalDifferentialDensityTargetNeighborhood p :=
  (Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_densityTarget
      p)).2.2.2 g hg

/-! ## Exact target and source representations -/

/-- The density-adapted direct kernel as a literal ambient subset. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Subtype.val ''
    (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) :
      Set
        (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p))

/-- The density-adapted direct kernel is open in the ambient group. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        p) := by
  exact
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      |>.isOpenEmbedding_subtypeVal.isOpenMap
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))
        (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))

/-- The density-adapted direct kernel is compact in the ambient group. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        p) := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp
      (L.isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
  have hKclosed : IsClosed (K : Set D) :=
    K.isClosed_of_isOpen
      (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))
  exact hKclosed.isCompact.image continuous_subtype_val

/-- The density-adapted ambient kernel lies in the identity-centered exact
translated Cayley target. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet_subset_target
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet p ⊆
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 := by
  rintro g ⟨h, hh, rfl⟩
  rcases
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_spec
        p h hh with
    ⟨y, -, hy⟩
  exact hy ▸ y.property

/-- The density-adapted kernel represented inside the exact
identity-centered translated target. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1) :=
  Subtype.val ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet p

/-- The density-adapted kernel pulled back to the exact Cayley source. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet p

/-- Including the exact-target density-adapted kernel recovers its ambient
representation. -/
theorem
    image_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ''
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet p =
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        p := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hg
    exact
      ⟨⟨g,
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet_subset_target
            p hg⟩,
        hg, rfl⟩

/-- The exact-target density-adapted kernel is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
    p).preimage continuous_subtype_val

/-- The exact-target density-adapted kernel is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet p) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
    L.image_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
      p]
  exact
    L.isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
      p

/-- The inverse-Cayley density-adapted source set is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p) :=
  ((L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
      p).preimage continuous_subtype_val).preimage
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).continuous

/-- The inverse-Cayley density-adapted source set is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
    L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1)
      |>.isCompact_preimage.mpr
        (L.isCompact_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
          p)

/-- The inverse-Cayley density-adapted source set is measurable. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p)
    |>.measurableSet

/-! ## Containment and corrected-density constancy -/

/-- The density-adapted inverse-Cayley source lies in the selected
zero-centered constant-density ball. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet_subset_densitySourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p ⊆
      L.localPadicSpecialOrthogonalDifferentialDensitySourceNeighborhood p := by
  intro x hx
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 x).1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
        p at hx
  rcases hx with ⟨g, hg, hgeq⟩
  rcases
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth_spec
        p g hg with
    ⟨y, ⟨z, hz, hzy⟩, hyg⟩
  have hxy :
      skewAdjointPadicCayleyTranslatedHomeomorph
          L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 x =
        y := by
    apply Subtype.ext
    exact (hyg.trans hgeq).symm
  have hxz : x = z := by
    apply
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).injective
    exact hxy.trans hzy.symm
  exact hxz ▸ hz

/-- Every underlying coordinate of the density-adapted inverse-Cayley source
belongs to the selected zero-centered uniform coordinate ball. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet_subset_densityBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p)
    (hX :
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) :
    X.1 ∈
      skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p) :=
  L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet_subset_densitySourceNeighborhood
    p hX

/-- The corrected source density has its explicit zero-coordinate value on
the whole density-adapted inverse-Cayley kernel. -/
theorem
    skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_zero_value_on_densityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p)
    (hX :
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) :
    Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
        p n L.rationalFormMatrix X =
      (‖(2 : ℚ_[p])‖₊ ^
        Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra L.rationalFormMatrix) : ℝ≥0∞) := by
  have hball :
      X.1 ∈
        skewAdjointPadicUniformCoordinateBall
          L.rationalFormMatrix p
          (L.localPadicSpecialOrthogonalDifferentialDensityBallLevel p) :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet_subset_densityBall
      p X hX
  simpa only [Subtype.coe_eta] using
    L.skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_zero_value_on_densityBall
      p X.1 hball

/-! ## Literal corrected differential mass -/

/-- Exact target recovery identifies the density-adapted target mass with the
global corrected mass of the literal ambient kernel. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_densityCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
          p) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
          p) := by
  have hFsymm : L.rationalFormMatrix.IsSymm := L.form_symm.map _
  rw [←
    comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
      p n L.rationalFormMatrix hFsymm
        L.rationalFormMatrix_det_ne_zero 1]
  rw [comap_subtype_coe_apply
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1).measurableSet]
  rw [
    L.image_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
      p]

/-- The corrected source mass of the density-adapted inverse-Cayley kernel is
its exact target differential mass. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
          p) := by
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure,
    Measure.map_apply
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).measurable
      (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet
        p).measurableSet]
  rfl

/-- The corrected stabilizer mass of the density-adapted principal kernel is
the global corrected mass of its ambient representation. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasure_densityCongruenceKernel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
          p) := by
  let G :=
    specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  let μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure
      p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
  let ν := L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
  let A :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet p
  have hmap : Measure.map (fun g : D ↦ (g : G)) ν =
      μ.restrict (D : Set G) := by
    change
      Measure.map (fun g : D ↦ (g : G))
          (Measure.comap (fun g : D ↦ (g : G)) μ) =
        μ.restrict (D : Set G)
    exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace D
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace_eq p)
      (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
        p).measurableSet
  have hAmeas : MeasurableSet A :=
    (L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet
      p).measurableSet
  have hpre : (fun g : D ↦ (g : G)) ⁻¹' A = (K : Set D) := by
    ext g
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨h, hh, heq⟩
      have hhg : h = g := Subtype.ext heq
      exact hhg ▸ hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hAsub : A ⊆ (D : Set G) := by
    rintro g ⟨h, hh, rfl⟩
    exact h.property
  change ν (K : Set D) = μ A
  calc
    ν (K : Set D) =
        Measure.map (fun g : D ↦ (g : G)) ν A := by
      rw [Measure.map_apply continuous_subtype_val.measurable hAmeas, hpre]
    _ = μ.restrict (D : Set G) A :=
      congrArg (fun ρ : Measure G ↦ ρ A) hmap
    _ = μ A := by
      rw [Measure.restrict_apply hAmeas, Set.inter_eq_left.mpr hAsub]

/-- The density-adapted inverse-Cayley source mass is the literal corrected
mass of its direct principal-congruence kernel. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_stabilizerMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p) :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) := by
  rw [
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet
      p,
    L.padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_densityCongruenceTargetSet
      p,
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_densityCongruenceKernel
      p]

/-- The density-adapted inverse-Cayley source satisfies the finite-index
corrected stabilizer-volume identity with the reduction image. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_volume_mul_inv_natCard_range
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (Nat.card
          (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
            p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
              p)).range : ℝ≥0∞)⁻¹ := by
  rw [
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_densityCongruenceSourceSet_eq_stabilizerMeasure
      p,
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_measure
      p]

end PositiveDefiniteIntegralLattice
