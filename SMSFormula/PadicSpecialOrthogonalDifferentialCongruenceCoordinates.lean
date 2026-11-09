import SMSFormula.PadicSpecialOrthogonalDifferentialDeepCongruence
import SMSFormula.SkewAdjointPadicCoordinateBallBasis

/-!
# Deep special congruence kernels in fixed p-adic Cayley coordinates

The first deep-congruence construction places a principal kernel in the
identity-centered Cayley target.  This module refines the chosen depth so that
the inverse Cayley image lies in the fixed rationally transported coordinate
lattice.

The refinement is topological and basis-respecting.  The coordinate lattice
inside the exact Cayley source is an open neighborhood of zero, so its chart
image is an open identity neighborhood.  The already proved
principal-congruence neighborhood basis supplies a deeper kernel inside it.
Conversely, the inverse image of that kernel is open at zero, hence contains a
uniform coordinate ball.  Thus the refined inverse-Cayley kernel is
sandwiched between a uniform coordinate ball and the level-zero coordinate
ball.  No coordinate mass is evaluated here.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceCoordinatesSourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceCoordinatesSourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceCoordinatesGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceCoordinatesGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The part of the exact identity-centered Cayley source lying in the fixed
transported coordinate lattice. -/
def localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) :=
  Subtype.val ⁻¹'
    (skewAdjointPadicCoordinateLattice L.rationalFormMatrix p : Set _)

/-- The coordinate-lattice part of the exact source is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
        p) :=
  (isClopen_skewAdjointPadicCoordinateLattice
    L.rationalFormMatrix p).2.preimage continuous_subtype_val

/-- Zero belongs to the coordinate-lattice part of the exact source. -/
theorem
    zero_mem_localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩ :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) ∈
        L.localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
          p :=
  zero_mem_skewAdjointPadicCoordinateLattice L.rationalFormMatrix p

/-- The identity-centered translated Cayley chart sends zero to the group
identity. -/
theorem
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_one_zero
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
        ⟨0, zero_mem_skewAdjointPadicCayleySource
          L.rationalFormMatrix p⟩).1 =
      (1 :
        specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  simp [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]

/-- The coordinate-lattice source neighborhood transported to the ambient
p-adic special-orthogonal group by the identity-centered Cayley chart. -/
def localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Subtype.val ''
    ((skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ''
      L.localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood p)

/-- The transported coordinate-lattice source neighborhood is open in the
ambient p-adic special-orthogonal group. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
        p) := by
  have hsource : IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
        p) :=
    L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
      p
  have htarget : IsOpen
      ((skewAdjointPadicCayleyTranslatedHomeomorph
          L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ''
        L.localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
          p) :=
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).isOpenMap
        _ hsource
  exact
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1).isOpenEmbedding_subtypeVal.isOpenMap _ htarget

/-- The ambient coordinate target neighborhood contains the identity. -/
theorem
    one_mem_localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (1 :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
        p := by
  let z :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
    ⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
  refine ⟨e z, ⟨z, ?_, rfl⟩, ?_⟩
  · exact
      L.zero_mem_localPadicSpecialOrthogonalDifferentialCoordinateSourceNeighborhood
        p
  · exact L.coe_skewAdjointPadicCayleyTranslatedHomeomorph_one_zero p

/-- Some direct principal-congruence kernel lies in the transported
coordinate-lattice Cayley neighborhood. -/
theorem
    exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_coordinateTarget
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ k, ∀
      g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p,
      g ∈
          L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p k →
        (g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
          L.localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
            p := by
  let U : Set
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :=
    {g |
      (g :
        specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
        L.localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
          p}
  have hU : IsOpen U :=
    (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
      p).preimage continuous_subtype_val
  have hone : (1 :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) ∈ U :=
    L.one_mem_localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
      p
  rcases
      L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset
        p hU hone with
    ⟨k, hk⟩
  exact ⟨k, fun g hg ↦ hk hg⟩

/-- A chosen coordinate-adapted principal-congruence depth. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_coordinateTarget
      p)

/-- The chosen coordinate-adapted kernel lies in the transported
coordinate-lattice Cayley neighborhood. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth_spec
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
          p)) :
    (g :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateTargetNeighborhood
        p :=
  Classical.choose_spec
    (L.exists_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_subset_coordinateTarget
      p) g hg

/-- The coordinate-adapted direct kernel as a literal ambient subset. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  Subtype.val ''
    (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth p) :
      Set
        (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p))

/-- The coordinate-adapted direct kernel is open in the ambient p-adic
special-orthogonal group. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
        p) := by
  exact
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      |>.isOpenEmbedding_subtypeVal.isOpenMap
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
            p))
        (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
            p))

/-- The coordinate-adapted direct kernel is compact in the ambient p-adic
special-orthogonal group. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
        p) := by
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth p)
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp
      (L.isCompact_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
  have hKclosed : IsClosed (K : Set D) :=
    K.isClosed_of_isOpen
      (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth p))
  exact hKclosed.isCompact.image continuous_subtype_val

/-- The coordinate-adapted direct kernel lies in the identity-centered exact
translated Cayley target. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet_subset_target
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet p ⊆
      padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1 := by
  rintro g ⟨h, hh, rfl⟩
  rcases
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth_spec
        p h hh with
    ⟨y, -, hy⟩
  exact hy ▸ y.property

/-- A direct-kernel element represented in the exact identity-centered
translated Cayley target. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetPoint
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
          p)) :
    padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1 :=
  ⟨g,
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet_subset_target
      p ⟨g, hg, rfl⟩⟩

/-- The inverse Cayley coordinate of a coordinate-adapted direct-kernel
element. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
          p)) :
    Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
    L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).symm
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetPoint
        p g hg)

/-- On the coordinate-adapted direct kernel, the identity-centered inverse
Cayley coordinate is literally `(g + 1)⁻¹ * (g - 1)`. -/
theorem
    coe_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
          p)) :
    ((L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley
        p g hg).1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        (((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
  rw [
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley,
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply]
  simp [
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetPoint]

/-- The coordinate-adapted kernel represented in the exact identity-centered
target subtype. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (padicCayleySpecialOrthogonalTranslatedTarget
        L.rationalFormMatrix p 1) :=
  Subtype.val ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet p

/-- The coordinate-adapted kernel pulled back to the exact Cayley source. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set (Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1) ⁻¹'
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet p

/-- The coordinate-adapted inverse-Cayley kernel as a literal subset of the
transported skew-adjoint carrier. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Set
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  Subtype.val ''
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet p

/-- Including the exact-target coordinate-adapted kernel recovers its ambient
representation. -/
theorem
    image_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ''
        L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
          p =
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
        p := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hg
    exact
      ⟨⟨g,
          L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet_subset_target
            p hg⟩,
        hg, rfl⟩

/-- The exact-target representation of the coordinate-adapted kernel is
open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
        p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
    p).preimage continuous_subtype_val

/-- The exact-target representation of the coordinate-adapted kernel is
compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
        p) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
    L.image_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
      p]
  exact
    L.isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
      p

/-- The exact-source representation of the coordinate-adapted kernel is
open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
        p) :=
  ((L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
      p).preimage continuous_subtype_val).preimage
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).continuous

/-- The exact-source representation of the coordinate-adapted kernel is
compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
        p) :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
    L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1)
      |>.isCompact_preimage.mpr
        (L.isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
          p)

/-- The exact-source representation of the coordinate-adapted kernel is
measurable. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
        p) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    p).measurableSet

/-- The literal ambient inverse-Cayley kernel is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p) := by
  exact
    (isOpen_skewAdjointPadicCayleySource L.rationalFormMatrix p)
      |>.isOpenEmbedding_subtypeVal.isOpenMap
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
          p)
        (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
          p)

/-- The literal ambient inverse-Cayley kernel is compact. -/
theorem
    isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p) :=
  (L.isCompact_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
    p).image continuous_subtype_val

/-- Zero belongs to the coordinate-adapted inverse-Cayley kernel. -/
theorem
    zero_mem_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p := by
  let z :
      Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
    ⟨0, zero_mem_skewAdjointPadicCayleySource L.rationalFormMatrix p⟩
  refine ⟨z, ?_, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 z).1 ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
        p
  refine ⟨1, ?_, ?_⟩
  · exact Subgroup.one_mem _
  · exact
      (L.coe_skewAdjointPadicCayleyTranslatedHomeomorph_one_zero p).symm

/-- The coordinate-adapted inverse-Cayley kernel lies in the fixed transported
coordinate lattice. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet_subset_lattice
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p ⊆
      (skewAdjointPadicCoordinateLattice L.rationalFormMatrix p : Set _) := by
  rintro X ⟨x, hx, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1 x).1 ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
        p at hx
  rcases hx with ⟨g, hg, hgeq⟩
  rcases
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth_spec
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
  change x.1 ∈
    (skewAdjointPadicCoordinateLattice L.rationalFormMatrix p : Set _)
  exact hxz ▸ hz

/-- Every explicit inverse Cayley coordinate of the coordinate-adapted direct
kernel belongs to the fixed transported coordinate lattice. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley_mem_lattice
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
          p)) :
    (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley
        p g hg).1 ∈
      (skewAdjointPadicCoordinateLattice L.rationalFormMatrix p : Set _) := by
  apply
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet_subset_lattice
      p
  refine
    ⟨L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInverseCayley
      p g hg, ?_, rfl⟩
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1)
        ((skewAdjointPadicCayleyTranslatedHomeomorph
          L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).symm
            (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetPoint
              p g hg)) ∈
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet p
  rw [
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).apply_symm_apply]
  exact ⟨g, hg, rfl⟩

/-- Some uniform coordinate ball lies inside the coordinate-adapted
inverse-Cayley kernel. -/
theorem
    exists_skewAdjointPadicUniformCoordinateBall_subset_coordinateCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ r,
      skewAdjointPadicUniformCoordinateBall L.rationalFormMatrix p r ⊆
        L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
          p := by
  exact
    exists_skewAdjointPadicUniformCoordinateBall_subset_of_mem_nhds_zero
      L.rationalFormMatrix p
      ((L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
          p).mem_nhds
        (L.zero_mem_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
          p))

/-- A chosen inner coordinate-ball level for the coordinate-adapted
inverse-Cayley kernel. -/
def localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInnerLevel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (L.exists_skewAdjointPadicUniformCoordinateBall_subset_coordinateCongruenceSourceAmbientSet
      p)

/-- The chosen inner coordinate ball lies inside the coordinate-adapted
inverse-Cayley kernel. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInnerLevel_spec
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInnerLevel
          p) ⊆
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p :=
  Classical.choose_spec
    (L.exists_skewAdjointPadicUniformCoordinateBall_subset_coordinateCongruenceSourceAmbientSet
      p)

/-- The coordinate-adapted inverse-Cayley kernel is sandwiched between a
uniform coordinate ball and the level-zero uniform coordinate ball. -/
theorem
    localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet_sandwich
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicUniformCoordinateBall
        L.rationalFormMatrix p
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInnerLevel
          p) ⊆
      L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p ∧
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet
        p ⊆
      skewAdjointPadicUniformCoordinateBall L.rationalFormMatrix p 0 := by
  refine
    ⟨L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceInnerLevel_spec
      p, ?_⟩
  intro X hX
  refine ⟨X,
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceAmbientSet_subset_lattice
      p hX, ?_⟩
  simp

/-! ## Corrected differential mass at the coordinate-adapted depth -/

/-- Exact target recovery identifies the coordinate-adapted target mass with
the global corrected mass of the literal ambient kernel. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_coordinateCongruenceTargetSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
          p) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
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
    L.image_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
      p]

/-- The corrected source mass of the coordinate-adapted inverse-Cayley kernel
is its exact target differential mass. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_coordinateCongruenceSourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
          p) =
      padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero 1
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
          p) := by
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure,
    Measure.map_apply
      (skewAdjointPadicCayleyTranslatedHomeomorph
        L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).measurable
      (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceTargetSet
        p).measurableSet]
  rfl

/-- The corrected stabilizer mass of the coordinate-adapted principal kernel
is the global corrected mass of its ambient representation. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasure_coordinateCongruenceKernel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p
            (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
              p) :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
          p) := by
  let G :=
    specialFormPreservingMatrixSubgroup
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
  let D :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p
  let K :=
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
      p
      (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth p)
  let μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure
      p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero
  let ν := L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
  let A :=
    L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet p
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
    (L.isOpen_localPadicSpecialOrthogonalDifferentialCoordinateCongruenceAmbientSet
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

/-- The coordinate-adapted inverse-Cayley kernel also satisfies the finite-index
corrected stabilizer-mass formula. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_coordinateCongruenceSourceSet_eq_volume_mul_inv_natCard_range
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
        p n L.rationalFormMatrix
        (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceSourceSet
          p) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (Nat.card
          (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
            p
            (L.localPadicSpecialOrthogonalDifferentialCoordinateCongruenceDepth
              p)).range : ℝ≥0∞)⁻¹ := by
  rw [
    L.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_coordinateCongruenceSourceSet
      p,
    L.padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_coordinateCongruenceTargetSet
      p,
    ←
      L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_coordinateCongruenceKernel
        p,
    L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_measure
      p]

end PositiveDefiniteIntegralLattice
