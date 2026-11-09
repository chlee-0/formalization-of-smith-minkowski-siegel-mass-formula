import SMSFormula.RationalCliffordSpinCandidateAdelicCarrier
import Mathlib.Topology.Algebra.Algebra

/-!
# Finite-coordinate topology on Clifford--Spin candidate points

For a topological commutative rational algebra `A`, candidate points are
embedded into the finite product consisting of all Clifford-basis
coefficients and all matrix entries.  This file installs the induced topology
and proves that scalar extension is continuous whenever the scalar map is.

This is the topological carrier precursor.  Continuity of multiplication and
inversion, local compactness, restricted-product identifications, and all
measure constructions are left to subsequent layers.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- All finite coordinates of a Clifford--Spin candidate point: first its
Clifford-basis coefficients, then its special-orthogonal matrix entries. -/
def cliffordSpinCandidatePointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    V.CliffordSpinCandidateGroup A →
      (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A :=
  fun x =>
    (fun u => x (V.cliffordSpinCandidateCliffordCoordinate u),
      fun i j => x (V.cliffordSpinCandidateMatrixCoordinate i j))

@[simp]
theorem cliffordSpinCandidatePointCoordinateMap_fst
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A) (u : Finset (Fin n)) :
    (V.cliffordSpinCandidatePointCoordinateMap A x).1 u =
      x (V.cliffordSpinCandidateCliffordCoordinate u) :=
  rfl

@[simp]
theorem cliffordSpinCandidatePointCoordinateMap_snd
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A) (i j : Fin n) :
    (V.cliffordSpinCandidatePointCoordinateMap A x).2 i j =
      x (V.cliffordSpinCandidateMatrixCoordinate i j) :=
  rfl

/-- The finite coordinate family determines a candidate point. -/
theorem cliffordSpinCandidatePointCoordinateMap_injective
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (V.cliffordSpinCandidatePointCoordinateMap A) := by
  intro x y hxy
  apply (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).injective
  change V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x =
    V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A y
  apply CliffordSpinCandidatePointData.ext
  · apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
    ext u
    rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
    exact congrArg (fun z => z.1 u) hxy
  · apply Subtype.ext
    ext i j
    rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
    exact congrArg (fun z => z.2 i j) hxy

/-- The natural topology on candidate points is the topology induced by all
finite Clifford and matrix coordinates. -/
noncomputable instance cliffordSpinCandidateGroupTopologicalSpace
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    TopologicalSpace (V.CliffordSpinCandidateGroup A) :=
  TopologicalSpace.induced
    (V.cliffordSpinCandidatePointCoordinateMap A) inferInstance

/-- The coordinate map is a topological embedding by construction. -/
theorem cliffordSpinCandidatePointCoordinateMap_isEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    Topology.IsEmbedding (V.cliffordSpinCandidatePointCoordinateMap A) :=
  (V.cliffordSpinCandidatePointCoordinateMap_injective A).isEmbedding_induced

/-- The simultaneous finite-coordinate map is continuous. -/
theorem continuous_cliffordSpinCandidatePointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    Continuous (V.cliffordSpinCandidatePointCoordinateMap A) :=
  (V.cliffordSpinCandidatePointCoordinateMap_isEmbedding A).continuous

/-- Each Clifford-basis coordinate is continuous. -/
theorem continuous_cliffordSpinCandidateCliffordCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (u : Finset (Fin n)) :
    Continuous (fun x : V.CliffordSpinCandidateGroup A =>
      x (V.cliffordSpinCandidateCliffordCoordinate u)) := by
  exact ((continuous_apply u).comp continuous_fst).comp
    (V.continuous_cliffordSpinCandidatePointCoordinateMap A)

/-- Each matrix coordinate is continuous. -/
theorem continuous_cliffordSpinCandidateMatrixCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (i j : Fin n) :
    Continuous (fun x : V.CliffordSpinCandidateGroup A =>
      x (V.cliffordSpinCandidateMatrixCoordinate i j)) := by
  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).comp
    (V.continuous_cliffordSpinCandidatePointCoordinateMap A)

/-- Hausdorffness descends from the ambient finite coordinate space. -/
noncomputable instance cliffordSpinCandidateGroupT2Space
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [T2Space A] :
    T2Space (V.CliffordSpinCandidateGroup A) :=
  (V.cliffordSpinCandidatePointCoordinateMap_isEmbedding A).t2Space

/-- Scalar extension acts coordinatewise on the finite coordinate map. -/
theorem cliffordSpinCandidatePointCoordinateMap_groupMap
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidatePointCoordinateMap B
        (V.cliffordSpinCandidateGroupMap f x) =
      ((fun u => f ((V.cliffordSpinCandidatePointCoordinateMap A x).1 u)),
        fun i j => f ((V.cliffordSpinCandidatePointCoordinateMap A x).2 i j)) :=
  rfl

/-- Clifford coordinates of a product are finite polynomial expressions in
the two coordinate families. -/
theorem cliffordSpinCandidatePointCoordinateMap_mul_fst
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : V.CliffordSpinCandidateGroup A) (u : Finset (Fin n)) :
    (V.cliffordSpinCandidatePointCoordinateMap A (x * y)).1 u =
      ∑ s, ∑ t,
        (V.cliffordSpinCandidatePointCoordinateMap A x).1 s *
          (V.cliffordSpinCandidatePointCoordinateMap A y).1 t *
          algebraMap ℚ A (V.cliffordMulStructureConstant s t u) := by
  have h := congrArg
    (fun d : V.CliffordSpinCandidatePointData A =>
      (V.cliffordCoordinateBaseChangeBasis A).repr d.clifford u)
    (map_mul (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) x y)
  simpa only [V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData_apply,
    V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr,
    CliffordSpinCandidatePointData.mul_clifford,
    V.cliffordCoordinateBaseChangeBasis_repr_mul] using h

/-- Matrix coordinates of a product are the usual finite matrix-product
expressions. -/
theorem cliffordSpinCandidatePointCoordinateMap_mul_snd
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : V.CliffordSpinCandidateGroup A) (i j : Fin n) :
    (V.cliffordSpinCandidatePointCoordinateMap A (x * y)).2 i j =
      ∑ k,
        (V.cliffordSpinCandidatePointCoordinateMap A x).2 i k *
          (V.cliffordSpinCandidatePointCoordinateMap A y).2 k j := by
  have h := congrArg
    (fun d : V.CliffordSpinCandidatePointData A => d.matrixPoint.1 i j)
    (map_mul (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) x y)
  simpa only [V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData_apply,
    V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply,
    CliffordSpinCandidatePointData.mul_matrixPoint,
    V.cliffordSpinCandidateMatrixPointMul_apply] using h

/-- Multiplication is continuous for the induced finite-coordinate
topology. -/
theorem continuous_mul_cliffordSpinCandidateGroup
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun z : V.CliffordSpinCandidateGroup A ×
      V.CliffordSpinCandidateGroup A => z.1 * z.2) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro u
    change Continuous (fun z : V.CliffordSpinCandidateGroup A ×
      V.CliffordSpinCandidateGroup A =>
        (V.cliffordSpinCandidatePointCoordinateMap A (z.1 * z.2)).1 u)
    simp_rw [V.cliffordSpinCandidatePointCoordinateMap_mul_fst A]
    apply continuous_finset_sum
    intro s _
    apply continuous_finset_sum
    intro t _
    exact (((V.continuous_cliffordSpinCandidateCliffordCoordinate A s).comp
      continuous_fst).mul
        ((V.continuous_cliffordSpinCandidateCliffordCoordinate A t).comp
          continuous_snd)).mul continuous_const
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun z : V.CliffordSpinCandidateGroup A ×
      V.CliffordSpinCandidateGroup A =>
        (V.cliffordSpinCandidatePointCoordinateMap A (z.1 * z.2)).2 i j)
    simp_rw [V.cliffordSpinCandidatePointCoordinateMap_mul_snd A]
    apply continuous_finset_sum
    intro k _
    exact ((V.continuous_cliffordSpinCandidateMatrixCoordinate A i k).comp
      continuous_fst).mul
        ((V.continuous_cliffordSpinCandidateMatrixCoordinate A k j).comp
          continuous_snd)

/-- Candidate multiplication is continuous in the finite-coordinate
topology. -/
noncomputable instance cliffordSpinCandidateGroupContinuousMul
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    ContinuousMul (V.CliffordSpinCandidateGroup A) where
  continuous_mul := V.continuous_mul_cliffordSpinCandidateGroup A

/-- A continuous scalar map induces a continuous map of candidate point
carriers. -/
theorem continuous_cliffordSpinCandidateGroupMap
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    (f : A →ₐ[ℚ] B) (hf : Continuous f) :
    Continuous (V.cliffordSpinCandidateGroupMap f) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro u
    exact hf.comp (V.continuous_cliffordSpinCandidateCliffordCoordinate A u)
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact hf.comp (V.continuous_cliffordSpinCandidateMatrixCoordinate A i j)

end RationalQuadraticSpaceMatrix
