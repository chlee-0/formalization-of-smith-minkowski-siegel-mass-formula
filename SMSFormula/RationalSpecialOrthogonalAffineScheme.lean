import SMSFormula.RationalCliffordSpinScalarExtensionKernel
import SMSFormula.RationalMuTwoCoordinateHopf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The rational special-orthogonal affine scheme carrier

For a nonsingular rational form matrix `V.pairingMatrix`, this file constructs
the coordinate algebra

```text
ℚ[x_ij] / (Xᵀ F X - F, det(X) - 1)
```

and its affine `Spec` over `Spec ℚ`.  Algebra maps out of this quotient are
proved equivalent to matrices satisfying the special-orthogonal equations
over every commutative rational algebra.  Affine `K`-points are consequently
equivalent to those matrices, and over a field they are equivalent to the
repository's scalar-extension special-orthogonal matrix subgroup.

This is the affine carrier and functor-of-affine-points layer.  It does not
yet bundle the carrier as a group object, construct an affine Spin carrier,
or assert a central isogeny or any form of surjectivity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

abbrev specialOrthogonalPolynomialRing :=
  MvPolynomial (Fin n × Fin n) ℚ

def specialOrthogonalUniversalMatrix :
    Matrix (Fin n) (Fin n) (specialOrthogonalPolynomialRing (n := n)) :=
  fun i j => MvPolynomial.X (i, j)

def specialOrthogonalFormMatrixPolynomial :
    Matrix (Fin n) (Fin n) (specialOrthogonalPolynomialRing (n := n)) :=
  V.pairingMatrix.map MvPolynomial.C

def specialOrthogonalRelation (i j : Fin n) :
    specialOrthogonalPolynomialRing (n := n) :=
  ((specialOrthogonalUniversalMatrix (n := n)).transpose *
      V.specialOrthogonalFormMatrixPolynomial *
        specialOrthogonalUniversalMatrix (n := n)) i j -
    MvPolynomial.C (V.pairingMatrix i j)

def specialOrthogonalDetRelation (_V : RationalQuadraticSpaceMatrix n) :
    specialOrthogonalPolynomialRing (n := n) :=
  (specialOrthogonalUniversalMatrix (n := n)).det - 1

def specialOrthogonalRelationSet :
    Set (specialOrthogonalPolynomialRing (n := n)) :=
  Set.range (fun ij : Fin n × Fin n =>
    V.specialOrthogonalRelation ij.1 ij.2) ∪
      {V.specialOrthogonalDetRelation}

def specialOrthogonalRelationIdeal :
    Ideal (specialOrthogonalPolynomialRing (n := n)) :=
  Ideal.span V.specialOrthogonalRelationSet

abbrev specialOrthogonalCoordinateRing :=
  specialOrthogonalPolynomialRing (n := n) ⧸ V.specialOrthogonalRelationIdeal

def specialOrthogonalMappedFormMatrix
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    Matrix (Fin n) (Fin n) K :=
  V.pairingMatrix.map (algebraMap ℚ K)

def specialOrthogonalMatrixPoint
    (K : Type*) [CommRing K] [Algebra ℚ K] :=
  { M : Matrix (Fin n) (Fin n) K //
      M.transpose * V.specialOrthogonalMappedFormMatrix K * M =
          V.specialOrthogonalMappedFormMatrix K ∧
        M.det = 1 }

def specialOrthogonalMatrixEvaluation
    (_V : RationalQuadraticSpaceMatrix n)
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : Matrix (Fin n) (Fin n) K) :
    specialOrthogonalPolynomialRing (n := n) →ₐ[ℚ] K :=
  MvPolynomial.aeval fun ij => M ij.1 ij.2

@[simp]
theorem specialOrthogonalMatrixEvaluation_X
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    V.specialOrthogonalMatrixEvaluation M (MvPolynomial.X (i, j)) = M i j := by
  simp [specialOrthogonalMatrixEvaluation]

theorem specialOrthogonalMatrixEvaluation_relation
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    V.specialOrthogonalMatrixEvaluation M (V.specialOrthogonalRelation i j) =
      (M.transpose * V.specialOrthogonalMappedFormMatrix K * M) i j -
        V.specialOrthogonalMappedFormMatrix K i j := by
  simp [specialOrthogonalMatrixEvaluation, specialOrthogonalRelation,
    specialOrthogonalUniversalMatrix, specialOrthogonalFormMatrixPolynomial,
    specialOrthogonalMappedFormMatrix, Matrix.mul_apply]

theorem specialOrthogonalMatrixEvaluation_detRelation
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : Matrix (Fin n) (Fin n) K) :
    V.specialOrthogonalMatrixEvaluation M V.specialOrthogonalDetRelation =
      M.det - 1 := by
  simp only [specialOrthogonalMatrixEvaluation, specialOrthogonalDetRelation,
    map_sub, map_one]
  congr 1
  change (V.specialOrthogonalMatrixEvaluation M).toRingHom
      (specialOrthogonalUniversalMatrix (n := n)).det = M.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [specialOrthogonalUniversalMatrix]

def specialOrthogonalCoordinate (i j : Fin n) :
    V.specialOrthogonalCoordinateRing :=
  Ideal.Quotient.mk V.specialOrthogonalRelationIdeal
    (MvPolynomial.X (i, j))

def specialOrthogonalMatrixOfCoordinateAlgHom
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => F (V.specialOrthogonalCoordinate i j)

theorem specialOrthogonalCoordinateAlgHom_comp_mk
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) :
    F.comp (Ideal.Quotient.mkₐ ℚ V.specialOrthogonalRelationIdeal) =
      V.specialOrthogonalMatrixEvaluation
        (V.specialOrthogonalMatrixOfCoordinateAlgHom F) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp [specialOrthogonalMatrixEvaluation,
    specialOrthogonalMatrixOfCoordinateAlgHom, specialOrthogonalCoordinate]

def specialOrthogonalMatrixPointOfCoordinateAlgHom
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) :
    V.specialOrthogonalMatrixPoint K := by
  let M := V.specialOrthogonalMatrixOfCoordinateAlgHom F
  refine ⟨M, ?_, ?_⟩
  · ext i j
    have hmem : V.specialOrthogonalRelation i j ∈
        V.specialOrthogonalRelationIdeal := by
      apply Ideal.subset_span
      exact Or.inl ⟨(i, j), rfl⟩
    have hzero :
        (F.comp (Ideal.Quotient.mkₐ ℚ V.specialOrthogonalRelationIdeal))
          (V.specialOrthogonalRelation i j) = 0 := by
      change F (Ideal.Quotient.mk V.specialOrthogonalRelationIdeal
        (V.specialOrthogonalRelation i j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
    rw [V.specialOrthogonalCoordinateAlgHom_comp_mk F,
      V.specialOrthogonalMatrixEvaluation_relation M i j] at hzero
    exact sub_eq_zero.mp hzero
  · have hmem : V.specialOrthogonalDetRelation ∈
        V.specialOrthogonalRelationIdeal := by
      apply Ideal.subset_span
      exact Or.inr (Set.mem_singleton _)
    have hzero :
        (F.comp (Ideal.Quotient.mkₐ ℚ V.specialOrthogonalRelationIdeal))
          V.specialOrthogonalDetRelation = 0 := by
      change F (Ideal.Quotient.mk V.specialOrthogonalRelationIdeal
        V.specialOrthogonalDetRelation) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
    rw [V.specialOrthogonalCoordinateAlgHom_comp_mk F,
      V.specialOrthogonalMatrixEvaluation_detRelation M] at hzero
    exact sub_eq_zero.mp hzero

def specialOrthogonalCoordinateAlgHomOfMatrixPoint
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : V.specialOrthogonalMatrixPoint K) :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ] K :=
  Ideal.Quotient.liftₐ V.specialOrthogonalRelationIdeal
    (V.specialOrthogonalMatrixEvaluation M.1) (by
      intro p hp
      have hle : V.specialOrthogonalRelationIdeal ≤
          RingHom.ker (V.specialOrthogonalMatrixEvaluation M.1).toRingHom := by
        apply Ideal.span_le.2
        intro q hq
        rcases hq with hq | hq
        · rcases hq with ⟨ij, rfl⟩
          change V.specialOrthogonalMatrixEvaluation M.1
            (V.specialOrthogonalRelation ij.1 ij.2) = 0
          rw [V.specialOrthogonalMatrixEvaluation_relation]
          exact sub_eq_zero.mpr
            (congrFun (congrFun M.2.1 ij.1) ij.2)
        · rw [Set.mem_singleton_iff.mp hq]
          change V.specialOrthogonalMatrixEvaluation M.1
            V.specialOrthogonalDetRelation = 0
          rw [V.specialOrthogonalMatrixEvaluation_detRelation]
          exact sub_eq_zero.mpr M.2.2
      exact hle hp)

@[simp]
theorem specialOrthogonalCoordinateAlgHomOfMatrixPoint_coordinate
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (M : V.specialOrthogonalMatrixPoint K) (i j : Fin n) :
    V.specialOrthogonalCoordinateAlgHomOfMatrixPoint M
        (V.specialOrthogonalCoordinate i j) = M.1 i j := by
  simp [specialOrthogonalCoordinateAlgHomOfMatrixPoint,
    specialOrthogonalCoordinate]

def specialOrthogonalCoordinateAlgHomEquivMatrixPoint
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    (V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) ≃
      V.specialOrthogonalMatrixPoint K where
  toFun := V.specialOrthogonalMatrixPointOfCoordinateAlgHom
  invFun := V.specialOrthogonalCoordinateAlgHomOfMatrixPoint
  left_inv F := by
    apply Ideal.Quotient.algHom_ext ℚ
    apply MvPolynomial.algHom_ext
    intro ij
    change V.specialOrthogonalCoordinateAlgHomOfMatrixPoint
        (V.specialOrthogonalMatrixPointOfCoordinateAlgHom F)
          (V.specialOrthogonalCoordinate ij.1 ij.2) =
      F (V.specialOrthogonalCoordinate ij.1 ij.2)
    rw [V.specialOrthogonalCoordinateAlgHomOfMatrixPoint_coordinate]
    rfl
  right_inv M := by
    apply Subtype.ext
    ext i j
    exact V.specialOrthogonalCoordinateAlgHomOfMatrixPoint_coordinate M i j

abbrev specialOrthogonalAffineScheme : Scheme :=
  Spec (CommRingCat.of V.specialOrthogonalCoordinateRing)

def specialOrthogonalStructureMap :
    V.specialOrthogonalAffineScheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ℚ V.specialOrthogonalCoordinateRing))

abbrev SpecialOrthogonalSchemePoint
    (K : Type) [CommRing K] [Algebra ℚ K] :=
  { f : Spec (CommRingCat.of K) ⟶ V.specialOrthogonalAffineScheme //
    f ≫ V.specialOrthogonalStructureMap =
      RationalTamagawa.rationalAffineStructureMap K }

def specialOrthogonalSchemePointOfCoordinateAlgHom
    {K : Type} [CommRing K] [Algebra ℚ K]
    (F : V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) :
    V.SpecialOrthogonalSchemePoint K :=
  ⟨Spec.map (CommRingCat.ofHom F.toRingHom), by
    change Spec.map (CommRingCat.ofHom F.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℚ V.specialOrthogonalCoordinateRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext q
    exact F.commutes q⟩

def specialOrthogonalCoordinateAlgHomOfSchemePoint
    {K : Type} [CommRing K] [Algebra ℚ K]
    (f : V.SpecialOrthogonalSchemePoint K) :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ] K where
  toRingHom := (Spec.preimage f.1).hom
  commutes' q := by
    have h := congrArg Spec.preimage f.2
    rw [Spec.preimage_comp] at h
    simp only [specialOrthogonalStructureMap,
      RationalTamagawa.rationalAffineStructureMap,
      Spec.preimage_map] at h
    exact congrArg
      (fun g : CommRingCat.of ℚ ⟶ CommRingCat.of K => g.hom q) h

def specialOrthogonalSchemePointEquivCoordinateAlgHom
    (K : Type) [CommRing K] [Algebra ℚ K] :
    V.SpecialOrthogonalSchemePoint K ≃
      (V.specialOrthogonalCoordinateRing →ₐ[ℚ] K) where
  toFun := V.specialOrthogonalCoordinateAlgHomOfSchemePoint
  invFun := V.specialOrthogonalSchemePointOfCoordinateAlgHom
  left_inv f := by
    apply Subtype.ext
    exact Spec.map_preimage f.1
  right_inv F := by
    apply AlgHom.ext
    intro x
    exact congrArg
      (fun g : CommRingCat.of V.specialOrthogonalCoordinateRing ⟶
          CommRingCat.of K => g.hom x)
      (Spec.preimage_map (CommRingCat.ofHom F.toRingHom))

def specialOrthogonalSchemePointEquivMatrixPoint
    (K : Type) [CommRing K] [Algebra ℚ K] :
    V.SpecialOrthogonalSchemePoint K ≃
      V.specialOrthogonalMatrixPoint K :=
  (V.specialOrthogonalSchemePointEquivCoordinateAlgHom K).trans
    (V.specialOrthogonalCoordinateAlgHomEquivMatrixPoint K)

def specialOrthogonalMatrixPointToScalarExtension
    (K : Type) [Field K] [Algebra ℚ K] [Invertible (2 : K)]
    (M : V.specialOrthogonalMatrixPoint K) :
    V.scalarExtensionSpecialOrthogonalMatrixSubgroup K := by
  have hdet : M.1.det ≠ 0 := by
    rw [M.2.2]
    exact one_ne_zero
  let g : GL (Fin n) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 hdet
  let gO : V.scalarExtensionOrthogonalMatrixSubgroup K :=
    ⟨g, (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
      (V.scalarExtensionFormMatrix K) g).2 (by
        simpa [g, specialOrthogonalMappedFormMatrix,
          scalarExtensionFormMatrix] using M.2.1)⟩
  exact ⟨gO, (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
    (V.scalarExtensionFormMatrix K) gO).2 (by
      simpa [gO, g] using M.2.2)⟩

def specialOrthogonalMatrixPointOfScalarExtension
    (K : Type) [Field K] [Algebra ℚ K] [Invertible (2 : K)]
    (g : V.scalarExtensionSpecialOrthogonalMatrixSubgroup K) :
    V.specialOrthogonalMatrixPoint K :=
  ⟨g.1.1.1, by
    constructor
    · simpa [specialOrthogonalMappedFormMatrix,
        scalarExtensionFormMatrix] using
        (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
          (V.scalarExtensionFormMatrix K) g.1.1).1 g.1.2
    · exact (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
        (V.scalarExtensionFormMatrix K) g.1).1 g.2⟩

def specialOrthogonalMatrixPointEquivScalarExtension
    (K : Type) [Field K] [Algebra ℚ K] [Invertible (2 : K)] :
    V.specialOrthogonalMatrixPoint K ≃
      V.scalarExtensionSpecialOrthogonalMatrixSubgroup K where
  toFun := V.specialOrthogonalMatrixPointToScalarExtension K
  invFun := V.specialOrthogonalMatrixPointOfScalarExtension K
  left_inv M := by
    apply Subtype.ext
    ext i j
    simp [specialOrthogonalMatrixPointToScalarExtension,
      specialOrthogonalMatrixPointOfScalarExtension]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [specialOrthogonalMatrixPointToScalarExtension,
      specialOrthogonalMatrixPointOfScalarExtension]

def specialOrthogonalSchemePointEquivScalarExtension
    (K : Type) [Field K] [Algebra ℚ K] [Invertible (2 : K)] :
    V.SpecialOrthogonalSchemePoint K ≃
      V.scalarExtensionSpecialOrthogonalMatrixSubgroup K :=
  (V.specialOrthogonalSchemePointEquivMatrixPoint K).trans
    (V.specialOrthogonalMatrixPointEquivScalarExtension K)

end RationalQuadraticSpaceMatrix
