import SMSFormula.RationalSpecialOrthogonalAffineScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# The rational special-orthogonal group scheme

The affine carrier defined by the equations

```text
Xᵀ F X = F,  det(X) = 1
```

is bundled here as a group object over `Spec ℚ`.  Over every commutative
rational algebra the represented group is the determinant-one subgroup of
the form-preserving general-linear group.  Entrywise scalar extension is
proved functorial, and the affine carrier represents the resulting
contravariant group-valued functor on all rational schemes via global
sections.

Consequently the group law supplied by `GrpObj.ofRepresentableBy` is proved
to induce ordinary matrix multiplication, identity, and inversion on every
relative point.  Over a field, the affine points are multiplicatively
equivalent to the repository's scalar-extension special-orthogonal matrix
subgroup.

This constructs the `SO` group scheme carrier and its group law.  It does not
construct the Spin affine group scheme, the central isogeny, or any fppf
surjectivity statement.
-/

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory Matrix

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

abbrev specialOrthogonalMatrixGroup
    (K : Type*) [CommRing K] [Algebra ℚ K] :=
  PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
    (V.specialOrthogonalMappedFormMatrix K)

def specialOrthogonalMatrixPointToGroup
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (M : V.specialOrthogonalMatrixPoint K) :
    V.specialOrthogonalMatrixGroup K := by
  have hdet : IsUnit M.1.det := by rw [M.2.2]; exact isUnit_one
  have hM : IsUnit M.1 := (Matrix.isUnit_iff_isUnit_det M.1).2 hdet
  let g : GL (Fin n) K := hM.unit
  have hg : (g : Matrix (Fin n) (Fin n) K) = M.1 := hM.unit_spec
  let gO : PositiveDefiniteIntegralLattice.formPreservingMatrixSubgroup
      (V.specialOrthogonalMappedFormMatrix K) :=
    ⟨g, (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) g).2 (by simpa [hg] using M.2.1)⟩
  exact ⟨gO, (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
    (V.specialOrthogonalMappedFormMatrix K) gO).2 (by simpa [gO, hg] using M.2.2)⟩

def specialOrthogonalMatrixPointOfGroup
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (g : V.specialOrthogonalMatrixGroup K) :
    V.specialOrthogonalMatrixPoint K :=
  ⟨g.1.1.1, by
    constructor
    · exact (PositiveDefiniteIntegralLattice.mem_formPreservingMatrixSubgroup_iff
        (V.specialOrthogonalMappedFormMatrix K) g.1.1).1 g.1.2
    · exact (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
        (V.specialOrthogonalMappedFormMatrix K) g.1).1 g.2⟩

def specialOrthogonalMatrixPointEquivGroup
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    V.specialOrthogonalMatrixPoint K ≃ V.specialOrthogonalMatrixGroup K where
  toFun := V.specialOrthogonalMatrixPointToGroup K
  invFun := V.specialOrthogonalMatrixPointOfGroup K
  left_inv M := by
    apply Subtype.ext
    ext i j
    simp [specialOrthogonalMatrixPointToGroup,
      specialOrthogonalMatrixPointOfGroup]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [specialOrthogonalMatrixPointToGroup,
      specialOrthogonalMatrixPointOfGroup]

def specialOrthogonalMatrixGroupMap
    {K L : Type*} [CommRing K] [CommRing L]
    [Algebra ℚ K] [Algebra ℚ L]
    (f : K →ₐ[ℚ] L) :
    V.specialOrthogonalMatrixGroup K →*
      V.specialOrthogonalMatrixGroup L where
  toFun g := by
    let mapped : GL (Fin n) L :=
      Matrix.GeneralLinearGroup.map f.toRingHom g.1.1
    have hform :
        mapped.1.transpose * V.specialOrthogonalMappedFormMatrix L * mapped.1 =
          V.specialOrthogonalMappedFormMatrix L := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K ↦
        M.map f.toRingHom) g.1.2
      have hF : (V.specialOrthogonalMappedFormMatrix K).map f.toRingHom =
          V.specialOrthogonalMappedFormMatrix L := by
        ext i j
        exact f.commutes (V.pairingMatrix i j)
      change (g.1.1.1.transpose * V.specialOrthogonalMappedFormMatrix K *
          g.1.1.1).map f.toRingHom =
        (V.specialOrthogonalMappedFormMatrix K).map f.toRingHom at h
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hF] at h
      simpa [mapped] using h
    let mappedO : PositiveDefiniteIntegralLattice.formPreservingMatrixSubgroup
        (V.specialOrthogonalMappedFormMatrix L) := ⟨mapped, hform⟩
    refine ⟨mappedO, (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix L) mappedO).2 ?_⟩
    have hdet := (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) g.1).1 g.2
    change (g.1.1.1.map f.toRingHom).det = 1
    calc
      (g.1.1.1.map f.toRingHom).det = f g.1.1.1.det :=
        (RingHom.map_det f.toRingHom g.1.1.1).symm
      _ = 1 := by rw [hdet, map_one]
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_one f.toRingHom
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_mul f.toRingHom g.1.1 h.1.1

@[simp]
theorem specialOrthogonalMatrixGroupMap_apply_matrix
    {K L : Type*} [CommRing K] [CommRing L]
    [Algebra ℚ K] [Algebra ℚ L]
    (f : K →ₐ[ℚ] L) (g : V.specialOrthogonalMatrixGroup K) :
    ((V.specialOrthogonalMatrixGroupMap f g).1.1.1) =
      g.1.1.1.map f.toRingHom := by
  ext i j
  simp [specialOrthogonalMatrixGroupMap]

@[simp]
theorem specialOrthogonalMatrixGroupMap_id
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (g : V.specialOrthogonalMatrixGroup K) :
    V.specialOrthogonalMatrixGroupMap (AlgHom.id ℚ K) g = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp

@[simp]
theorem specialOrthogonalMatrixGroupMap_comp
    {K L M : Type*} [CommRing K] [CommRing L] [CommRing M]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra ℚ M]
    (f : K →ₐ[ℚ] L) (g : L →ₐ[ℚ] M)
    (x : V.specialOrthogonalMatrixGroup K) :
    V.specialOrthogonalMatrixGroupMap g
        (V.specialOrthogonalMatrixGroupMap f x) =
      V.specialOrthogonalMatrixGroupMap (g.comp f) x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp

def specialOrthogonalMatrixGroupEquivScalarExtension
    (K : Type) [Field K] [Algebra ℚ K] [Invertible (2 : K)] :
    V.specialOrthogonalMatrixGroup K ≃*
      V.scalarExtensionSpecialOrthogonalMatrixSubgroup K := by
  change PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ K)) ≃*
    PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ K))
  exact MulEquiv.refl _

end RationalQuadraticSpaceMatrix
