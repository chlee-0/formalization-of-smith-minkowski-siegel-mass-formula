import SMSFormula.LocalOrientedComparison
import SMSFormula.ProperMass
import SMSFormula.SpecialOrthogonalLinearization
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Concrete finite-adelic special orthogonal presentation

This module cuts the determinant-one groups used by Schulze--Pillot's first
version out of the existing concrete ordinary orthogonal presentation. The
generic double-coset and quotient-measure infrastructure applies to these
groups without modification; the proper-genus parametrization is developed
separately. It also identifies the matrix-valued local special-orthogonal
carrier with the existing units-valued subgroup and transports the identity
chart into skew-adjoint coordinates.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

universe u

variable {n : ℕ}

open MeasureTheory
open TopologicalSpace
open scoped ENNReal Matrix RestrictedProduct Uniformity

/-- The determinant-one subgroup of a form-preserving matrix group. -/
def specialFormPreservingMatrixSubgroup {R : Type*} [CommRing R]
    (F : Matrix (Fin n) (Fin n) R) :
    Subgroup (formPreservingMatrixSubgroup F) :=
  ((Matrix.GeneralLinearGroup.det (n := Fin n)).comp
    (formPreservingMatrixSubgroup F).subtype).ker

@[simp]
theorem mem_specialFormPreservingMatrixSubgroup_iff
    {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R)
    (g : formPreservingMatrixSubgroup F) :
    g ∈ specialFormPreservingMatrixSubgroup F ↔ g.1.1.det = 1 := by
  change Matrix.GeneralLinearGroup.det g.1 = 1 ↔ g.1.1.det = 1
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- A determinant-one form-preserving matrix as an element of the existing
units-valued special subgroup. -/
def specialOrthogonalMatrixSetToSpecialSubgroup
    {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R)
    (g : Matrix.specialOrthogonalMatrixSet F) :
    specialFormPreservingMatrixSubgroup F := by
  let A : Matrix.GeneralLinearGroup (Fin n) R :=
    Matrix.SpecialLinearGroup.toGL ⟨g, g.property.2⟩
  let hA : A ∈ formPreservingMatrixSubgroup F := by
    rw [mem_formPreservingMatrixSubgroup_iff]
    exact (Matrix.formPreservingConstraint_eq_zero_iff F g).mp g.property.1
  let og : formPreservingMatrixSubgroup F := ⟨A, hA⟩
  exact ⟨og, (mem_specialFormPreservingMatrixSubgroup_iff F og).mpr g.property.2⟩

/-- The matrix-valued special-orthogonal carrier and the existing
units-valued special subgroup have the same elements. -/
def specialOrthogonalMatrixSetEquivSpecialSubgroup
    {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R) :
    Matrix.specialOrthogonalMatrixSet F ≃
      specialFormPreservingMatrixSubgroup F where
  toFun := specialOrthogonalMatrixSetToSpecialSubgroup F
  invFun g := ⟨g.1.1.1,
    (Matrix.formPreservingConstraint_eq_zero_iff F g.1.1.1).mpr g.1.2,
    (mem_specialFormPreservingMatrixSubgroup_iff F g.1).mp g.2⟩
  left_inv _ := rfl
  right_inv _ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl

@[simp]
theorem coe_specialOrthogonalMatrixSetEquivSpecialSubgroup_apply
    {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R)
    (g : Matrix.specialOrthogonalMatrixSet F) :
    (specialOrthogonalMatrixSetEquivSpecialSubgroup F g).1.1.1 = g :=
  rfl

@[simp]
theorem coe_specialOrthogonalMatrixSetEquivSpecialSubgroup_symm_apply
    {R : Type*} [CommRing R] (F : Matrix (Fin n) (Fin n) R)
    (g : specialFormPreservingMatrixSubgroup F) :
    ((specialOrthogonalMatrixSetEquivSpecialSubgroup F).symm g :
      Matrix (Fin n) (Fin n) R) = g.1.1.1 :=
  rfl

section IdentityChartBridge

open scoped Matrix.Norms.Operator Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- The carrier-to-subgroup map is continuous for every topological
commutative ring. -/
theorem continuous_specialOrthogonalMatrixSetToSpecialSubgroup
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (F : Matrix (Fin n) (Fin n) R) :
    Continuous (specialOrthogonalMatrixSetToSpecialSubgroup F) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact Matrix.SpecialLinearGroup.continuous_toGL.comp
    (Continuous.subtype_mk continuous_subtype_val (fun g => g.property.2))

/-- The matrix-valued carrier and units-valued special subgroup are
homeomorphic over every topological commutative ring. -/
def specialOrthogonalMatrixSetHomeomorphSpecialSubgroup
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (F : Matrix (Fin n) (Fin n) R) :
    Matrix.specialOrthogonalMatrixSet F ≃ₜ
      specialFormPreservingMatrixSubgroup F where
  toEquiv := specialOrthogonalMatrixSetEquivSpecialSubgroup F
  continuous_toFun :=
    continuous_specialOrthogonalMatrixSetToSpecialSubgroup F
  continuous_invFun := by fun_prop

/-- The local identity neighborhood transported to the existing units-valued
special subgroup. -/
def specialFormPreservingIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) : Set (specialFormPreservingMatrixSubgroup F) :=
  specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F ''
    Matrix.specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar

/-- The units-valued local special-orthogonal neighborhood is open. -/
theorem isOpen_specialFormPreservingIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialFormPreservingIdentityChartNeighborhood F hF hdet hchar) := by
  exact (specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).isOpen_image.mpr
    (Matrix.isOpen_specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar)

omit [CompleteSpace K] in
@[simp]
theorem specialOrthogonalMatrixSetToSpecialSubgroup_identity
    (F : Matrix (Fin n) (Fin n) K) :
    specialOrthogonalMatrixSetToSpecialSubgroup F
      (Matrix.specialOrthogonalMatrixIdentity F) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

/-- The subgroup identity belongs to its transported chart neighborhood. -/
theorem one_mem_specialFormPreservingIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : specialFormPreservingMatrixSubgroup F) ∈
      specialFormPreservingIdentityChartNeighborhood F hF hdet hchar := by
  refine ⟨Matrix.specialOrthogonalMatrixIdentity F,
    Matrix.specialOrthogonalMatrixIdentity_mem_identityCarrierNeighborhood
      F hF hdet hchar, ?_⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup_identity F

/-- The units-valued local special-orthogonal neighborhood in skew-adjoint
matrix coordinates. -/
noncomputable def specialFormPreservingIdentitySkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialFormPreservingIdentityChartNeighborhood F hF hdet hchar ≃ₜ
      Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar :=
  ((specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).image
    (Matrix.specialOrthogonalIdentityCarrierNeighborhood F hF hdet hchar)).symm.trans
      (Matrix.specialOrthogonalIdentityCarrierSkewAdjointHomeomorph F hF hdet hchar)

@[simp]
theorem specialFormPreservingIdentitySkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingIdentityChartNeighborhood F hF hdet hchar) :
    ((specialFormPreservingIdentitySkewAdjointHomeomorph F hF hdet hchar g :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
        Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingDetOneIdentityChart F hF hdet hchar
        (g.1.1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

/-- The identity chart neighborhood translated by left multiplication to a
specified special-orthogonal group point. -/
def specialFormPreservingTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    Set (specialFormPreservingMatrixSubgroup F) :=
  Homeomorph.mulLeft g ''
    specialFormPreservingIdentityChartNeighborhood F hF hdet hchar

/-- Every translated special-orthogonal chart neighborhood is open. -/
theorem isOpen_specialFormPreservingTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    IsOpen (specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g) := by
  exact (Homeomorph.mulLeft g).isOpen_image.mpr
    (isOpen_specialFormPreservingIdentityChartNeighborhood F hF hdet hchar)

/-- The center belongs to its translated special-orthogonal chart
neighborhood. -/
theorem self_mem_specialFormPreservingTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g := by
  refine ⟨1,
    one_mem_specialFormPreservingIdentityChartNeighborhood F hF hdet hchar, ?_⟩
  exact mul_one g

/-- The translated local special-orthogonal neighborhood in the same
skew-adjoint coordinates as the identity chart. -/
noncomputable def specialFormPreservingTranslatedSkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g ≃ₜ
      Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar :=
  ((Homeomorph.mulLeft g).image
    (specialFormPreservingIdentityChartNeighborhood F hF hdet hchar)).symm.trans
      (specialFormPreservingIdentitySkewAdjointHomeomorph F hF hdet hchar)

@[simp]
theorem specialFormPreservingTranslatedSkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g) :
    ((specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g x :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
        Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingDetOneIdentityChart F hF hdet hchar
        ((g⁻¹ * x.1).1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

/-- The translated skew-adjoint chart sends its center to zero. -/
@[simp]
theorem specialFormPreservingTranslatedSkewAdjointHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g
      ⟨g, self_mem_specialFormPreservingTranslatedChartNeighborhood
        F hF hdet hchar g⟩ :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) = 0 := by
  apply Subtype.ext
  change ((specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g
    ⟨g, self_mem_specialFormPreservingTranslatedChartNeighborhood
      F hF hdet hchar g⟩ :
      (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
        Matrix (Fin n) (Fin n) K) = 0
  rw [specialFormPreservingTranslatedSkewAdjointHomeomorph_apply]
  simp

/-- The translated special-orthogonal chart bundled between the full subgroup
and full skew-adjoint coordinate spaces. -/
noncomputable def specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (specialFormPreservingMatrixSubgroup F)
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g,
      isOpen_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar,
      Matrix.isOpen_specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar⟩
  ((U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    (specialFormPreservingTranslatedSkewAdjointHomeomorph
      F hF hdet hchar g).toOpenPartialHomeomorph).trans
      (V.openPartialHomeomorphSubtypeCoe hV)

@[simp]
theorem specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).source =
      specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g := by
  simp [specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph]

@[simp]
theorem specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).target =
      Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar := by
  simp [specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph]

/-- On its source, the ambient chart is the existing translated subtype
homeomorphism. -/
theorem specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g) :
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g x.1 =
      (specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g x :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g,
      isOpen_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar,
      Matrix.isOpen_specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar⟩
  change (V.openPartialHomeomorphSubtypeCoe hV) ((
    specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g)
      ((U.openPartialHomeomorphSubtypeCoe hU).symm x.1)) = _
  have hx : x.1 ∈ (U.openPartialHomeomorphSubtypeCoe hU).target := by
    rw [U.openPartialHomeomorphSubtypeCoe_target]
    exact x.2
  have hinv : (U.openPartialHomeomorphSubtypeCoe hU).symm x.1 = x := by
    apply Subtype.ext
    exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv hx
  rw [hinv]
  rfl

/-- Every subgroup point lies in the source of its translated ambient chart. -/
theorem self_mem_specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).source := by
  rw [specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source]
  exact self_mem_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g

/-- The translated ambient chart sends its center to zero. -/
@[simp]
theorem specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g g = 0 := by
  rw [show g = (⟨g,
    self_mem_specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g⟩ :
      specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g).1 by rfl,
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply]
  exact specialFormPreservingTranslatedSkewAdjointHomeomorph_center F hF hdet hchar g

/-- The sources of the translated ambient charts cover the special-orthogonal
subgroup. -/
theorem iUnion_specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (⋃ g : specialFormPreservingMatrixSubgroup F,
      (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  rw [Set.mem_iUnion]
  exact ⟨g,
    self_mem_specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar g⟩

/-- The special-orthogonal subgroup as a charted space in skew-adjoint
coordinates. This is an explicit parameterized structure, not a global
instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingChartedSpace
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) where
  atlas := Set.range fun g =>
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g
  chartAt g := specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar g
  mem_chart_source g :=
    self_mem_specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar g
  chart_mem_atlas g := ⟨g, rfl⟩

@[simp]
theorem specialFormPreservingChartedSpace_chartAt
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    @chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingChartedSpace F hF hdet hchar) g =
        specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar g :=
  rfl

@[simp]
theorem specialFormPreservingChartedSpace_atlas
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingChartedSpace F hF hdet hchar) =
        Set.range fun g =>
          specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar g :=
  rfl

/-- The preferred chart in the explicit charted-space structure contains its
center in its source. -/
theorem specialFormPreservingChartedSpace_mem_chart_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (@chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingChartedSpace F hF hdet hchar) g).source :=
  self_mem_specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source
    F hF hdet hchar g

/-- A translated chart is the identity chart after translating its argument
back to the identity. -/
theorem specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g x : specialFormPreservingMatrixSubgroup F)
    (hx : x ∈ (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).source) :
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g x =
      specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1 (g⁻¹ * x) := by
  rw [specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_source] at hx
  rcases hx with ⟨z, hz, hzx⟩
  have hzx' : g * z = x := hzx
  have hshift : g⁻¹ * x = z := by
    rw [← hzx']
    simp
  have hshift_mem : g⁻¹ * x ∈
      specialFormPreservingIdentityChartNeighborhood F hF hdet hchar := by
    rwa [hshift]
  have hshift_mem_one : g⁻¹ * x ∈
      specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar 1 := by
    exact ⟨g⁻¹ * x, hshift_mem, one_mul _⟩
  let xs : specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar g :=
    ⟨x, ⟨z, hz, hzx⟩⟩
  let ys : specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar 1 :=
    ⟨g⁻¹ * x, hshift_mem_one⟩
  rw [show specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g x =
      specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar g xs by
    exact specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply
      F hF hdet hchar g xs]
  rw [show specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar 1 (g⁻¹ * x) =
      specialFormPreservingTranslatedSkewAdjointHomeomorph F hF hdet hchar 1 ys by
    exact specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply
      F hF hdet hchar 1 ys]
  apply Subtype.ext
  rw [specialFormPreservingTranslatedSkewAdjointHomeomorph_apply,
    specialFormPreservingTranslatedSkewAdjointHomeomorph_apply]
  simp [xs, ys]

/-- The coordinate transition from the chart centered at `g` to the chart
centered at `h`. -/
noncomputable def specialFormPreservingSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g h : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar g).symm.trans
      (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar h)

@[simp]
theorem specialFormPreservingSkewAdjointTransition_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g h : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingSkewAdjointTransition F hF hdet hchar g h).source =
      Matrix.specialOrthogonalIdentitySkewAdjointNeighborhood F hF hdet hchar ∩
        (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar g).symm ⁻¹'
            specialFormPreservingTranslatedChartNeighborhood F hF hdet hchar h := by
  simp [specialFormPreservingSkewAdjointTransition]

/-- On its overlap, a transition is the identity chart applied after left
translation of the point represented by the source coordinate. -/
theorem specialFormPreservingSkewAdjointTransition_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (g h : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈ (specialFormPreservingSkewAdjointTransition
      F hF hdet hchar g h).source) :
    specialFormPreservingSkewAdjointTransition F hF hdet hchar g h y =
      specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1
          (h⁻¹ * (specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar g).symm y) := by
  rw [specialFormPreservingSkewAdjointTransition,
    OpenPartialHomeomorph.trans_source] at hy
  rw [specialFormPreservingSkewAdjointTransition,
    OpenPartialHomeomorph.trans_apply]
  exact
    specialFormPreservingTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
      F hF hdet hchar h _ hy.2

end IdentityChartBridge

section RCLikeIdentityChartBridge

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Operator Topology ContDiff

variable {K : Type*} [RCLike K]

/-- The common smooth matrix-carrier identity neighborhood transported to the
existing units-valued special subgroup. -/
def specialFormPreservingSmoothIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Set (specialFormPreservingMatrixSubgroup F) :=
  specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F ''
    Matrix.specialOrthogonalSmoothIdentityCarrierNeighborhood
      F hF hdet hchar

/-- The common smooth units-valued identity neighborhood is open. -/
theorem isOpen_specialFormPreservingSmoothIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    IsOpen (specialFormPreservingSmoothIdentityChartNeighborhood
      F hF hdet hchar) := by
  exact (specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).isOpen_image.mpr
    (Matrix.isOpen_specialOrthogonalSmoothIdentityCarrierNeighborhood
      F hF hdet hchar)

/-- The subgroup identity belongs to the common smooth identity
neighborhood. -/
theorem one_mem_specialFormPreservingSmoothIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (1 : specialFormPreservingMatrixSubgroup F) ∈
      specialFormPreservingSmoothIdentityChartNeighborhood
        F hF hdet hchar := by
  refine ⟨Matrix.specialOrthogonalMatrixIdentity F,
    Matrix.specialOrthogonalMatrixIdentity_mem_smoothIdentityCarrierNeighborhood
      F hF hdet hchar, ?_⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup_identity F

/-- The common smooth units-valued identity neighborhood in the same
skew-adjoint coordinates as its matrix carrier. -/
noncomputable def specialFormPreservingSmoothIdentitySkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    specialFormPreservingSmoothIdentityChartNeighborhood F hF hdet hchar ≃ₜ
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar :=
  ((specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).image
    (Matrix.specialOrthogonalSmoothIdentityCarrierNeighborhood
      F hF hdet hchar)).symm.trans
        (Matrix.specialOrthogonalSmoothIdentityCarrierSkewAdjointHomeomorph
          F hF hdet hchar)

@[simp]
theorem specialFormPreservingSmoothIdentitySkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingSmoothIdentityChartNeighborhood
      F hF hdet hchar) :
    ((specialFormPreservingSmoothIdentitySkewAdjointHomeomorph
      F hF hdet hchar g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
          Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar (g.1.1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

@[simp]
theorem coe_specialFormPreservingSmoothIdentitySkewAdjointHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (y : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar) :
    ((specialFormPreservingSmoothIdentitySkewAdjointHomeomorph
      F hF hdet hchar).symm y).1.1.1.1 =
      (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar).symm
          (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y) :=
  rfl

/-- The common smooth identity neighborhood translated by left multiplication
to a specified special-orthogonal group point. -/
def specialFormPreservingSmoothTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    Set (specialFormPreservingMatrixSubgroup F) :=
  Homeomorph.mulLeft g ''
    specialFormPreservingSmoothIdentityChartNeighborhood F hF hdet hchar

/-- Every common smooth translated special-orthogonal neighborhood is open. -/
theorem isOpen_specialFormPreservingSmoothTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    IsOpen (specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g) := by
  exact (Homeomorph.mulLeft g).isOpen_image.mpr
    (isOpen_specialFormPreservingSmoothIdentityChartNeighborhood
      F hF hdet hchar)

/-- The center belongs to its common smooth translated special-orthogonal
neighborhood. -/
theorem self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g := by
  refine ⟨1,
    one_mem_specialFormPreservingSmoothIdentityChartNeighborhood
      F hF hdet hchar, ?_⟩
  exact mul_one g

/-- The common smooth translated neighborhood in the same skew-adjoint
coordinates as the identity chart. -/
noncomputable def specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g ≃ₜ
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar :=
  ((Homeomorph.mulLeft g).image
    (specialFormPreservingSmoothIdentityChartNeighborhood
      F hF hdet hchar)).symm.trans
        (specialFormPreservingSmoothIdentitySkewAdjointHomeomorph
          F hF hdet hchar)

@[simp]
theorem specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g) :
    ((specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
      F hF hdet hchar g x :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
          Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar
          ((g⁻¹ * x.1).1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

/-- The common smooth translated skew-adjoint chart sends its center to
zero. -/
@[simp]
theorem specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        F hF hdet hchar g
        ⟨g, self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
          F hF hdet hchar g⟩ =
      ⟨0, Matrix.zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar⟩ := by
  apply Subtype.ext
  change (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
    F hF hdet hchar g
      ⟨g, self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g⟩ :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) = 0
  apply Subtype.ext
  rw [specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply]
  simp

/-- The common smooth translated chart bundled between the full subgroup and
full skew-adjoint coordinate spaces. -/
noncomputable def
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (specialFormPreservingMatrixSubgroup F)
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g,
      isOpen_specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar,
      Matrix.isOpen_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar⟩
  ((U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
      F hF hdet hchar g).toOpenPartialHomeomorph).trans
      (V.openPartialHomeomorphSubtypeCoe hV)

@[simp]
theorem
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).source =
        specialFormPreservingSmoothTranslatedChartNeighborhood
          F hF hdet hchar g := by
  simp [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph]

@[simp]
theorem
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).target =
        Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
          F hF hdet hchar := by
  simp [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph]

/-- On its source, the common smooth ambient chart is the translated subtype
homeomorphism. -/
theorem
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g) :
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g x.1 =
      (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        F hF hdet hchar g x :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g,
      isOpen_specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar,
      Matrix.isOpen_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar⟩
  change (V.openPartialHomeomorphSubtypeCoe hV) ((
    specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
      F hF hdet hchar g)
        ((U.openPartialHomeomorphSubtypeCoe hU).symm x.1)) = _
  have hx : x.1 ∈ (U.openPartialHomeomorphSubtypeCoe hU).target := by
    rw [U.openPartialHomeomorphSubtypeCoe_target]
    exact x.2
  have hinv : (U.openPartialHomeomorphSubtypeCoe hU).symm x.1 = x := by
    apply Subtype.ext
    exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv hx
  rw [hinv]
  rfl

/-- On the common smooth target, the inverse ambient translated chart is left
multiplication by its center composed with the identity-chart inverse. -/
theorem
    coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F)
    (y : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar) :
    ((specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).symm y.1).1.1.1 =
      (g.1.1.1 : Matrix (Fin n) (Fin n) K) *
        (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
          F hF hdet hchar).symm
            (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
              F hF).symm y) := by
  let A :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g
  let H := specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
    F hF hdet hchar g
  let x := H.symm y
  have hxsource : x.1 ∈ A.source := by
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    exact x.2
  have happly : A x.1 = y.1 := by
    rw [show A x.1 = (H x :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) by
      exact
        specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
          F hF hdet hchar g x]
    exact congrArg Subtype.val (H.apply_symm_apply y)
  have hinv : A.symm y.1 = x.1 := by
    rw [← happly]
    exact A.left_inv hxsource
  rw [hinv]
  rfl

/-- Every subgroup point lies in the source of its centered common smooth
ambient chart. -/
theorem
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).source := by
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
  exact self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
    F hF hdet hchar g

/-- The common smooth ambient chart sends its center to zero. -/
@[simp]
theorem
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g g = 0 := by
  rw [show g = (⟨g,
    self_mem_specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g⟩ :
        specialFormPreservingSmoothTranslatedChartNeighborhood
          F hF hdet hchar g).1 by rfl,
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply]
  exact congrArg Subtype.val
    (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_center
      F hF hdet hchar g)

/-- The sources of the centered common smooth ambient charts cover the
special-orthogonal subgroup. -/
theorem
    iUnion_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    (⋃ g : specialFormPreservingMatrixSubgroup F,
      (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  rw [Set.mem_iUnion]
  exact ⟨g,
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar g⟩

/-- The common smooth special-orthogonal charts collected as an explicit
parameterized charted space, not a global instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingSmoothChartedSpace
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) where
  atlas := Set.range fun g =>
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g
  chartAt g :=
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g
  mem_chart_source g :=
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar g
  chart_mem_atlas g := ⟨g, rfl⟩

@[simp]
theorem specialFormPreservingSmoothChartedSpace_chartAt
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    @chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar) g =
        specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar g :=
  rfl

@[simp]
theorem specialFormPreservingSmoothChartedSpace_atlas
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar) =
        Set.range fun g =>
          specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar g :=
  rfl

/-- The preferred chart in the explicit common smooth charted space contains
its center in its source. -/
theorem specialFormPreservingSmoothChartedSpace_mem_chart_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (@chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar) g).source :=
  self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
    F hF hdet hchar g

/-- A common smooth translated chart is the identity chart after translating
its argument back to the identity. -/
theorem
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g x : specialFormPreservingMatrixSubgroup F)
    (hx : x ∈
      (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g).source) :
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g x =
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1 (g⁻¹ * x) := by
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    at hx
  rcases hx with ⟨z, hz, hzx⟩
  have hzx' : g * z = x := hzx
  have hshift : g⁻¹ * x = z := by
    rw [← hzx']
    simp
  have hshift_mem : g⁻¹ * x ∈
      specialFormPreservingSmoothIdentityChartNeighborhood
        F hF hdet hchar := by
    rwa [hshift]
  have hshift_mem_one : g⁻¹ * x ∈
      specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar 1 := by
    exact ⟨g⁻¹ * x, hshift_mem, one_mul _⟩
  let xs : specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar g :=
    ⟨x, ⟨z, hz, hzx⟩⟩
  let ys : specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar 1 :=
    ⟨g⁻¹ * x, hshift_mem_one⟩
  rw [show
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar g x =
      specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        F hF hdet hchar g xs by
    exact
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar g xs]
  rw [show
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1 (g⁻¹ * x) =
      specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        F hF hdet hchar 1 ys by
    exact
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar 1 ys]
  apply Subtype.ext
  rw [specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply,
    specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply]
  simp [xs, ys]

/-- The common smooth coordinate transition from the chart centered at `g`
to the chart centered at `h`. -/
noncomputable def specialFormPreservingSmoothSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g h : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar g).symm.trans
      (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar h)

@[simp]
theorem specialFormPreservingSmoothSkewAdjointTransition_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g h : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingSmoothSkewAdjointTransition
      F hF hdet hchar g h).source =
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
          F hF hdet hchar ∩
        (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar g).symm ⁻¹'
            specialFormPreservingSmoothTranslatedChartNeighborhood
              F hF hdet hchar h := by
  simp [specialFormPreservingSmoothSkewAdjointTransition]

/-- On its overlap, a common smooth transition is the common smooth identity
chart applied after left translation of the represented point. -/
theorem specialFormPreservingSmoothSkewAdjointTransition_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g h : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      F hF hdet hchar g h).source) :
    specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar g h y =
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1
          (h⁻¹ *
            (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
              F hF hdet hchar g).symm y) := by
  rw [specialFormPreservingSmoothSkewAdjointTransition,
    OpenPartialHomeomorph.trans_source] at hy
  rw [specialFormPreservingSmoothSkewAdjointTransition,
    OpenPartialHomeomorph.trans_apply]
  exact
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
      F hF hdet hchar h _ hy.2

/-- Every common smooth coordinate transition is smooth on its overlap
source. -/
theorem contDiffOn_infty_specialFormPreservingSmoothSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g h : specialFormPreservingMatrixSubgroup F) :
    ContDiffOn K (∞ : WithTop ℕ∞)
      (specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar g h)
      (specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar g h).source := by
  let e := Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  let c : Matrix (Fin n) (Fin n) K :=
    (h⁻¹).1.1.1 * g.1.1.1
  let invCoord : (skewAdjointMatricesLieSubalgebra F).toSubmodule →
      Matrix (Fin n) (Fin n) K := fun y ↦
    (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar).symm (0, e.symm y)
  let forwardCoord : Matrix (Fin n) (Fin n) K →
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := fun x ↦
    e (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
      F hF hdet hchar x).snd
  let s := (specialFormPreservingSmoothSkewAdjointTransition
    F hF hdet hchar g h).source
  have hsV : s ⊆
      Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
        F hF hdet hchar := by
    intro y hy
    change y ∈ (specialFormPreservingSmoothSkewAdjointTransition
      F hF hdet hchar g h).source at hy
    rw [specialFormPreservingSmoothSkewAdjointTransition_source] at hy
    exact hy.1
  have hinv : ContDiffOn K (∞ : WithTop ℕ∞) invCoord s := by
    exact
      (Matrix.contDiffOn_infty_specialOrthogonalSmoothIdentityZeroFiberCoordinate_symm
        F hF hdet hchar).mono hsV
  have hshift : ContDiffOn K (∞ : WithTop ℕ∞)
      (fun y ↦ c * invCoord y) s :=
    contDiff_const.contDiffOn.mul hinv
  have hchart : ContDiff K (∞ : WithTop ℕ∞)
      (Matrix.symmetricFormPreservingSmoothDetOneIdentityChart
        F hF hdet hchar) := by
    simpa [Matrix.symmetricFormPreservingSmoothDetOneIdentityChart,
      Matrix.symmetricFormPreservingSmoothIdentityChart] using
        (Matrix.contDiff_symmetricFormPreservingIdentityChart
          F hF hdet hchar).of_le
            (show (∞ : WithTop ℕ∞) ≤ ⊤ by simp)
  have hfwd : ContDiff K (∞ : WithTop ℕ∞) forwardCoord := by
    exact e.contDiff.comp (contDiff_snd.comp hchart)
  have hcomp : ContDiffOn K (∞ : WithTop ℕ∞)
      (fun y ↦ forwardCoord (c * invCoord y)) s := by
    simpa only [Function.comp_apply] using hfwd.comp_contDiffOn hshift
  apply hcomp.congr
  intro y hy
  change y ∈ (specialFormPreservingSmoothSkewAdjointTransition
    F hF hdet hchar g h).source at hy
  rw [specialFormPreservingSmoothSkewAdjointTransition_apply
    F hF hdet hchar g h y hy]
  rw [specialFormPreservingSmoothSkewAdjointTransition_source] at hy
  let ys : Matrix.specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      F hF hdet hchar := ⟨y, hy.1⟩
  have hsymm :=
    coe_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
      F hF hdet hchar g ys
  let x :=
    (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar g).symm y
  have hx_h : x ∈
      specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar h := hy.2
  rcases hx_h with ⟨z, hz, hzx⟩
  have hshift_eq : h⁻¹ * x = z := by
    rw [← hzx]
    simp
  have hq_identity : h⁻¹ * x ∈
      specialFormPreservingSmoothIdentityChartNeighborhood
        F hF hdet hchar := by
    rwa [hshift_eq]
  have hq : h⁻¹ * x ∈
      specialFormPreservingSmoothTranslatedChartNeighborhood
        F hF hdet hchar 1 :=
    ⟨h⁻¹ * x, hq_identity, one_mul _⟩
  let q : specialFormPreservingSmoothTranslatedChartNeighborhood
      F hF hdet hchar 1 := ⟨h⁻¹ * x, hq⟩
  rw [show
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar 1 (h⁻¹ * x) =
      (specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph
        F hF hdet hchar 1 q :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) by
    exact
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar 1 q]
  apply Subtype.ext
  rw [specialFormPreservingSmoothTranslatedSkewAdjointHomeomorph_apply]
  simp only [forwardCoord, e,
    Matrix.coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply]
  apply congrArg
  apply congrArg
  apply congrArg
  simp only [inv_one, one_mul]
  change ((h⁻¹ * x).1.1.1 : Matrix (Fin n) (Fin n) K) = c * invCoord y
  change (h⁻¹).1.1.1 * x.1.1.1 = c * invCoord y
  rw [hsymm]
  simp only [c, invCoord, e, ys, mul_assoc]

/-- The finite-order smooth matrix-carrier identity neighborhood transported
to the existing units-valued special subgroup. -/
def specialFormPreservingContDiffIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    Set (specialFormPreservingMatrixSubgroup F) :=
  specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F ''
    Matrix.specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar m

/-- The finite-order smooth units-valued identity neighborhood is open. -/
theorem isOpen_specialFormPreservingContDiffIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    IsOpen (specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m) := by
  exact (specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).isOpen_image.mpr
    (Matrix.isOpen_specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar m)

/-- The subgroup identity belongs to the finite-order smooth identity
neighborhood. -/
theorem one_mem_specialFormPreservingContDiffIdentityChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    (1 : specialFormPreservingMatrixSubgroup F) ∈
      specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m := by
  refine ⟨Matrix.specialOrthogonalMatrixIdentity F,
    Matrix.specialOrthogonalMatrixIdentity_mem_contDiffIdentityCarrierNeighborhood
      F hF hdet hchar m, ?_⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup_identity F

/-- The finite-order smooth units-valued identity neighborhood in the same
skew-adjoint coordinates as its matrix carrier. -/
noncomputable def specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m ≃ₜ
      Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m :=
  ((specialOrthogonalMatrixSetHomeomorphSpecialSubgroup F).image
    (Matrix.specialOrthogonalContDiffIdentityCarrierNeighborhood
      F hF hdet hchar m)).symm.trans
        (Matrix.specialOrthogonalContDiffIdentityCarrierSkewAdjointHomeomorph
          F hF hdet hchar m)

@[simp]
theorem specialFormPreservingContDiffIdentitySkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m) :
    ((specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
      F hF hdet hchar m g :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
          Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar m (g.1.1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

@[simp]
theorem coe_specialFormPreservingContDiffIdentitySkewAdjointHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (y : Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar m) :
    ((specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
      F hF hdet hchar m).symm y).1.1.1.1 =
      (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar m).symm
          (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
            F hF).symm y) :=
  rfl

/-- The finite-order smooth units-valued identity chart sends its center to
zero. -/
@[simp]
theorem specialFormPreservingContDiffIdentitySkewAdjointHomeomorph_one
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
        F hF hdet hchar m
        ⟨1, one_mem_specialFormPreservingContDiffIdentityChartNeighborhood
          F hF hdet hchar m⟩ =
      ⟨0, Matrix.zero_mem_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m⟩ := by
  apply Subtype.ext
  change (specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
    F hF hdet hchar m
      ⟨1, one_mem_specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m⟩ :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) = 0
  apply Subtype.ext
  rw [specialFormPreservingContDiffIdentitySkewAdjointHomeomorph_apply]
  simp

/-- The finite-order smooth identity neighborhood translated by left
multiplication to a specified special-orthogonal group point. -/
def specialFormPreservingContDiffTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    Set (specialFormPreservingMatrixSubgroup F) :=
  Homeomorph.mulLeft g ''
    specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m

/-- Every finite-order smooth translated special-orthogonal neighborhood is
open. -/
theorem isOpen_specialFormPreservingContDiffTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    IsOpen (specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g) := by
  exact (Homeomorph.mulLeft g).isOpen_image.mpr
    (isOpen_specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m)

/-- The center belongs to its finite-order smooth translated
special-orthogonal neighborhood. -/
theorem self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g := by
  refine ⟨1,
    one_mem_specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m, ?_⟩
  exact mul_one g

/-- The finite-order smooth translated neighborhood in the same skew-adjoint
coordinates as the identity chart. -/
noncomputable def
    specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g ≃ₜ
      Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m :=
  ((Homeomorph.mulLeft g).image
    (specialFormPreservingContDiffIdentityChartNeighborhood
      F hF hdet hchar m)).symm.trans
        (specialFormPreservingContDiffIdentitySkewAdjointHomeomorph
          F hF hdet hchar m)

@[simp]
theorem specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g) :
    ((specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
      F hF hdet hchar m g x :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
          Matrix (Fin n) (Fin n) K) =
      (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar m
          ((g⁻¹ * x.1).1.1.1 : Matrix (Fin n) (Fin n) K)).snd :=
  rfl

/-- The finite-order smooth translated skew-adjoint chart sends its center to
zero. -/
@[simp]
theorem specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
        F hF hdet hchar m g
        ⟨g, self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
          F hF hdet hchar m g⟩ =
      ⟨0, Matrix.zero_mem_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m⟩ := by
  apply Subtype.ext
  change (specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
    F hF hdet hchar m g
      ⟨g, self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g⟩ :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) = 0
  apply Subtype.ext
  rw [specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_apply]
  simp

/-- The finite-order smooth translated chart bundled between the full subgroup
and full skew-adjoint coordinate spaces. -/
noncomputable def
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (specialFormPreservingMatrixSubgroup F)
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g,
      isOpen_specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m,
      Matrix.isOpen_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar m⟩
  ((U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    (specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
      F hF hdet hchar m g).toOpenPartialHomeomorph).trans
      (V.openPartialHomeomorphSubtypeCoe hV)

@[simp]
theorem
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g).source =
        specialFormPreservingContDiffTranslatedChartNeighborhood
          F hF hdet hchar m g := by
  simp [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph]

@[simp]
theorem
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_target
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g).target =
        Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
          F hF hdet hchar m := by
  simp [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph]

/-- On its source, the finite-order ambient chart is the existing translated
subtype homeomorphism. -/
theorem
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F)
    (x : specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g) :
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g x.1 =
      (specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
        F hF hdet hchar m g x :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  let U : Opens (specialFormPreservingMatrixSubgroup F) :=
    ⟨specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g,
      isOpen_specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m g⟩
  let V : Opens (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
    ⟨Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m,
      Matrix.isOpen_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m⟩
  let hU : Nonempty U :=
    ⟨g, self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g⟩
  let hV : Nonempty V :=
    ⟨0, Matrix.zero_mem_specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar m⟩
  change (V.openPartialHomeomorphSubtypeCoe hV) ((
    specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
      F hF hdet hchar m g)
        ((U.openPartialHomeomorphSubtypeCoe hU).symm x.1)) = _
  have hx : x.1 ∈ (U.openPartialHomeomorphSubtypeCoe hU).target := by
    rw [U.openPartialHomeomorphSubtypeCoe_target]
    exact x.2
  have hinv : (U.openPartialHomeomorphSubtypeCoe hU).symm x.1 = x := by
    apply Subtype.ext
    exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv hx
  rw [hinv]
  rfl

/-- On the finite-order target, the inverse ambient translated chart is left
multiplication by its center composed with the identity-chart inverse. -/
theorem
    coe_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F)
    (y : Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar m) :
    ((specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g).symm y.1).1.1.1 =
      (g.1.1.1 : Matrix (Fin n) (Fin n) K) *
        (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
          F hF hdet hchar m).symm
            (0, (Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv
              F hF).symm y) := by
  let A :=
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g
  let H := specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
    F hF hdet hchar m g
  let x := H.symm y
  have hxsource : x.1 ∈ A.source := by
    rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
    exact x.2
  have happly : A x.1 = y.1 := by
    rw [show A x.1 = (H x :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) by
      exact
        specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply
          F hF hdet hchar m g x]
    exact congrArg Subtype.val (H.apply_symm_apply y)
  have hinv : A.symm y.1 = x.1 := by
    rw [← happly]
    exact A.left_inv hxsource
  rw [hinv]
  rfl

/-- Every subgroup point lies in the source of its centered finite-order
ambient chart. -/
theorem
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g).source := by
  rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
  exact self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
    F hF hdet hchar m g

/-- The finite-order ambient chart sends its center to zero. -/
@[simp]
theorem
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_center
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g g = 0 := by
  rw [show g = (⟨g,
    self_mem_specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g⟩ :
        specialFormPreservingContDiffTranslatedChartNeighborhood
          F hF hdet hchar m g).1 by rfl,
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply]
  exact congrArg Subtype.val
    (specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_center
      F hF hdet hchar m g)

/-- The sources of the centered finite-order ambient charts cover the
special-orthogonal subgroup. -/
theorem
    iUnion_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    (⋃ g : specialFormPreservingMatrixSubgroup F,
      (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  rw [Set.mem_iUnion]
  exact ⟨g,
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar m g⟩

/-- The finite-order smooth special-orthogonal charts collected as an explicit
parameterized charted space, not a global instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingContDiffChartedSpace
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) where
  atlas := Set.range fun g =>
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g
  chartAt g :=
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g
  mem_chart_source g :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar m g
  chart_mem_atlas g := ⟨g, rfl⟩

@[simp]
theorem specialFormPreservingContDiffChartedSpace_chartAt
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    @chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m) g =
        specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar m g :=
  rfl

@[simp]
theorem specialFormPreservingContDiffChartedSpace_atlas
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m) =
        Set.range fun g =>
          specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar m g :=
  rfl

/-- The preferred chart in the explicit finite-order charted space contains
its center in its source. -/
theorem specialFormPreservingContDiffChartedSpace_mem_chart_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F) :
    g ∈ (@chartAt (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m) g).source :=
  self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
    F hF hdet hchar m g

/-- A finite-order translated chart is the finite-order identity chart after
translating its argument back to the identity. -/
theorem
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g x : specialFormPreservingMatrixSubgroup F)
    (hx : x ∈
      (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g).source) :
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g x =
      specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m 1 (g⁻¹ * x) := by
  rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
    at hx
  rcases hx with ⟨z, hz, hzx⟩
  have hzx' : g * z = x := hzx
  have hshift : g⁻¹ * x = z := by
    rw [← hzx']
    simp
  have hshift_mem : g⁻¹ * x ∈
      specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m := by
    rwa [hshift]
  have hshift_mem_one : g⁻¹ * x ∈
      specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m 1 := by
    exact ⟨g⁻¹ * x, hshift_mem, one_mul _⟩
  let xs : specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m g :=
    ⟨x, ⟨z, hz, hzx⟩⟩
  let ys : specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m 1 :=
    ⟨g⁻¹ * x, hshift_mem_one⟩
  rw [show
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g x =
      specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
        F hF hdet hchar m g xs by
    exact
      specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar m g xs]
  rw [show
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m 1 (g⁻¹ * x) =
      specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
        F hF hdet hchar m 1 ys by
    exact
      specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar m 1 ys]
  apply Subtype.ext
  rw [specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_apply,
    specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_apply]
  simp [xs, ys]

/-- The finite-order coordinate transition from the chart centered at `g` to
the chart centered at `h`. -/
noncomputable def specialFormPreservingContDiffSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g h : specialFormPreservingMatrixSubgroup F) :
    OpenPartialHomeomorph (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (skewAdjointMatricesLieSubalgebra F).toSubmodule :=
  (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar m g).symm.trans
      (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m h)

@[simp]
theorem specialFormPreservingContDiffSkewAdjointTransition_source
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g h : specialFormPreservingMatrixSubgroup F) :
    (specialFormPreservingContDiffSkewAdjointTransition
      F hF hdet hchar m g h).source =
      Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
          F hF hdet hchar m ∩
        (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
          F hF hdet hchar m g).symm ⁻¹'
            specialFormPreservingContDiffTranslatedChartNeighborhood
              F hF hdet hchar m h := by
  simp [specialFormPreservingContDiffSkewAdjointTransition]

/-- On its overlap, a finite-order transition is the finite-order identity
chart applied after left translation of the represented point. -/
theorem specialFormPreservingContDiffSkewAdjointTransition_apply
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g h : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈ (specialFormPreservingContDiffSkewAdjointTransition
      F hF hdet hchar m g h).source) :
    specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m g h y =
      specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m 1
          (h⁻¹ *
            (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
              F hF hdet hchar m g).symm y) := by
  rw [specialFormPreservingContDiffSkewAdjointTransition,
    OpenPartialHomeomorph.trans_source] at hy
  rw [specialFormPreservingContDiffSkewAdjointTransition,
    OpenPartialHomeomorph.trans_apply]
  exact
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
      F hF hdet hchar m h _ hy.2

/-- Every finite-order coordinate transition is smooth to the selected order
on its overlap source. -/
theorem contDiffOn_specialFormPreservingContDiffSkewAdjointTransition
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g h : specialFormPreservingMatrixSubgroup F) :
    ContDiffOn K m
      (specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m g h)
      (specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m g h).source := by
  let e := Matrix.symmetricSkewAdjointOperatorKerContinuousLinearEquiv F hF
  let c : Matrix (Fin n) (Fin n) K :=
    (h⁻¹).1.1.1 * g.1.1.1
  let invCoord : (skewAdjointMatricesLieSubalgebra F).toSubmodule →
      Matrix (Fin n) (Fin n) K := fun y ↦
    (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar m).symm (0, e.symm y)
  let forwardCoord : Matrix (Fin n) (Fin n) K →
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := fun x ↦
    e (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
      F hF hdet hchar m x).snd
  let s := (specialFormPreservingContDiffSkewAdjointTransition
    F hF hdet hchar m g h).source
  have hsV : s ⊆
      Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
        F hF hdet hchar m := by
    intro y hy
    change y ∈ (specialFormPreservingContDiffSkewAdjointTransition
      F hF hdet hchar m g h).source at hy
    rw [specialFormPreservingContDiffSkewAdjointTransition_source] at hy
    exact hy.1
  have hinv : ContDiffOn K m invCoord s := by
    exact
      (Matrix.contDiffOn_specialOrthogonalContDiffIdentityZeroFiberCoordinate_symm
        F hF hdet hchar m).mono hsV
  have hshift : ContDiffOn K m (fun y ↦ c * invCoord y) s :=
    contDiff_const.contDiffOn.mul hinv
  have hchart : ContDiff K m
      (Matrix.symmetricFormPreservingContDiffDetOneIdentityChart
        F hF hdet hchar m) := by
    simpa [Matrix.symmetricFormPreservingContDiffDetOneIdentityChart,
      Matrix.symmetricFormPreservingContDiffIdentityChart] using
        (Matrix.contDiff_symmetricFormPreservingIdentityChart
          F hF hdet hchar).of_le
            (show (m : WithTop ℕ∞) ≤ ⊤ by simp)
  have hfwd : ContDiff K m forwardCoord := by
    exact e.contDiff.comp (contDiff_snd.comp hchart)
  have hcomp : ContDiffOn K m (fun y ↦ forwardCoord (c * invCoord y)) s := by
    simpa only [Function.comp_apply] using hfwd.comp_contDiffOn hshift
  apply hcomp.congr
  intro y hy
  change y ∈ (specialFormPreservingContDiffSkewAdjointTransition
    F hF hdet hchar m g h).source at hy
  rw [specialFormPreservingContDiffSkewAdjointTransition_apply
    F hF hdet hchar m g h y hy]
  rw [specialFormPreservingContDiffSkewAdjointTransition_source] at hy
  let ys : Matrix.specialOrthogonalContDiffIdentitySkewAdjointNeighborhood
      F hF hdet hchar m := ⟨y, hy.1⟩
  have hsymm :=
    coe_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_symm_apply
      F hF hdet hchar m g ys
  let x :=
    (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
      F hF hdet hchar m g).symm y
  have hx_h : x ∈
      specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m h := hy.2
  rcases hx_h with ⟨z, hz, hzx⟩
  have hshift_eq : h⁻¹ * x = z := by
    rw [← hzx]
    simp
  have hq_identity : h⁻¹ * x ∈
      specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m := by
    rwa [hshift_eq]
  have hq : h⁻¹ * x ∈
      specialFormPreservingContDiffTranslatedChartNeighborhood
        F hF hdet hchar m 1 :=
    ⟨h⁻¹ * x, hq_identity, one_mul _⟩
  let q : specialFormPreservingContDiffTranslatedChartNeighborhood
      F hF hdet hchar m 1 := ⟨h⁻¹ * x, hq⟩
  rw [show
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m 1 (h⁻¹ * x) =
      (specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph
        F hF hdet hchar m 1 q :
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) by
    exact
      specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply
        F hF hdet hchar m 1 q]
  apply Subtype.ext
  rw [specialFormPreservingContDiffTranslatedSkewAdjointHomeomorph_apply]
  simp only [forwardCoord, e,
    Matrix.coe_symmetricSkewAdjointOperatorKerContinuousLinearEquiv_apply]
  apply congrArg
  apply congrArg
  apply congrArg
  simp only [inv_one, one_mul]
  change ((h⁻¹ * x).1.1.1 : Matrix (Fin n) (Fin n) K) = c * invCoord y
  change (h⁻¹).1.1.1 * x.1.1.1 = c * invCoord y
  rw [hsymm]
  simp only [c, invCoord, e, ys, mul_assoc]

/-- Every common smooth coordinate transition belongs to the maximal-order
smooth structure groupoid. -/
theorem specialFormPreservingSmoothSkewAdjointTransition_mem_contDiffGroupoid
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g h : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar g h ∈
      contDiffGroupoid (∞ : WithTop ℕ∞)
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa [contDiffPregroupoid] using
      contDiffOn_infty_specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar g h
  · simpa [contDiffPregroupoid,
      specialFormPreservingSmoothSkewAdjointTransition] using
      contDiffOn_infty_specialFormPreservingSmoothSkewAdjointTransition
        F hF hdet hchar h g

/-- Every pair of charts in the explicit common smooth atlas is compatible in
the maximal-order smooth structure groupoid. This theorem does not install a
charted-space or groupoid instance. -/
theorem specialFormPreservingSmoothChartedSpace_compatible
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    {e e' : OpenPartialHomeomorph
      (specialFormPreservingMatrixSubgroup F)
      (skewAdjointMatricesLieSubalgebra F).toSubmodule}
    (he : e ∈ @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar))
    (he' : e' ∈ @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar)) :
    e.symm.trans e' ∈
      contDiffGroupoid (∞ : WithTop ℕ∞)
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  rw [specialFormPreservingSmoothChartedSpace_atlas] at he he'
  rcases he with ⟨g, rfl⟩
  rcases he' with ⟨h, rfl⟩
  exact
    specialFormPreservingSmoothSkewAdjointTransition_mem_contDiffGroupoid
      F hF hdet hchar g h

/-- The explicit common smooth charted space carries the maximal-order smooth
structure groupoid. This is a parameterized value, not a registered instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingSmoothHasGroupoid
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @HasGroupoid
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar)
      (contDiffGroupoid (∞ : WithTop ℕ∞)
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  refine { compatible := ?_ }
  intro e e' he he'
  exact specialFormPreservingSmoothChartedSpace_compatible
    F hF hdet hchar he he'

/-- The explicit common smooth chart and groupoid values define a smooth
real/complex manifold value. This is not a registered instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingSmoothIsManifold
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @IsManifold K _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  let gr := specialFormPreservingSmoothHasGroupoid F hF hdet hchar
  exact { gr with }

/-- In the centered common smooth charts, fixed left multiplication has the
identity coordinate map at every source point. -/
theorem specialFormPreservingSmooth_left_mul_coordinate
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈
      (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar x).target) :
    specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar (a * x)
        (a *
          (specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar x).symm y) = y := by
  let A := specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar
  have hx_source : (A x).symm y ∈ (A x).source :=
    (A x).symm.map_source hy
  have hax_source : a * (A x).symm y ∈ (A (a * x)).source := by
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
    rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source]
      at hx_source
    rcases hx_source with ⟨z, hz, hzx⟩
    refine ⟨z, hz, ?_⟩
    rw [← hzx]
    change (a * x) * z = a * (x * z)
    exact mul_assoc a x z
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    F hF hdet hchar (a * x) _ hax_source]
  rw [show (a * x)⁻¹ * (a * (A x).symm y) = x⁻¹ * (A x).symm y by
    simp [mul_assoc]]
  rw [← specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    F hF hdet hchar x _ hx_source]
  exact (A x).right_inv hy

/-- Under the explicit common smooth structure values, left multiplication is
maximally continuously differentiable at every source point. -/
theorem contMDiffAt_specialFormPreservingSmooth_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    ContMDiffAt
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (fun y ↦ a * y) x := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  change ContMDiffAt
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (∞ : WithTop ℕ∞) (fun y ↦ a * y) x
  let A := specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar
  have hsource_x : x ∈ (A x).source :=
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar x
  have hsource_ax : a * x ∈ (A (a * x)).source :=
    self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar (a * x)
  rw [contMDiffAt_iff_of_mem_source hsource_x hsource_ax]
  constructor
  · fun_prop
  · rw [extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id]
    simp only [specialFormPreservingSmoothChartedSpace_chartAt]
    apply contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A x).open_target.mem_nhds ((A x).map_source hsource_x)]
        with y hy
      exact specialFormPreservingSmooth_left_mul_coordinate
        F hF hdet hchar a x y hy
    · exact specialFormPreservingSmooth_left_mul_coordinate
        F hF hdet hchar a x ((A x) x) ((A x).map_source hsource_x)

/-- Under the explicit common smooth structure values, fixed left
multiplication is maximally continuously differentiable on the full subgroup. -/
theorem contMDiff_specialFormPreservingSmooth_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    ContMDiff
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (fun y ↦ a * y) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  intro x
  exact contMDiffAt_specialFormPreservingSmooth_left_mul
    F hF hdet hchar a x

/-- Fixed left multiplication is an explicit maximal-order diffeomorphism
under the locally installed common smooth manifold values. -/
noncomputable def specialFormPreservingSmoothLeftMulDiffeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    Diffeomorph
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (specialFormPreservingMatrixSubgroup F)
      (specialFormPreservingMatrixSubgroup F) (∞ : WithTop ℕ∞) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  exact
    { toEquiv := Equiv.mulLeft a
      contMDiff_toFun :=
        contMDiff_specialFormPreservingSmooth_left_mul F hF hdet hchar a
      contMDiff_invFun := by
        simpa only [Equiv.mulLeft_symm_apply] using
          contMDiff_specialFormPreservingSmooth_left_mul
            F hF hdet hchar a⁻¹ }

/-- Every finite-order coordinate transition belongs to the corresponding
smooth structure groupoid. -/
theorem specialFormPreservingContDiffSkewAdjointTransition_mem_contDiffGroupoid
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g h : specialFormPreservingMatrixSubgroup F) :
    specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m g h ∈
      contDiffGroupoid m
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simpa [contDiffPregroupoid] using
      contDiffOn_specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m g h
  · simpa [contDiffPregroupoid,
      specialFormPreservingContDiffSkewAdjointTransition] using
      contDiffOn_specialFormPreservingContDiffSkewAdjointTransition
        F hF hdet hchar m h g

/-- Every pair of charts in the explicit finite-order atlas is compatible in
the corresponding smooth structure groupoid. This theorem does not install a
charted-space or groupoid instance. -/
theorem specialFormPreservingContDiffChartedSpace_compatible
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    {e e' : OpenPartialHomeomorph
      (specialFormPreservingMatrixSubgroup F)
      (skewAdjointMatricesLieSubalgebra F).toSubmodule}
    (he : e ∈ @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m))
    (he' : e' ∈ @atlas (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m)) :
    e.symm.trans e' ∈
      contDiffGroupoid m
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  rw [specialFormPreservingContDiffChartedSpace_atlas] at he he'
  rcases he with ⟨g, rfl⟩
  rcases he' with ⟨h, rfl⟩
  exact
    specialFormPreservingContDiffSkewAdjointTransition_mem_contDiffGroupoid
      F hF hdet hchar m g h

/-- The explicit finite-order charted space carries the corresponding smooth
structure groupoid. This is a parameterized value, not a registered instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingContDiffHasGroupoid
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    @HasGroupoid
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m)
      (contDiffGroupoid m
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar m
  refine { compatible := ?_ }
  intro e e' he he'
  exact specialFormPreservingContDiffChartedSpace_compatible
    F hF hdet hchar m he he'

/-- The explicit finite-order chart and groupoid values define a finite-order
real/complex manifold value. This is not a registered instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingContDiffIsManifold
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ) :
    @IsManifold K _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      m (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingContDiffChartedSpace F hF hdet hchar m) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar m
  let gr := specialFormPreservingContDiffHasGroupoid F hF hdet hchar m
  exact { gr with }

/-- At first order, the identity tangent model of the explicit manifold is
continuously linearly equivalent to the skew-adjoint matrix submodule. -/
noncomputable def specialFormPreservingContDiffIdentityTangentEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingContDiffChartedSpace F hF hdet hchar 1)
        (1 : specialFormPreservingMatrixSubgroup F) ≃L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃L[K]
    (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact ContinuousLinearEquiv.refl K _

/-- Passing a skew-adjoint matrix into the identity tangent model and back
preserves its ambient matrix. -/
@[simp]
theorem coe_specialFormPreservingContDiffIdentityTangentEquiv_apply_symm
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (X : (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
    (((specialFormPreservingContDiffIdentityTangentEquiv F hF hdet hchar)
      ((specialFormPreservingContDiffIdentityTangentEquiv
        F hF hdet hchar).symm X) :
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) :
      Matrix (Fin n) (Fin n) K) = X := by
  simp

/-- The maximal-order common smooth manifold value, restricted to first
order. This remains a parameterized value, not a registered instance. -/
@[implicit_reducible]
noncomputable def specialFormPreservingSmoothIsManifoldOne
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @IsManifold K _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      1 (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  exact IsManifold.of_le
    (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)

/-- At first order, the identity tangent model of the common smooth manifold
is continuously linearly equivalent to the skew-adjoint matrix submodule. -/
noncomputable def specialFormPreservingSmoothIdentityTangentEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingSmoothChartedSpace F hF hdet hchar)
        (1 : specialFormPreservingMatrixSubgroup F) ≃L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifoldOne F hF hdet hchar
  change (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃L[K]
    (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact ContinuousLinearEquiv.refl K _

/-- The common smooth and finite-atlas identity tangent models are identified
through their shared skew-adjoint coordinate model. -/
noncomputable def specialFormPreservingSmoothIdentityTangentFiniteEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingSmoothChartedSpace F hF hdet hchar)
        (1 : specialFormPreservingMatrixSubgroup F) ≃L[K]
      @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingContDiffChartedSpace F hF hdet hchar 1)
        (1 : specialFormPreservingMatrixSubgroup F) :=
  (specialFormPreservingSmoothIdentityTangentEquiv
    F hF hdet hchar).trans
      (specialFormPreservingContDiffIdentityTangentEquiv
        F hF hdet hchar).symm

/-- The common-to-finite identity tangent comparison preserves the shared
skew-adjoint model coordinate. -/
@[simp]
theorem specialFormPreservingSmoothIdentityTangentFiniteEquiv_model
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (v : @TangentSpace K _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
      (skewAdjointMatricesLieSubalgebra F).toSubmodule _
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (specialFormPreservingMatrixSubgroup F) _
      (specialFormPreservingSmoothChartedSpace F hF hdet hchar)
      (1 : specialFormPreservingMatrixSubgroup F)) :
    specialFormPreservingContDiffIdentityTangentEquiv F hF hdet hchar
        (specialFormPreservingSmoothIdentityTangentFiniteEquiv
          F hF hdet hchar v) =
      specialFormPreservingSmoothIdentityTangentEquiv F hF hdet hchar v := by
  simp [specialFormPreservingSmoothIdentityTangentFiniteEquiv]

/-- The tangent space at any point of the common smooth manifold is the shared
skew-adjoint model, exposed as a continuous linear equivalence. -/
noncomputable def specialFormPreservingSmoothTangentModelEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) x ≃L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  change (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃L[K]
    (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact ContinuousLinearEquiv.refl K _

/-- The common smooth fixed-left diffeomorphism induces a continuous linear
equivalence from the tangent space at `x` to the tangent space at `a * x`. -/
noncomputable def specialFormPreservingSmoothLeftMulTangentEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) x ≃L[K]
      TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) (a * x) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  exact (specialFormPreservingSmoothLeftMulDiffeomorph
    F hF hdet hchar a).mfderivToContinuousLinearEquiv (by simp) x

/-- In the shared skew-adjoint tangent model, common smooth fixed-left tangent
transport is the identity continuous linear map. -/
theorem specialFormPreservingSmoothLeftMulTangentEquiv_model
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothChartedSpace F hF hdet hchar
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingSmoothIsManifold F hF hdet hchar
    (specialFormPreservingSmoothTangentModelEquiv
        F hF hdet hchar (a * x)).toContinuousLinearMap.comp
      ((specialFormPreservingSmoothLeftMulTangentEquiv
          F hF hdet hchar a x).toContinuousLinearMap.comp
        (specialFormPreservingSmoothTangentModelEquiv
          F hF hdet hchar x).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothChartedSpace F hF hdet hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingSmoothIsManifold F hF hdet hchar
  change mfderiv
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun y ↦ a * y) x =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule
  apply HasMFDerivAt.mfderiv
  rw [HasMFDerivAt]
  constructor
  · fun_prop
  · let A :=
      specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar
    have hsource_x : x ∈ (A x).source :=
      self_mem_specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_source
        F hF hdet hchar x
    rw [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id]
    simp only [specialFormPreservingSmoothChartedSpace_chartAt]
    apply (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A x).open_target.mem_nhds ((A x).map_source hsource_x)]
        with y hy
      simp only [Function.comp_apply, id_eq]
      exact specialFormPreservingSmooth_left_mul_coordinate
        F hF hdet hchar a x y hy
    · simp only [Function.comp_apply, id_eq, extChartAt_coe,
        modelWithCornersSelf_coe,
        specialFormPreservingSmoothChartedSpace_chartAt]
      exact specialFormPreservingSmooth_left_mul_coordinate
        F hF hdet hchar a x ((A x) x) ((A x).map_source hsource_x)

/-- In the centered finite-order charts, left multiplication by the center is
the identity coordinate map on the identity-chart target. -/
theorem specialFormPreservingContDiff_left_mul_coordinate
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (g : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈
      (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m 1).target) :
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m g
        (g *
          (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar m 1).symm y) = y := by
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar m
  have hx_one : (A 1).symm y ∈ (A 1).source :=
    (A 1).symm.map_source hy
  have hx_identity : (A 1).symm y ∈
      specialFormPreservingContDiffIdentityChartNeighborhood
        F hF hdet hchar m := by
    rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
      at hx_one
    rcases hx_one with ⟨z, hz, hzx⟩
    simpa [← hzx] using hz
  have hx_g : g * (A 1).symm y ∈ (A g).source := by
    rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
    exact ⟨(A 1).symm y, hx_identity, rfl⟩
  rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    F hF hdet hchar m g _ hx_g]
  simpa using (A 1).right_inv hy

/-- In centered finite-order charts, left multiplication has the identity
coordinate map at every source point. -/
theorem specialFormPreservingContDiff_left_mul_coordinate_at
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2) (m : ℕ)
    (a x : specialFormPreservingMatrixSubgroup F)
    (y : (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (hy : y ∈
      (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m x).target) :
    specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
        F hF hdet hchar m (a * x)
        (a *
          (specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
            F hF hdet hchar m x).symm y) = y := by
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar m
  have hx_source : (A x).symm y ∈ (A x).source :=
    (A x).symm.map_source hy
  have hax_source : a * (A x).symm y ∈ (A (a * x)).source := by
    rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
    rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source]
      at hx_source
    rcases hx_source with ⟨z, hz, hzx⟩
    refine ⟨z, hz, ?_⟩
    rw [← hzx]
    change (a * x) * z = a * (x * z)
    exact mul_assoc a x z
  rw [specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    F hF hdet hchar m (a * x) _ hax_source]
  rw [show (a * x)⁻¹ * (a * (A x).symm y) = x⁻¹ * (A x).symm y by
    simp [mul_assoc]]
  rw [← specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_apply_eq_identity
    F hF hdet hchar m x _ hx_source]
  exact (A x).right_inv hy

/-- With the explicit order-one manifold values installed locally, left
multiplication by a group point is continuously differentiable at the
identity. -/
theorem contMDiffAt_specialFormPreservingContDiff_left_mul_one
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    ContMDiffAt
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      1 (fun x ↦ g * x) 1 := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change ContMDiffAt
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    1 (fun x ↦ g * x) 1
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar 1
  have hsource_one : (1 : specialFormPreservingMatrixSubgroup F) ∈ (A 1).source :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 1
  have hsource_g : g * (1 : specialFormPreservingMatrixSubgroup F) ∈ (A g).source := by
    rw [show g * (1 : specialFormPreservingMatrixSubgroup F) = g by simp]
    exact self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 g
  rw [contMDiffAt_iff_of_mem_source hsource_one hsource_g]
  constructor
  · fun_prop
  · rw [extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id]
    simp only [specialFormPreservingContDiffChartedSpace_chartAt]
    apply contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A 1).open_target.mem_nhds ((A 1).map_source hsource_one)]
        with y hy
      exact specialFormPreservingContDiff_left_mul_coordinate
        F hF hdet hchar 1 g y hy
    · exact specialFormPreservingContDiff_left_mul_coordinate
        F hF hdet hchar 1 g ((A 1) 1) ((A 1).map_source hsource_one)

/-- In the centered order-one charts, the derivative of left multiplication
at the identity is the identity continuous linear map. -/
theorem hasMFDerivAt_specialFormPreservingContDiff_left_mul_one
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    HasMFDerivAt
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (fun x ↦ g * x) 1
      (ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change HasMFDerivAt
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun x ↦ g * x) 1
    (ContinuousLinearMap.id K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar 1
  have hsource_one : (1 : specialFormPreservingMatrixSubgroup F) ∈ (A 1).source :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 1
  rw [HasMFDerivAt]
  constructor
  · fun_prop
  · rw [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id, mul_one]
    simp only [specialFormPreservingContDiffChartedSpace_chartAt]
    apply (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A 1).open_target.mem_nhds ((A 1).map_source hsource_one)]
        with y hy
      simp only [Function.comp_apply, id_eq]
      exact specialFormPreservingContDiff_left_mul_coordinate
        F hF hdet hchar 1 g y hy
    · simp only [Function.comp_apply, id_eq, extChartAt_coe,
        modelWithCornersSelf_coe,
        specialFormPreservingContDiffChartedSpace_chartAt]
      exact specialFormPreservingContDiff_left_mul_coordinate
        F hF hdet hchar 1 g ((A 1) 1) ((A 1).map_source hsource_one)

/-- The explicit order-one manifold derivative of left multiplication at the
identity is the identity model map. -/
theorem mfderiv_specialFormPreservingContDiff_left_mul_one
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (g : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    mfderiv
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (fun x ↦ g * x) 1 =
        ContinuousLinearMap.id K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change mfderiv
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun x ↦ g * x) 1 =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact (hasMFDerivAt_specialFormPreservingContDiff_left_mul_one
    F hF hdet hchar g).mfderiv

/-- With the explicit order-one manifold values installed locally, left
multiplication is continuously differentiable at every source point. -/
theorem contMDiffAt_specialFormPreservingContDiff_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    ContMDiffAt
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      1 (fun y ↦ a * y) x := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change ContMDiffAt
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    1 (fun y ↦ a * y) x
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar 1
  have hsource_x : x ∈ (A x).source :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 x
  have hsource_ax : a * x ∈ (A (a * x)).source :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 (a * x)
  rw [contMDiffAt_iff_of_mem_source hsource_x hsource_ax]
  constructor
  · fun_prop
  · rw [extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id]
    simp only [specialFormPreservingContDiffChartedSpace_chartAt]
    apply contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A x).open_target.mem_nhds ((A x).map_source hsource_x)]
        with y hy
      exact specialFormPreservingContDiff_left_mul_coordinate_at
        F hF hdet hchar 1 a x y hy
    · exact specialFormPreservingContDiff_left_mul_coordinate_at
        F hF hdet hchar 1 a x ((A x) x) ((A x).map_source hsource_x)

/-- In centered order-one charts, the derivative of left multiplication at
every source point is the identity continuous linear map. -/
theorem hasMFDerivAt_specialFormPreservingContDiff_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    HasMFDerivAt
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (fun y ↦ a * y) x
      (ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change HasMFDerivAt
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun y ↦ a * y) x
    (ContinuousLinearMap.id K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
  let A := specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph
    F hF hdet hchar 1
  have hsource_x : x ∈ (A x).source :=
    self_mem_specialFormPreservingContDiffTranslatedSkewAdjointOpenPartialHomeomorph_source
      F hF hdet hchar 1 x
  rw [HasMFDerivAt]
  constructor
  · fun_prop
  · rw [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id]
    simp only [specialFormPreservingContDiffChartedSpace_chartAt]
    apply (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
    · rw [nhdsWithin_univ]
      filter_upwards [(A x).open_target.mem_nhds ((A x).map_source hsource_x)]
        with y hy
      simp only [Function.comp_apply, id_eq]
      exact specialFormPreservingContDiff_left_mul_coordinate_at
        F hF hdet hchar 1 a x y hy
    · simp only [Function.comp_apply, id_eq, extChartAt_coe,
        modelWithCornersSelf_coe,
        specialFormPreservingContDiffChartedSpace_chartAt]
      exact specialFormPreservingContDiff_left_mul_coordinate_at
        F hF hdet hchar 1 a x ((A x) x) ((A x).map_source hsource_x)

/-- The explicit order-one manifold derivative of left multiplication at
every source point is the identity model map. -/
theorem mfderiv_specialFormPreservingContDiff_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    mfderiv
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (fun y ↦ a * y) x =
        ContinuousLinearMap.id K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change mfderiv
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun y ↦ a * y) x =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact (hasMFDerivAt_specialFormPreservingContDiff_left_mul
    F hF hdet hchar a x).mfderiv

/-- With the explicit order-one manifold values installed locally, fixed left
multiplication is continuously differentiable on the full subgroup. -/
theorem contMDiff_specialFormPreservingContDiff_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    ContMDiff
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      1 (fun y ↦ a * y) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  intro x
  exact contMDiffAt_specialFormPreservingContDiff_left_mul
    F hF hdet hchar a x

/-- With the explicit order-one manifold values installed locally, fixed left
multiplication is differentiable on the full subgroup. -/
theorem mdifferentiable_specialFormPreservingContDiff_left_mul
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    MDifferentiable
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (fun y ↦ a * y) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  exact (contMDiff_specialFormPreservingContDiff_left_mul
    F hF hdet hchar a).mdifferentiable one_ne_zero

/-- Fixed left multiplication is an explicit order-one diffeomorphism under
the locally installed real/complex special-orthogonal manifold values. -/
noncomputable def specialFormPreservingContDiffLeftMulDiffeomorph
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    Diffeomorph
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule)
      (specialFormPreservingMatrixSubgroup F)
      (specialFormPreservingMatrixSubgroup F) 1 := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  exact
    { toEquiv := Equiv.mulLeft a
      contMDiff_toFun :=
        contMDiff_specialFormPreservingContDiff_left_mul F hF hdet hchar a
      contMDiff_invFun := by
        simpa only [Equiv.mulLeft_symm_apply] using
          contMDiff_specialFormPreservingContDiff_left_mul
            F hF hdet hchar a⁻¹ }

/-- The tangent space at any point of the explicit order-one manifold is the
common skew-adjoint model, exposed as a continuous linear equivalence. -/
noncomputable def specialFormPreservingContDiffTangentModelEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) x ≃L[K]
      (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change (skewAdjointMatricesLieSubalgebra F).toSubmodule ≃L[K]
    (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact ContinuousLinearEquiv.refl K _

/-- At every point, the common smooth and finite-atlas tangent models are
identified through their shared skew-adjoint coordinate model. -/
noncomputable def specialFormPreservingSmoothTangentFiniteEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (x : specialFormPreservingMatrixSubgroup F) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingSmoothChartedSpace F hF hdet hchar) x ≃L[K]
      @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra F).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule)
        (specialFormPreservingMatrixSubgroup F) _
        (specialFormPreservingContDiffChartedSpace F hF hdet hchar 1) x :=
  (specialFormPreservingSmoothTangentModelEquiv
    F hF hdet hchar x).trans
      (specialFormPreservingContDiffTangentModelEquiv
        F hF hdet hchar x).symm

/-- The fixed-left diffeomorphism induces a continuous linear equivalence
from the tangent space at `x` to the tangent space at `a * x`. -/
noncomputable def specialFormPreservingContDiffLeftMulTangentEquiv
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) x ≃L[K]
      TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) (a * x) := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  exact (specialFormPreservingContDiffLeftMulDiffeomorph
    F hF hdet hchar a).mfderivToContinuousLinearEquiv one_ne_zero x

/-- In the common skew-adjoint tangent model, fixed-left tangent transport is
the identity continuous linear map. -/
theorem specialFormPreservingContDiffLeftMulTangentEquiv_model
    (F : Matrix (Fin n) (Fin n) K) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hchar : ringChar K ≠ 2)
    (a x : specialFormPreservingMatrixSubgroup F) :
    letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup F) :=
      specialFormPreservingContDiffIsManifold F hF hdet hchar 1
    (specialFormPreservingContDiffTangentModelEquiv
        F hF hdet hchar (a * x)).toContinuousLinearMap.comp
      ((specialFormPreservingContDiffLeftMulTangentEquiv
          F hF hdet hchar a x).toContinuousLinearMap.comp
        (specialFormPreservingContDiffTangentModelEquiv
          F hF hdet hchar x).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule := by
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra F).toSubmodule
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffChartedSpace F hF hdet hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup F) :=
    specialFormPreservingContDiffIsManifold F hF hdet hchar 1
  change mfderiv
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (modelWithCornersSelf K
      (skewAdjointMatricesLieSubalgebra F).toSubmodule)
    (fun y ↦ a * y) x =
      ContinuousLinearMap.id K
        (skewAdjointMatricesLieSubalgebra F).toSubmodule
  exact mfderiv_specialFormPreservingContDiff_left_mul
    F hF hdet hchar a x

private theorem isSymm_map_algebraMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    (F.map (algebraMap ℚ K)).IsSymm :=
  hF.map _

private theorem det_map_algebraMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ K)).det ≠ 0 := by
  have hmap : algebraMap ℚ K F.det ≠ 0 := by
    intro hz
    apply hdet
    apply (algebraMap ℚ K).injective
    simpa using hz
  have heq : (F.map (algebraMap ℚ K)).det = algebraMap ℚ K F.det := by
    simpa [RingHom.mapMatrix_apply] using ((algebraMap ℚ K).map_det F).symm
  rwa [heq]

private theorem rclike_ringChar_ne_two : ringChar K ≠ 2 := by
  norm_num [ringChar.eq K]

/-- The rationally normalized skew-adjoint determinant form pulled back to the
tangent space at a supplied point of the explicit order-one manifold. -/
noncomputable def specialFormPreservingContDiffDetFormAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingContDiffChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1)
        x [⋀^Fin (Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F))]→ₗ[K] K := by
  exact (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
    (specialFormPreservingContDiffTangentModelEquiv
      (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
      (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
      x).toContinuousLinearMap.toLinearMap

/-- The rationally normalized determinant form as a continuous alternating
form on the tangent model at a supplied point. -/
noncomputable def specialFormPreservingContDiffContinuousDetFormAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingContDiffChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1)
        x [⋀^Fin (Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F))]→L[K] K := by
  exact
    (Matrix.skewAdjointScalarExtensionContinuousDetForm (K := K) F).compContinuousLinearMap
      (specialFormPreservingContDiffTangentModelEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        x).toContinuousLinearMap

/-- The rationally normalized determinant form as a continuous alternating
form on the common smooth tangent model at a supplied point. -/
noncomputable def specialFormPreservingSmoothContinuousDetFormAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingSmoothChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two)
        x [⋀^Fin (Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F))]→L[K] K := by
  exact
    (Matrix.skewAdjointScalarExtensionContinuousDetForm (K := K) F).compContinuousLinearMap
      (specialFormPreservingSmoothTangentModelEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        x).toContinuousLinearMap

/-- Pulling the finite-atlas pointwise form back through the explicit tangent
comparison gives the common smooth pointwise form. -/
theorem specialFormPreservingSmoothContinuousDetFormAt_eq_finite_pullback
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    (specialFormPreservingContDiffContinuousDetFormAt F hF hdet x).compContinuousLinearMap
        (specialFormPreservingSmoothTangentFiniteEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap =
      specialFormPreservingSmoothContinuousDetFormAt F hF hdet x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change
    ((Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
      (specialFormPreservingContDiffTangentModelEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        x).toContinuousLinearMap.toLinearMap).compLinearMap
          (specialFormPreservingSmoothTangentFiniteEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
            x).toContinuousLinearMap.toLinearMap =
      (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap.toLinearMap
  rw [AlternatingMap.compLinearMap_assoc]
  apply congrArg (fun L ↦
    (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap L)
  apply LinearMap.ext
  intro v
  let ef := specialFormPreservingContDiffTangentModelEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x
  let es := specialFormPreservingSmoothTangentModelEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x
  change ef (ef.symm (es v)) = es v
  exact ef.apply_symm_apply (es v)

/-- The common smooth continuous pointwise determinant forms are invariant
under fixed-left tangent transport. -/
theorem specialFormPreservingSmoothContinuousDetFormAt_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    (specialFormPreservingSmoothContinuousDetFormAt
        F hF hdet (a * x)).compContinuousLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toContinuousLinearMap =
      specialFormPreservingSmoothContinuousDetFormAt F hF hdet x := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothChartedSpace FK hFK hdetK hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothIsManifold FK hFK hdetK hchar
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change
    ((Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
      (specialFormPreservingSmoothTangentModelEquiv
        FK hFK hdetK hchar (a * x)).toContinuousLinearMap.toLinearMap).compLinearMap
          (specialFormPreservingSmoothLeftMulTangentEquiv
            FK hFK hdetK hchar a x).toContinuousLinearMap.toLinearMap =
      (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          FK hFK hdetK hchar x).toContinuousLinearMap.toLinearMap
  rw [AlternatingMap.compLinearMap_assoc]
  apply congrArg (fun L ↦
    (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap L)
  apply LinearMap.ext
  intro v
  let ex := specialFormPreservingSmoothTangentModelEquiv
    FK hFK hdetK hchar x
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦ L (ex v))
    (specialFormPreservingSmoothLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [ContinuousLinearMap.comp_apply, ex] using hmodel

/-- The scalar-extended skew-adjoint finite basis transported to the common
smooth tangent model at a supplied point. -/
noncomputable def specialFormPreservingSmoothTangentFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) K
      (@TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingSmoothChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two)
        x) :=
  (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).map
    (specialFormPreservingSmoothTangentModelEquiv
      (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
      (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
      x).symm.toLinearEquiv

/-- The common smooth continuous tangent form has volume one on its
transported scalar-extended finite basis. -/
theorem specialFormPreservingSmoothContinuousDetFormAt_apply_tangent_finBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingSmoothContinuousDetFormAt F hF hdet x
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x) = 1 := by
  change Matrix.skewAdjointScalarExtensionContinuousDetForm (K := K) F
      (fun j ↦ (specialFormPreservingSmoothTangentModelEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x)
          ((specialFormPreservingSmoothTangentModelEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x).symm
              (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F j))) = 1
  simpa [specialFormPreservingSmoothTangentFinBasis] using
    Matrix.skewAdjointScalarExtensionCoordinateDetForm_apply_finBasis
      (K := K) F 0

/-- The common smooth continuous tangent form is the pullback of the fixed
coordinate differential-form value at every coordinate point. -/
theorem specialFormPreservingSmoothContinuousDetFormAt_eq_coordinate_pullback
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    (Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap =
      specialFormPreservingSmoothContinuousDetFormAt F hF hdet x :=
  rfl

/-- Every coordinate-form pullback evaluates to one on the normalized common
smooth tangent basis. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_apply_tangent_finBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    (Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x) = 1 := by
  rw [specialFormPreservingSmoothContinuousDetFormAt_eq_coordinate_pullback]
  exact specialFormPreservingSmoothContinuousDetFormAt_apply_tangent_finBasis
    (K := K) F hF hdet x

/-- The common smooth continuous determinant form is nonzero on every
supplied tangent model. -/
theorem specialFormPreservingSmoothContinuousDetFormAt_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingSmoothContinuousDetFormAt F hF hdet x ≠ 0 := by
  intro hzero
  have hone :=
    specialFormPreservingSmoothContinuousDetFormAt_apply_tangent_finBasis
      (K := K) F hF hdet x
  rw [hzero] at hone
  simp at hone

/-- Common smooth fixed-left tangent transport carries the normalized tangent
basis at `x` to the normalized tangent basis at `a * x`. -/
theorem specialFormPreservingSmoothTangentFinBasis_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    (specialFormPreservingSmoothTangentFinBasis F hF hdet x).map
        (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearEquiv =
      specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x) := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothChartedSpace FK hFK hdetK hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothIsManifold FK hFK hdetK hchar
  ext j
  apply (specialFormPreservingSmoothTangentModelEquiv
    FK hFK hdetK hchar (a * x)).injective
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦
      L (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F j))
    (specialFormPreservingSmoothLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [specialFormPreservingSmoothTangentFinBasis,
    Module.Basis.map_apply, ContinuousLinearMap.comp_apply,
    FK, hFK, hdetK, hchar] using hmodel

/-- Common smooth fixed-left tangent transport preserves coordinates in the
normalized pointwise tangent bases. -/
theorem specialFormPreservingSmoothTangentFinBasis_repr_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    ∀ v : TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) x,
      (specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x)).repr
          (specialFormPreservingSmoothLeftMulTangentEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
            a x v) =
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x).repr v := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothChartedSpace FK hFK hdetK hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothIsManifold FK hFK hdetK hchar
  intro v
  simp only [specialFormPreservingSmoothTangentFinBasis,
    Module.Basis.map_repr, LinearEquiv.trans_apply]
  apply congrArg
    (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).repr
  let ex := specialFormPreservingSmoothTangentModelEquiv
    FK hFK hdetK hchar x
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦ L (ex v))
    (specialFormPreservingSmoothLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [ContinuousLinearMap.comp_apply, FK, hFK, hdetK, hchar, ex] using hmodel

set_option maxRecDepth 2048 in
/-- The matrix of common smooth fixed-left tangent transport in the normalized
pointwise tangent bases is the identity. -/
theorem specialFormPreservingSmoothLeftMulTangentEquiv_toMatrix_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    LinearMap.toMatrix
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x)
        (specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap = 1 := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothChartedSpace FK hFK hdetK hchar
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule)
      (∞ : WithTop ℕ∞) (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingSmoothIsManifold FK hFK hdetK hchar
  have hbasis := specialFormPreservingSmoothTangentFinBasis_left_invariant
    (K := K) F hF hdet a x
  ext i j
  rw [LinearMap.toMatrix_apply]
  have hj := congrArg (fun b ↦ b j) hbasis
  have hj' :
      (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearEquiv
          (specialFormPreservingSmoothTangentFinBasis F hF hdet x j) =
        specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x) j := by
    simpa only [Module.Basis.map_apply] using hj
  have hjcoord := congrArg
    (fun v ↦ (specialFormPreservingSmoothTangentFinBasis
      F hF hdet (a * x)).repr v i) hj'
  exact hjcoord.trans (by
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm])

/-- Common smooth fixed-left tangent transport has determinant one in the
normalized pointwise tangent bases. -/
theorem specialFormPreservingSmoothLeftMulTangentEquiv_toMatrix_det
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    (LinearMap.toMatrix
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x)
        (specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap).det = 1 := by
  rw [specialFormPreservingSmoothLeftMulTangentEquiv_toMatrix_eq_one
    (K := K) F hF hdet a x, Matrix.det_one]

/-- The scalar-extended skew-adjoint finite basis transported to the tangent
model at a supplied point. -/
noncomputable def specialFormPreservingContDiffTangentFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) K
      (@TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingContDiffChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1)
        x) :=
  (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).map
    (specialFormPreservingContDiffTangentModelEquiv
      (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
      (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
      x).symm.toLinearEquiv

/-- The determinant of the transported tangent basis is the normalized
pointwise tangent determinant form. -/
theorem specialFormPreservingContDiffTangentFinBasis_det
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    (specialFormPreservingContDiffTangentFinBasis F hF hdet x).det =
      specialFormPreservingContDiffDetFormAt F hF hdet x := by
  let e := specialFormPreservingContDiffTangentModelEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x
  simpa only [specialFormPreservingContDiffTangentFinBasis,
    specialFormPreservingContDiffDetFormAt,
    Matrix.skewAdjointScalarExtensionDetForm,
    ContinuousLinearEquiv.coe_toLinearEquiv, e] using
      (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).det_map'
        e.symm.toLinearEquiv

/-- The determinant alternating map of the normalized basis on a common
smooth tangent model. -/
noncomputable def specialFormPreservingSmoothTangentDetFormAt
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingSmoothChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two)
        x [⋀^Fin (Module.finrank ℚ
          (skewAdjointMatricesLieSubalgebra F))]→ₗ[K] K :=
  (specialFormPreservingSmoothTangentFinBasis F hF hdet x).det

/-- The determinant of the normalized common smooth tangent basis is the
underlying alternating map of the continuous pointwise determinant form. -/
theorem specialFormPreservingSmoothTangentDetFormAt_eq_continuous
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingSmoothTangentDetFormAt F hF hdet x =
      (specialFormPreservingSmoothContinuousDetFormAt
        F hF hdet x).toAlternatingMap := by
  let e := specialFormPreservingSmoothTangentModelEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x
  simpa only [specialFormPreservingSmoothTangentDetFormAt,
    specialFormPreservingSmoothTangentFinBasis,
    specialFormPreservingSmoothContinuousDetFormAt,
    Matrix.skewAdjointScalarExtensionContinuousDetForm_toAlternatingMap,
    ContinuousLinearEquiv.coe_toLinearEquiv, e] using
      (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).det_map'
        e.symm.toLinearEquiv

/-- Pulling the finite-atlas normalized tangent determinant form through the
pointwise tangent comparison gives the common smooth determinant form. -/
theorem specialFormPreservingSmoothTangentDetFormAt_eq_finite_pullback
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    (specialFormPreservingContDiffTangentFinBasis F hF hdet x).det.compLinearMap
        (specialFormPreservingSmoothTangentFiniteEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toLinearMap =
      specialFormPreservingSmoothTangentDetFormAt F hF hdet x := by
  rw [specialFormPreservingContDiffTangentFinBasis_det,
    specialFormPreservingSmoothTangentDetFormAt_eq_continuous]
  have h := congrArg ContinuousAlternatingMap.toAlternatingMap
    (specialFormPreservingSmoothContinuousDetFormAt_eq_finite_pullback
      (K := K) F hF hdet x)
  exact h

/-- The underlying alternating map of every common smooth coordinate-form
pullback is the basis-defined tangent determinant form. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_toAlternatingMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap).toAlternatingMap =
      specialFormPreservingSmoothTangentDetFormAt F hF hdet x := by
  rw [specialFormPreservingSmoothContinuousDetFormAt_eq_coordinate_pullback]
  exact (specialFormPreservingSmoothTangentDetFormAt_eq_continuous
    (K := K) F hF hdet x).symm

/-- The underlying alternating map of every common smooth coordinate-form
pullback is nonzero, witnessed by its normalized basis evaluation. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_toAlternatingMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap).toAlternatingMap ≠ 0 := by
  intro hzero
  have hone :=
    specialFormPreservingSmoothCoordinateDetFormPullback_apply_tangent_finBasis
      (K := K) F hF hdet x y
  change
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap).toAlternatingMap
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x) = 1 at hone
  rw [hzero] at hone
  simp at hone

/-- Fixed-left tangent transport identifies arbitrary target and source
coordinate-form pullbacks on the common smooth tangent models. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K)))
    (y z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          (a * x)).toContinuousLinearMap).compContinuousLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toContinuousLinearMap =
      (Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F z).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap := by
  rw [specialFormPreservingSmoothContinuousDetFormAt_eq_coordinate_pullback,
    specialFormPreservingSmoothContinuousDetFormAt_eq_coordinate_pullback]
  exact specialFormPreservingSmoothContinuousDetFormAt_left_invariant
    (K := K) F hF hdet a x

/-- The underlying alternating maps of arbitrary target and source coordinate
pullbacks satisfy the same fixed-left compatibility. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_toAlternatingMap_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K)))
    (y z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          (a * x)).toContinuousLinearMap).toAlternatingMap.compLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toLinearMap =
      ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F z).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap).toAlternatingMap := by
  have h := congrArg ContinuousAlternatingMap.toAlternatingMap
    (specialFormPreservingSmoothCoordinateDetFormPullback_left_invariant
      (K := K) F hF hdet a x y z)
  exact h

/-- The algebraic fixed-left coordinate pullback is the normalized tangent
Jacobian determinant acting on the source coordinate pullback. -/
theorem specialFormPreservingSmoothCoordinateDetFormPullback_eq_jacobian_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K)))
    (y z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingSmoothTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          (a * x)).toContinuousLinearMap).toAlternatingMap.compLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toLinearMap =
      (LinearMap.toMatrix
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x)
        (specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap).det •
        ((Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F z).compContinuousLinearMap
          (specialFormPreservingSmoothTangentModelEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
            x).toContinuousLinearMap).toAlternatingMap := by
  rw [specialFormPreservingSmoothLeftMulTangentEquiv_toMatrix_det
    (K := K) F hF hdet a x, one_smul]
  exact
    specialFormPreservingSmoothCoordinateDetFormPullback_toAlternatingMap_left_invariant
      (K := K) F hF hdet a x y z

/-- The basis-defined common smooth tangent determinant forms are invariant
under fixed-left tangent transport. -/
theorem specialFormPreservingSmoothTangentDetFormAt_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    (specialFormPreservingSmoothTangentDetFormAt
        F hF hdet (a * x)).compLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toLinearMap =
      specialFormPreservingSmoothTangentDetFormAt F hF hdet x := by
  rw [specialFormPreservingSmoothTangentDetFormAt_eq_continuous,
    specialFormPreservingSmoothTangentDetFormAt_eq_continuous]
  have h := congrArg ContinuousAlternatingMap.toAlternatingMap
    (specialFormPreservingSmoothContinuousDetFormAt_left_invariant
      (K := K) F hF hdet a x)
  exact h

/-- The fixed-left pullback of the common smooth tangent determinant form is
the normalized tangent Jacobian acting on the source determinant form. -/
theorem specialFormPreservingSmoothTangentDetFormAt_pullback_eq_jacobian_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (∞ : WithTop ℕ∞)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingSmoothIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
    (specialFormPreservingSmoothTangentDetFormAt
        F hF hdet (a * x)).compLinearMap
      (specialFormPreservingSmoothLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toLinearMap =
      (LinearMap.toMatrix
        (specialFormPreservingSmoothTangentFinBasis F hF hdet x)
        (specialFormPreservingSmoothTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingSmoothLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap).det •
        specialFormPreservingSmoothTangentDetFormAt F hF hdet x := by
  rw [specialFormPreservingSmoothLeftMulTangentEquiv_toMatrix_det,
    one_smul, specialFormPreservingSmoothTangentDetFormAt_left_invariant]

/-- Fixed-left tangent transport carries the normalized tangent basis at `x`
to the normalized tangent basis at `a * x`. -/
theorem specialFormPreservingContDiffTangentFinBasis_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    (specialFormPreservingContDiffTangentFinBasis F hF hdet x).map
        (specialFormPreservingContDiffLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearEquiv =
      specialFormPreservingContDiffTangentFinBasis F hF hdet (a * x) := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffChartedSpace FK hFK hdetK hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffIsManifold FK hFK hdetK hchar 1
  ext j
  apply (specialFormPreservingContDiffTangentModelEquiv
    FK hFK hdetK hchar (a * x)).injective
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦
      L (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F j))
    (specialFormPreservingContDiffLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [specialFormPreservingContDiffTangentFinBasis,
    Module.Basis.map_apply, ContinuousLinearMap.comp_apply,
    FK, hFK, hdetK, hchar] using hmodel

/-- Fixed-left tangent transport preserves the coordinates in the normalized
pointwise tangent bases. -/
theorem specialFormPreservingContDiffTangentFinBasis_repr_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    ∀ v : TangentSpace
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) x,
      (specialFormPreservingContDiffTangentFinBasis F hF hdet (a * x)).repr
          (specialFormPreservingContDiffLeftMulTangentEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
            a x v) =
        (specialFormPreservingContDiffTangentFinBasis F hF hdet x).repr v := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffChartedSpace FK hFK hdetK hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffIsManifold FK hFK hdetK hchar 1
  intro v
  simp only [specialFormPreservingContDiffTangentFinBasis,
    Module.Basis.map_repr, LinearEquiv.trans_apply]
  apply congrArg
    (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F).repr
  let ex := specialFormPreservingContDiffTangentModelEquiv
    FK hFK hdetK hchar x
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦ L (ex v))
    (specialFormPreservingContDiffLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [ContinuousLinearMap.comp_apply, FK, hFK, hdetK, hchar, ex] using hmodel

set_option maxRecDepth 2048 in
/-- The matrix of fixed-left tangent transport in the normalized pointwise
tangent bases is the identity. -/
theorem specialFormPreservingContDiffLeftMulTangentEquiv_toMatrix_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    LinearMap.toMatrix
        (specialFormPreservingContDiffTangentFinBasis F hF hdet x)
        (specialFormPreservingContDiffTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingContDiffLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap = 1 := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffChartedSpace FK hFK hdetK hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffIsManifold FK hFK hdetK hchar 1
  have hbasis := specialFormPreservingContDiffTangentFinBasis_left_invariant
    (K := K) F hF hdet a x
  ext i j
  rw [LinearMap.toMatrix_apply]
  have hj := congrArg (fun b ↦ b j) hbasis
  have hj' :
      (specialFormPreservingContDiffLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearEquiv
          (specialFormPreservingContDiffTangentFinBasis F hF hdet x j) =
        specialFormPreservingContDiffTangentFinBasis F hF hdet (a * x) j := by
    simpa only [Module.Basis.map_apply] using hj
  have hjcoord := congrArg
    (fun v ↦ (specialFormPreservingContDiffTangentFinBasis
      F hF hdet (a * x)).repr v i) hj'
  exact hjcoord.trans (by
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm])

/-- Fixed-left tangent transport has determinant one in the normalized
pointwise tangent bases. -/
theorem specialFormPreservingContDiffLeftMulTangentEquiv_toMatrix_det
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    (LinearMap.toMatrix
        (specialFormPreservingContDiffTangentFinBasis F hF hdet x)
        (specialFormPreservingContDiffTangentFinBasis F hF hdet (a * x))
        (specialFormPreservingContDiffLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toLinearMap).det = 1 := by
  rw [specialFormPreservingContDiffLeftMulTangentEquiv_toMatrix_eq_one
    (K := K) F hF hdet a x, Matrix.det_one]

@[simp]
theorem specialFormPreservingContDiffContinuousDetFormAt_toAlternatingMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    (specialFormPreservingContDiffContinuousDetFormAt F hF hdet x).toAlternatingMap =
      specialFormPreservingContDiffDetFormAt F hF hdet x :=
  rfl

/-- The continuous tangent form is the pullback of the fixed coordinate form
at every coordinate point. -/
theorem specialFormPreservingContDiffContinuousDetFormAt_eq_coordinate_pullback
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K)))
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ K))).toSubmodule) :
    (Matrix.skewAdjointScalarExtensionCoordinateDetForm (K := K) F y).compContinuousLinearMap
        (specialFormPreservingContDiffTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).toContinuousLinearMap =
      specialFormPreservingContDiffContinuousDetFormAt F hF hdet x :=
  rfl

/-- The continuous tangent form has volume one on the scalar-extended finite
basis lifted through the tangent-model equivalence. -/
theorem specialFormPreservingContDiffContinuousDetFormAt_apply_tangent_finBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingContDiffContinuousDetFormAt F hF hdet x
        (fun j ↦ (specialFormPreservingContDiffTangentModelEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          x).symm (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F j)) = 1 := by
  change Matrix.skewAdjointScalarExtensionContinuousDetForm (K := K) F
      (fun j ↦ (specialFormPreservingContDiffTangentModelEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x)
          ((specialFormPreservingContDiffTangentModelEquiv
            (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
            (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two x).symm
              (Matrix.skewAdjointScalarExtensionFinBasis (K := K) F j))) = 1
  simpa using Matrix.skewAdjointScalarExtensionCoordinateDetForm_apply_finBasis
    (K := K) F 0

/-- The pointwise determinant forms are invariant under the tangent transport
induced by fixed left multiplication. -/
theorem specialFormPreservingContDiffDetFormAt_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    (specialFormPreservingContDiffDetFormAt F hF hdet (a * x)).compLinearMap
        (specialFormPreservingContDiffLeftMulTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
          a x).toContinuousLinearMap.toLinearMap =
      specialFormPreservingContDiffDetFormAt F hF hdet x := by
  let FK := F.map (algebraMap ℚ K)
  let hFK : FK.IsSymm := isSymm_map_algebraMap (K := K) F hF
  let hdetK : FK.det ≠ 0 := det_map_algebraMap_ne_zero (K := K) F hdet
  let hchar := rclike_ringChar_ne_two (K := K)
  letI : ChartedSpace (skewAdjointMatricesLieSubalgebra FK).toSubmodule
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffChartedSpace FK hFK hdetK hchar 1
  letI : IsManifold
      (modelWithCornersSelf K
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule) 1
      (specialFormPreservingMatrixSubgroup FK) :=
    specialFormPreservingContDiffIsManifold FK hFK hdetK hchar 1
  rw [specialFormPreservingContDiffDetFormAt,
    specialFormPreservingContDiffDetFormAt,
    AlternatingMap.compLinearMap_assoc]
  apply congrArg (fun L =>
    (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap L)
  apply LinearMap.ext
  intro v
  let ex := specialFormPreservingContDiffTangentModelEquiv
    FK hFK hdetK hchar x
  have hmodel := congrArg
    (fun L : (skewAdjointMatricesLieSubalgebra FK).toSubmodule →L[K]
        (skewAdjointMatricesLieSubalgebra FK).toSubmodule ↦ L (ex v))
    (specialFormPreservingContDiffLeftMulTangentEquiv_model
      FK hFK hdetK hchar a x)
  simpa [ContinuousLinearMap.comp_apply, FK, hFK, hdetK, hchar, ex] using hmodel

/-- The continuous pointwise determinant forms are invariant under fixed-left
tangent transport. -/
theorem specialFormPreservingContDiffContinuousDetFormAt_left_invariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (a x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ K))) :
    letI : ChartedSpace
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffChartedSpace
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    letI : IsManifold
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule) 1
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) :=
      specialFormPreservingContDiffIsManifold
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1
    (specialFormPreservingContDiffContinuousDetFormAt
        F hF hdet (a * x)).compContinuousLinearMap
      (specialFormPreservingContDiffLeftMulTangentEquiv
        (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
        (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
        a x).toContinuousLinearMap =
      specialFormPreservingContDiffContinuousDetFormAt F hF hdet x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact specialFormPreservingContDiffDetFormAt_left_invariant
    F hF hdet a x

/-- The fixed rational skew-adjoint determinant form, scalar-extended to an
`RCLike` field and pulled back to the explicit order-one identity tangent
space. -/
noncomputable def specialFormPreservingContDiffIdentityDetForm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    @TangentSpace K _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _ _
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ K))).toSubmodule _
        (modelWithCornersSelf K
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ K))).toSubmodule)
        (specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K))) _
        (specialFormPreservingContDiffChartedSpace
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two 1)
        (1 : specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ K)))
      [⋀^Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))]→ₗ[K] K := by
  exact (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
    (specialFormPreservingContDiffIdentityTangentEquiv
      (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
      (det_map_algebraMap_ne_zero F hdet)
      rclike_ringChar_ne_two).toContinuousLinearMap.toLinearMap

/-- The pointwise determinant form at the identity is the fixed identity
tangent determinant form. -/
theorem specialFormPreservingContDiffDetFormAt_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    specialFormPreservingContDiffDetFormAt (K := K) F hF hdet 1 =
      specialFormPreservingContDiffIdentityDetForm F hF hdet := by
  rfl

/-- Evaluation on tangent lifts is exactly evaluation of the scalar-extended
skew-adjoint determinant form. -/
theorem specialFormPreservingContDiffIdentityDetForm_apply_tangent_lifts
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (v : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) →
      skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ K))) :
    specialFormPreservingContDiffIdentityDetForm F hF hdet
        (fun i ↦ (specialFormPreservingContDiffIdentityTangentEquiv
          (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
          (det_map_algebraMap_ne_zero F hdet)
          rclike_ringChar_ne_two).symm (v i)) =
      Matrix.skewAdjointScalarExtensionDetForm (K := K) F v := by
  rw [specialFormPreservingContDiffIdentityDetForm,
    AlternatingMap.compLinearMap_apply]
  apply AlternatingMap.congr_arg
  funext i
  exact (specialFormPreservingContDiffIdentityTangentEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet)
    rclike_ringChar_ne_two).apply_symm_apply (v i)

/-- The scalar-extended identity tangent determinant form is nonzero. -/
theorem specialFormPreservingContDiffIdentityDetForm_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    specialFormPreservingContDiffIdentityDetForm (K := K) F hF hdet ≠ 0 := by
  intro hzero
  let e := specialFormPreservingContDiffIdentityTangentEquiv
    (F.map (algebraMap ℚ K)) (isSymm_map_algebraMap F hF)
    (det_map_algebraMap_ne_zero F hdet) rclike_ringChar_ne_two
  have hform :
      (Matrix.skewAdjointScalarExtensionDetForm (K := K) F).compLinearMap
          e.toLinearEquiv.toLinearMap = 0 := by
    simpa [specialFormPreservingContDiffIdentityDetForm, e] using hzero
  have : Matrix.skewAdjointScalarExtensionDetForm (K := K) F = 0 :=
    (AlternatingMap.compLinearEquiv_eq_zero_iff
      (Matrix.skewAdjointScalarExtensionDetForm (K := K) F)
      e.toLinearEquiv).mp hform
  exact Matrix.skewAdjointScalarExtensionDetForm_ne_zero (K := K) F this

/-- The rationally normalized pointwise tangent determinant form is nonzero at
every point of the explicit order-one manifold. -/
theorem specialFormPreservingContDiffDetFormAt_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingContDiffDetFormAt F hF hdet x ≠ 0 := by
  intro hzero
  have hinv := specialFormPreservingContDiffDetFormAt_left_invariant
    (K := K) F hF hdet x 1
  have hinv' := hinv
  have hxone : x * 1 = x := mul_one x
  rw [hxone] at hinv'
  have hone : specialFormPreservingContDiffDetFormAt F hF hdet
      (1 : specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ K))) = 0 := by
    rw [hzero, AlternatingMap.zero_compLinearMap] at hinv'
    exact hinv'.symm
  apply specialFormPreservingContDiffIdentityDetForm_ne_zero
    (K := K) F hF hdet
  rw [← specialFormPreservingContDiffDetFormAt_one (K := K) F hF hdet]
  exact hone

/-- The continuous determinant form on every supplied tangent model is
nonzero. -/
theorem specialFormPreservingContDiffContinuousDetFormAt_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ K))) :
    specialFormPreservingContDiffContinuousDetFormAt F hF hdet x ≠ 0 := by
  intro hzero
  apply specialFormPreservingContDiffDetFormAt_ne_zero (K := K) F hF hdet x
  have := congrArg ContinuousAlternatingMap.toAlternatingMap hzero
  simpa using this

end RCLikeIdentityChartBridge

/-- The concrete finite-adelic special orthogonal subgroup attached to L. -/
def finiteAdelicSpecialOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicOrthogonalGroup :=
  specialFormPreservingMatrixSubgroup L.finiteAdelicFormMatrix

/-- The concrete carrier of SO(L)(A_f). -/
abbrev ConcreteFiniteAdelicSpecialOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.finiteAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    g ∈ L.finiteAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff L.finiteAdelicFormMatrix g

/-- The inclusion from SO(L)(A_f) to O(L)(A_f). -/
def finiteAdelicSpecialOrthogonalInclusion (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFiniteAdelicSpecialOrthogonalGroup →*
      L.ConcreteFiniteAdelicOrthogonalGroup :=
  L.finiteAdelicSpecialOrthogonalMatrixSubgroup.subtype

@[simp]
theorem finiteAdelicSpecialOrthogonalInclusion_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.finiteAdelicSpecialOrthogonalInclusion g = g.1 :=
  rfl

/-- The rational special orthogonal subgroup attached to L. -/
def rationalSpecialOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.rationalOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup L.rationalFormMatrix

@[simp]
theorem mem_rationalSpecialOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.rationalOrthogonalMatrixSubgroup) :
    g ∈ L.rationalSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff L.rationalFormMatrix g

/-- The rational diagonal embedding restricted to determinant-one matrices. -/
def rationalSpecialOrthogonalDiagonalHom (L : PositiveDefiniteIntegralLattice n) :
    L.rationalSpecialOrthogonalMatrixSubgroup →*
      L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  (L.rationalOrthogonalDiagonalHom.restrict
      L.rationalSpecialOrthogonalMatrixSubgroup).codRestrict
    L.finiteAdelicSpecialOrthogonalMatrixSubgroup (by
      intro g
      rw [L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff]
      have hdet : g.1.1.1.det = 1 :=
        (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
      change (L.rationalOrthogonalDiagonalHom g.1).1.1.det = 1
      rw [L.rationalOrthogonalDiagonalHom_apply_matrix,
        ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, hdet, map_one])

@[simp]
theorem rationalSpecialOrthogonalDiagonalHom_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalSpecialOrthogonalMatrixSubgroup) :
    (L.rationalSpecialOrthogonalDiagonalHom g).1 =
      L.rationalOrthogonalDiagonalHom g.1 :=
  rfl

/-- The diagonal rational SO(L)(Q) subgroup inside SO(L)(A_f). -/
def rationalSpecialOrthogonalDiagonalSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.rationalSpecialOrthogonalDiagonalHom.range

/-- The integral finite-adelic stabilizer inside SO(L)(A_f). -/
def finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.finiteLocalLatticeStabilizerSubgroup.comap
    L.finiteAdelicSpecialOrthogonalInclusion

@[simp]
theorem mem_finiteSpecialOrthogonalLatticeStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    g ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ↔
      (g.1 : L.ConcreteFiniteAdelicOrthogonalGroup) ∈
        L.finiteLocalLatticeStabilizerSubgroup :=
  Iff.rfl

/-! ## Proper compact-open topology and Haar normalization -/

/-- The finite-adelic special orthogonal subgroup is closed in the concrete
ordinary orthogonal group. -/
theorem isClosed_finiteAdelicSpecialOrthogonalMatrixSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsClosed (L.finiteAdelicSpecialOrthogonalMatrixSubgroup :
      Set L.ConcreteFiniteAdelicOrthogonalGroup) := by
  have hset :
      (L.finiteAdelicSpecialOrthogonalMatrixSubgroup :
        Set L.ConcreteFiniteAdelicOrthogonalGroup) =
        {g : L.ConcreteFiniteAdelicOrthogonalGroup | g.1.1.det = 1} := by
    ext g
    exact L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff g
  rw [hset]
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
    continuous_const

/-- The determinant-one finite local lattice stabilizer is open in the
finite-adelic special orthogonal group. -/
theorem isOpen_finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsOpen (L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
  exact L.isOpen_finiteLocalLatticeStabilizerSubgroup.preimage continuous_subtype_val

/-- The determinant-one finite local lattice stabilizer is compact. -/
theorem isCompact_finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsCompact (L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :
      Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
  have hembedding :=
    (L.isClosed_finiteAdelicSpecialOrthogonalMatrixSubgroup)
      |>.isClosedEmbedding_subtypeVal
  exact hembedding.isCompact_preimage
    L.isCompact_finiteLocalLatticeStabilizerSubgroup

/-- The proper finite local lattice stabilizer is measurable whenever open
sets are measurable. -/
theorem measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    [MeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup]
    [OpensMeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup] :
    MeasurableSet
      (L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :
        Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :=
  L.isOpen_finiteSpecialOrthogonalLatticeStabilizerSubgroup.measurableSet

/-- The compact-open proper finite local stabilizer, bundled as the
normalization set for Haar measure on `SO(V)(A_f)`. -/
def finiteSpecialOrthogonalLatticeStabilizerPositiveCompacts
    (L : PositiveDefiniteIntegralLattice n) :
    PositiveCompacts L.ConcreteFiniteAdelicSpecialOrthogonalGroup where
  carrier := L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
  isCompact' := L.isCompact_finiteSpecialOrthogonalLatticeStabilizerSubgroup
  interior_nonempty' := by
    rw [L.isOpen_finiteSpecialOrthogonalLatticeStabilizerSubgroup.interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩

/-- The compact neighborhood `H_f^+` supplies local compactness of the
concrete finite-adelic special orthogonal group. -/
instance concreteFiniteAdelicSpecialOrthogonalGroupLocallyCompactSpace
    (L : PositiveDefiniteIntegralLattice n) :
    LocallyCompactSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.finiteSpecialOrthogonalLatticeStabilizerPositiveCompacts
    |>.locallyCompactSpace_of_group

/-- Haar measure on the concrete finite-adelic special orthogonal group,
normalized so that `H_f^+` has mass one. -/
noncomputable def concreteFiniteAdelicSpecialOrthogonalHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  Measure.haarMeasure
    L.finiteSpecialOrthogonalLatticeStabilizerPositiveCompacts

instance concreteFiniteAdelicSpecialOrthogonalHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
  unfold concreteFiniteAdelicSpecialOrthogonalHaarMeasure
  infer_instance

/-- The normalized proper ambient Haar measure gives `H_f^+` mass one. -/
theorem concreteFiniteAdelicSpecialOrthogonalHaarMeasure_stabilizer
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup = 1 := by
  exact Measure.haarMeasure_self

/-- Haar measure on `H_f^+`, obtained by comapping normalized proper ambient
Haar measure along the subtype inclusion. -/
noncomputable def concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  Measure.comap
    (fun h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
      (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup))
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure

/-- The proper finite local stabilizer uses the inherited subtype measurable
space. -/
theorem concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
    (L : PositiveDefiniteIntegralLattice n) :
    (inferInstance :
      MeasurableSpace L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) =
      (@Subtype.instMeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup
        (fun x => x ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup)
        (inferInstance :
          MeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup)) :=
  rfl

/-- The subgroup Haar measure pushes forward to proper ambient Haar measure
restricted to `H_f^+`. -/
theorem concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_map_eq_restrict
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.map
        (fun h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
          (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup))
        L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure =
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure.restrict
        (L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :
          Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
  exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup

/-- The normalized Haar measure on `H_f^+` has total mass one. -/
theorem concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure Set.univ = 1 := by
  change (Measure.comap
    (fun h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup =>
      (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup))
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure) Set.univ = 1
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup]
  exact L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure_stabilizer

instance concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure := by
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
    L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup

/-! ## Proper compact-open measurable selectors -/

/-- The closed finite-adelic special orthogonal subgroup of the concrete
ordinary Polish group is Polish. -/
noncomputable instance concreteFiniteAdelicSpecialOrthogonalGroupPolishSpace
    (L : PositiveDefiniteIntegralLattice n) :
    PolishSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.isClosed_finiteAdelicSpecialOrthogonalMatrixSubgroup
    |>.isClosedEmbedding_subtypeVal.polishSpace

/-- The inherited Borel structure on the concrete finite-adelic special
orthogonal group is standard Borel. -/
noncomputable instance concreteFiniteAdelicSpecialOrthogonalGroupStandardBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    StandardBorelSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup where
  polish :=
    ⟨(inferInstance : TopologicalSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup),
      (inferInstance : BorelSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup),
      L.concreteFiniteAdelicSpecialOrthogonalGroupPolishSpace⟩

/-- The proper finite local lattice stabilizer, with its inherited subtype
measurable space, is standard Borel. -/
noncomputable instance concreteFiniteSpecialOrthogonalLatticeStabilizerStandardBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    StandardBorelSpace L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
  letI : StandardBorelSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    L.concreteFiniteAdelicSpecialOrthogonalGroupStandardBorelSpace
  exact L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup.standardBorel

/-! ## Proper rational left quotient measure -/

/-- The proper rational left quotient
`SO(V)(ℚ) \ SO(V)(𝔸_f)` attached to `L`. -/
abbrev ConcreteProperRationalLeftQuotient (L : PositiveDefiniteIntegralLattice n) :=
  leftCosetSet L.rationalSpecialOrthogonalDiagonalSubgroup

/-- The canonical projection to the proper rational left quotient. -/
def concreteProperRationalLeftQuotientMap (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFiniteAdelicSpecialOrthogonalGroup →
      L.ConcreteProperRationalLeftQuotient :=
  leftCosetMap L.rationalSpecialOrthogonalDiagonalSubgroup

/-- The proper rational quotient carries the measurable structure generated
by the quotient map from the inherited ambient measurable space. -/
instance concreteProperRationalLeftQuotientMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteProperRationalLeftQuotient :=
  MeasurableSpace.map L.concreteProperRationalLeftQuotientMap
    (inferInstance :
      MeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup)

theorem concreteProperRationalLeftQuotientMeasurableSpace_eq_map
    (L : PositiveDefiniteIntegralLattice n) :
    (inferInstance : MeasurableSpace L.ConcreteProperRationalLeftQuotient) =
      MeasurableSpace.map L.concreteProperRationalLeftQuotientMap
        (inferInstance :
          MeasurableSpace L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :=
  rfl

/-- The canonical proper rational quotient map is measurable. -/
theorem concreteProperRationalLeftQuotientMap_measurable
    (L : PositiveDefiniteIntegralLattice n) :
    Measurable L.concreteProperRationalLeftQuotientMap := by
  exact leftCosetMap_measurable_map L.rationalSpecialOrthogonalDiagonalSubgroup

/-- The proper rational quotient measure obtained by restricting normalized
ambient Haar measure to a domain candidate and pushing it to the quotient. -/
noncomputable def concreteProperRationalLeftQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Measure L.ConcreteProperRationalLeftQuotient :=
  leftQuotientFundamentalDomainMeasure
    L.rationalSpecialOrthogonalDiagonalSubgroup
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure F

theorem concreteProperRationalLeftQuotientMeasure_eq_map_restrict
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperRationalLeftQuotientMeasure F =
      Measure.map L.concreteProperRationalLeftQuotientMap
        (L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure.restrict F) :=
  rfl

theorem concreteProperRationalLeftQuotientMeasure_apply
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    {A : Set L.ConcreteProperRationalLeftQuotient} (hA : MeasurableSet A) :
    L.concreteProperRationalLeftQuotientMeasure F A =
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
        (F ∩ L.concreteProperRationalLeftQuotientMap ⁻¹' A) := by
  exact leftQuotientFundamentalDomainMeasure_apply_map_mspace
    L.concreteProperRationalLeftQuotientMeasurableSpace_eq_map hA

/-- The total proper quotient mass is the ambient Haar mass of its domain. -/
theorem concreteProperRationalLeftQuotientMeasure_univ
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperRationalLeftQuotientMeasure F Set.univ =
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure F := by
  exact leftQuotientFundamentalDomainMeasure_univ_map_mspace
    L.concreteProperRationalLeftQuotientMeasurableSpace_eq_map

/-- Real-valued total-mass form of the proper quotient normalization. -/
theorem concreteProperRationalLeftQuotientMeasure_univ_toReal
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    (L.concreteProperRationalLeftQuotientMeasure F Set.univ).toReal =
      (L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure F).toReal := by
  exact leftQuotientFundamentalDomainMeasure_univ_toReal_map_mspace
    L.concreteProperRationalLeftQuotientMeasurableSpace_eq_map

/-- The real volume of a proper rational quotient domain candidate. -/
noncomputable def concreteProperFiniteAdelicQuotientVolume
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) : ℝ :=
  (L.concreteProperRationalLeftQuotientMeasure F Set.univ).toReal

/-- Proper quotient volume is the real ambient Haar mass of its domain. -/
theorem concreteProperFiniteAdelicQuotientVolume_eq_ambient
    (L : PositiveDefiniteIntegralLattice n)
    (F : Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperFiniteAdelicQuotientVolume F =
      (L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure F).toReal := by
  simpa [concreteProperFiniteAdelicQuotientVolume] using
    L.concreteProperRationalLeftQuotientMeasure_univ_toReal F

/-- The ordinary finite-adelic representative assembled from oriented local
comparisons has determinant one. -/
theorem concreteFiniteAdelicRepresentativeOfRationalComparison_det_eq_one
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)))
    (hdet : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      (Pv * Uv).1.det = 1) :
    (L.concreteFiniteAdelicRepresentativeOfRationalComparison
      M P hP U hU).1.1.det = 1 := by
  rw [L.concreteFiniteAdelicRepresentativeOfRationalComparison_matrix]
  ext v
  let ev : RationalFiniteAdele →+* v.adicCompletion ℚ :=
    RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum ℤ ↦ w.adicCompletion ℚ) v
  let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
  let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
    Matrix.GeneralLinearGroup.map
      (v.adicCompletionIntegers ℚ).subtype (U v)
  have hPmap :
      (P.1.map (algebraMap ℚ RationalFiniteAdele)).map ev = Pv.1 := by
    ext i j
    simp [ev, Pv]
  have hUmap : (localIntegralMatrixUnitsFiniteAdeleGL U).1.map ev = Uv.1 := by
    have hmap := localIntegralMatrixUnitsFiniteAdeleGL_map_eval U v
    exact congrArg Units.val hmap
  change ev ((P.1.map (algebraMap ℚ RationalFiniteAdele) *
    (localIntegralMatrixUnitsFiniteAdeleGL U).1).det) = ev 1
  rw [map_one]
  calc
    ev ((P.1.map (algebraMap ℚ RationalFiniteAdele) *
        (localIntegralMatrixUnitsFiniteAdeleGL U).1).det) =
        ((P.1.map (algebraMap ℚ RationalFiniteAdele) *
          (localIntegralMatrixUnitsFiniteAdeleGL U).1).map ev).det :=
      RingHom.map_det ev _
    _ = (Pv.1 * Uv.1).det := by
      rw [Matrix.map_mul, hPmap, hUmap]
    _ = 1 := hdet v

/-- Assemble oriented local comparisons into an element of `SO(L)(A_f)`. -/
noncomputable def concreteFiniteAdelicSpecialOrthogonalRepresentativeOfRationalComparison
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)))
    (hdet : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      (Pv * Uv).1.det = 1) :
    L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  ⟨L.concreteFiniteAdelicRepresentativeOfRationalComparison M P hP U hU,
    (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff _).2
      (L.concreteFiniteAdelicRepresentativeOfRationalComparison_det_eq_one
        M P hP U hU hdet)⟩

@[simp]
theorem concreteFiniteAdelicSpecialOrthogonalRepresentativeOfRationalComparison_matrix
    (L M : PositiveDefiniteIntegralLattice n)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hU : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)))
    (hdet : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (U v)
      (Pv * Uv).1.det = 1) :
    (L.concreteFiniteAdelicSpecialOrthogonalRepresentativeOfRationalComparison
      M P hP U hU hdet).1.1.1 =
      P.1.map (algebraMap ℚ RationalFiniteAdele) *
        (localIntegralMatrixUnitsFiniteAdeleGL U).1 := by
  rfl

/-- The concrete proper double-coset set:
SO(L)(Q) \ SO(L)(A_f) / SO(L)(A_f; L). -/
abbrev ConcreteProperRationalDoubleCosetSet (L : PositiveDefiniteIntegralLattice n) :=
  leftRightDoubleCosetSet L.rationalSpecialOrthogonalDiagonalSubgroup
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup

/-! ## Orientation-normalized attached lattices -/

/-- Correct the arbitrary chosen basis of an attached lattice to have positive
determinant in the ambient rational coordinates. -/
noncomputable def concreteAttachedOrientationCorrectionMatrix
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] : Matrix (Fin n) (Fin n) ℤ :=
  if 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g).det then
    1
  else
    orientationReversingBasisChangeMatrix

lemma concreteAttachedOrientationCorrectionMatrix_isUnit
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    IsUnit (L.concreteAttachedOrientationCorrectionMatrix g) := by
  rw [concreteAttachedOrientationCorrectionMatrix]
  split_ifs
  · exact isUnit_one
  · exact orientationReversingBasisChangeMatrix_isUnit

lemma concreteAttachedOrientationCorrectionMatrix_det
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    (L.concreteAttachedOrientationCorrectionMatrix g).det =
      if 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g).det then
        1
      else
        -1 := by
  rw [concreteAttachedOrientationCorrectionMatrix]
  split_ifs
  · simp
  · exact orientationReversingBasisChangeMatrix_det

lemma concreteAttachedOrientationCorrectionMatrix_mul_self
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    L.concreteAttachedOrientationCorrectionMatrix g *
        L.concreteAttachedOrientationCorrectionMatrix g = 1 := by
  rw [concreteAttachedOrientationCorrectionMatrix]
  split_ifs
  · simp
  · rw [orientationReversingBasisChangeMatrix,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = Classical.arbitrary (Fin n)
    · simp [hi]
    · simp [hi]

lemma concreteAttachedOrientationCorrectionMatrix_transpose
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    (L.concreteAttachedOrientationCorrectionMatrix g)ᵀ =
      L.concreteAttachedOrientationCorrectionMatrix g := by
  rw [concreteAttachedOrientationCorrectionMatrix]
  split_ifs
  · simp
  · ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [orientationReversingBasisChangeMatrix, Matrix.transpose_apply,
        hij, Ne.symm hij]

/-- The corrected attached basis has positive determinant in ambient rational
coordinates. -/
lemma concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g *
      (L.concreteAttachedOrientationCorrectionMatrix g).map
        (Int.cast : ℤ → ℚ)).det := by
  let B := L.concreteAttachedRationalLatticeBasisMatrixRat g
  have hB_ne : B.det ≠ 0 := by
    simpa [B] using
      L.concreteAttachedRationalLatticeBasisMatrixRat_det_ne_zero g
  rw [Matrix.det_mul, ← Int.cast_det,
    L.concreteAttachedOrientationCorrectionMatrix_det]
  by_cases hB_pos : 0 < B.det
  · rw [if_pos hB_pos]
    norm_num
    exact hB_pos
  · rw [if_neg hB_pos]
    norm_num
    exact lt_of_le_of_ne (le_of_not_gt hB_pos) hB_ne

/-- The attached integral lattice rebased so that its chosen ambient rational
basis has positive determinant. -/
noncomputable def concreteOrientedAttachedIntegralLattice
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] : PositiveDefiniteIntegralLattice n :=
  if 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g).det then
    L.concreteAttachedIntegralLattice g
  else
    orientationReversingBasisChangeLattice
      (L.concreteAttachedIntegralLattice g)

lemma concreteOrientedAttachedIntegralLattice_pairingMatrix
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    (L.concreteOrientedAttachedIntegralLattice g).pairingMatrix =
      (L.concreteAttachedOrientationCorrectionMatrix g)ᵀ *
        (L.concreteAttachedIntegralLattice g).pairingMatrix *
          L.concreteAttachedOrientationCorrectionMatrix g := by
  rw [concreteOrientedAttachedIntegralLattice,
    concreteAttachedOrientationCorrectionMatrix]
  split_ifs
  · simp
  · rfl

lemma concreteOrientedAttachedIntegralLattice_isSameGenus
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup)
    [Nonempty (Fin n)] :
    L.IsSameGenus (L.concreteOrientedAttachedIntegralLattice g) := by
  rw [concreteOrientedAttachedIntegralLattice]
  split_ifs
  · exact L.concreteAttachedIntegralLattice_isSameGenus g
  · apply isSameGenus_trans
      (L.concreteAttachedIntegralLattice_isSameGenus g)
    exact isSameGenus_of_isGlobalIsometry
      (isGlobalIsometry_symm
        (orientationReversingBasisChangeLattice_isGlobalIsometry
          (L.concreteAttachedIntegralLattice g)))

/-- Determinant-one rational and integral translations induce a proper
isometry between the orientation-normalized attached lattices. -/
theorem concreteOrientedAttachedIntegralLattice_rationalSpecial_mul_stabilizer_isProperGlobalIsometry
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (q : L.rationalSpecialOrthogonalMatrixSubgroup)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    (L.concreteOrientedAttachedIntegralLattice
      (L.rationalOrthogonalDiagonalHom q.1 * g.1 * h.1.1)).IsProperGlobalIsometry
      (L.concreteOrientedAttachedIntegralLattice g.1) := by
  classical
  let hO : L.finiteLocalLatticeStabilizerSubgroup := ⟨h.1.1, h.2⟩
  let g' : L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.rationalOrthogonalDiagonalHom q.1 * g.1 * hO
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let C' := L.concreteAttachedOrientationCorrectionMatrix g'
  rcases
      L.exists_concreteAttachedIntegralLattice_rational_mul_stabilizer_basisChange
        q.1 g.1 hO with ⟨T, hTunit, hchange, hform⟩
  let U : Matrix (Fin n) (Fin n) ℤ := C * T * C'
  have hCunit : IsUnit C := by
    exact L.concreteAttachedOrientationCorrectionMatrix_isUnit g.1
  have hC'unit : IsUnit C' := by
    exact L.concreteAttachedOrientationCorrectionMatrix_isUnit g'
  have hUunit : IsUnit U := hCunit.mul hTunit |>.mul hC'unit
  have hCself : C * C = 1 := by
    exact L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hC'self : C' * C' = 1 := by
    exact L.concreteAttachedOrientationCorrectionMatrix_mul_self g'
  have hCtrans : Cᵀ = C := by
    exact L.concreteAttachedOrientationCorrectionMatrix_transpose g.1
  have hC'trans : C'ᵀ = C' := by
    exact L.concreteAttachedOrientationCorrectionMatrix_transpose g'
  have hchange_oriented :
      q.1.1.1 *
          (L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
            C.map (Int.cast : ℤ → ℚ)) *
          U.map (Int.cast : ℤ → ℚ) =
        L.concreteAttachedRationalLatticeBasisMatrixRat g' *
          C'.map (Int.cast : ℤ → ℚ) := by
    have hCselfQ := congrArg
      (fun A : Matrix (Fin n) (Fin n) ℤ =>
        A.map (Int.castRingHom ℚ)) hCself
    have hCselfQ' :
        C.map (Int.cast : ℤ → ℚ) * C.map (Int.cast : ℤ → ℚ) = 1 := by
      simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using
        hCselfQ
    dsimp [U]
    change q.1.1.1 *
          (L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
            C.map (Int.castRingHom ℚ)) *
          (C * T * C').map (Int.castRingHom ℚ) =
        L.concreteAttachedRationalLatticeBasisMatrixRat g' *
          C'.map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, Matrix.map_mul]
    calc
      q.1.1.1 *
            (L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
              C.map (Int.cast : ℤ → ℚ)) *
            ((C.map (Int.cast : ℤ → ℚ) *
              T.map (Int.cast : ℤ → ℚ)) *
              C'.map (Int.cast : ℤ → ℚ)) =
          (q.1.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g.1) *
            (C.map (Int.cast : ℤ → ℚ) *
              C.map (Int.cast : ℤ → ℚ)) *
            T.map (Int.cast : ℤ → ℚ) *
            C'.map (Int.cast : ℤ → ℚ) := by noncomm_ring
      _ = (q.1.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
            T.map (Int.cast : ℤ → ℚ)) *
            C'.map (Int.cast : ℤ → ℚ) := by rw [hCselfQ']; simp
      _ = L.concreteAttachedRationalLatticeBasisMatrixRat g' *
            C'.map (Int.cast : ℤ → ℚ) := by rw [hchange]
  have hUdet : U.det = 1 := by
    have hUdet_unit : IsUnit U.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hUunit
    rcases Int.isUnit_iff.mp hUdet_unit with hUdet | hUdet
    · exact hUdet
    · have hleft :=
        L.concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos
          g.1
      have hright :=
        L.concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos
          g'
      have hdetEq := congrArg Matrix.det hchange_oriented
      have hqdet : q.1.1.1.det = 1 :=
        (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff q.1).mp q.2
      rw [Matrix.det_mul, Matrix.det_mul, hqdet, one_mul,
        ← Int.cast_det, hUdet] at hdetEq
      norm_num at hdetEq
      have hleft' :
          0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g.1).det *
            (C.map (Int.cast : ℤ → ℚ)).det := by
        rw [← Matrix.det_mul]
        exact hleft
      have hright' :
          0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g').det *
            (C'.map (Int.cast : ℤ → ℚ)).det := by
        rw [← Matrix.det_mul]
        exact hright
      nlinarith
  refine ⟨U, hUunit, hUdet, ?_⟩
  rw [L.concreteOrientedAttachedIntegralLattice_pairingMatrix,
    L.concreteOrientedAttachedIntegralLattice_pairingMatrix]
  change Uᵀ * (Cᵀ * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) *
      U = C'ᵀ * (L.concreteAttachedIntegralLattice g').pairingMatrix * C'
  rw [hCtrans, hC'trans]
  dsimp [U]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hCtrans, hC'trans]
  calc
    (C' * (Tᵀ * C)) *
          (C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) *
          (C * T * C') =
        C' * Tᵀ * (C * C) *
          (L.concreteAttachedIntegralLattice g.1).pairingMatrix *
          (C * C) * T * C' := by noncomm_ring
    _ = C' * (Tᵀ * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * T) *
          C' := by
      rw [hCself]
      simp
      noncomm_ring
    _ = C' * (L.concreteAttachedIntegralLattice g').pairingMatrix * C' := by
      rw [hform]

/-- Proper-related representatives have the same proper global class after
orientation normalization. -/
theorem concreteProperRelated_orientedAttached_properGlobalIsometryClass_eq
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g g' : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (hrel : IsLeftRightDoubleCosetRelated
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup g g') :
    (L.concreteOrientedAttachedIntegralLattice g.1).properGlobalIsometryClass =
      (L.concreteOrientedAttachedIntegralLattice g'.1).properGlobalIsometryClass := by
  rcases hrel with ⟨gamma, h, rfl⟩
  rcases gamma.property with ⟨q, hq⟩
  have hiso :=
    L.concreteOrientedAttachedIntegralLattice_rationalSpecial_mul_stabilizer_isProperGlobalIsometry
      q g h
  have hclass :=
    (properGlobalIsometryClass_eq_of_isProperGlobalIsometry hiso).symm
  rw [← hq]
  exact hclass

/-- The proper finite-adelic double quotient maps to the proper genus using
the orientation-normalized attached lattice of a chosen representative. -/
noncomputable def concreteProperDoubleCosetToProperGenus
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    L.ConcreteProperRationalDoubleCosetSet → L.properGenus :=
  fun C =>
    let g := Quot.out C
    let M := L.concreteOrientedAttachedIntegralLattice g.1
    ⟨M.properGlobalIsometryClass,
      ⟨M, L.concreteOrientedAttachedIntegralLattice_isSameGenus g.1, rfl⟩⟩

/-- Evaluation of the proper-genus map on an explicit proper double-coset
representative. -/
theorem concreteProperDoubleCosetToProperGenus_mk
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperDoubleCosetToProperGenus
        (Quot.mk (leftRightDoubleCosetSetoid
          L.rationalSpecialOrthogonalDiagonalSubgroup
          L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) g) =
      ⟨(L.concreteOrientedAttachedIntegralLattice g.1).properGlobalIsometryClass,
        ⟨L.concreteOrientedAttachedIntegralLattice g.1,
          L.concreteOrientedAttachedIntegralLattice_isSameGenus g.1, rfl⟩⟩ := by
  apply Subtype.ext
  change properGlobalIsometryClass (L.concreteOrientedAttachedIntegralLattice
      (Quot.out (Quot.mk (leftRightDoubleCosetSetoid
        L.rationalSpecialOrthogonalDiagonalSubgroup
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) g)).1) = _
  apply L.concreteProperRelated_orientedAttached_properGlobalIsometryClass_eq
  exact Quotient.exact (Quot.out_eq
    (Quot.mk (leftRightDoubleCosetSetoid
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) g))

/-! ## Injectivity -/

/-- A proper isometry between orientation-normalized attached lattices gives
an explicit determinant-one rational comparison between their original
attached bases. -/
theorem exists_rationalSpecialOrthogonal_of_orientedAttached_properGlobalIsometry
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g g' : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (hiso : (L.concreteOrientedAttachedIntegralLattice g.1).IsProperGlobalIsometry
      (L.concreteOrientedAttachedIntegralLattice g'.1)) :
    ∃ q : L.rationalSpecialOrthogonalMatrixSubgroup,
      ∃ T : Matrix (Fin n) (Fin n) ℤ,
        IsUnit T ∧
        q.1.1.1 * L.concreteAttachedRationalLatticeBasisMatrixRat g.1 =
          L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
            T.map (Int.castRingHom ℚ) := by
  classical
  rcases hiso with ⟨U, hUunit, hUdet, hUform⟩
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let C' := L.concreteAttachedOrientationCorrectionMatrix g'.1
  let T : Matrix (Fin n) (Fin n) ℤ := C' * U * C
  have hCunit : IsUnit C :=
    L.concreteAttachedOrientationCorrectionMatrix_isUnit g.1
  have hC'unit : IsUnit C' :=
    L.concreteAttachedOrientationCorrectionMatrix_isUnit g'.1
  have hTunit : IsUnit T := (hC'unit.mul hUunit).mul hCunit
  have hCself : C * C = 1 :=
    L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hCtrans : Cᵀ = C :=
    L.concreteAttachedOrientationCorrectionMatrix_transpose g.1
  have hC'trans : C'ᵀ = C' :=
    L.concreteAttachedOrientationCorrectionMatrix_transpose g'.1
  rw [L.concreteOrientedAttachedIntegralLattice_pairingMatrix,
    L.concreteOrientedAttachedIntegralLattice_pairingMatrix] at hUform
  change Uᵀ *
      (C'ᵀ * (L.concreteAttachedIntegralLattice g'.1).pairingMatrix * C') * U =
    Cᵀ * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C at hUform
  rw [hCtrans, hC'trans] at hUform
  have hTform :
      Tᵀ * (L.concreteAttachedIntegralLattice g'.1).pairingMatrix * T =
        (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
    dsimp [T]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hCtrans, hC'trans]
    calc
      (C * (Uᵀ * C')) *
            (L.concreteAttachedIntegralLattice g'.1).pairingMatrix *
            (C' * U * C) =
          C *
            (Uᵀ * (C' *
              (L.concreteAttachedIntegralLattice g'.1).pairingMatrix * C') * U) *
            C := by noncomm_ring
      _ = C * (C *
            (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * C := by
        rw [hUform]
      _ = (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
        calc
          C * (C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * C =
              (C * C) * (L.concreteAttachedIntegralLattice g.1).pairingMatrix *
                (C * C) := by noncomm_ring
          _ = (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
            rw [hCself]
            simp
  obtain ⟨q, hbasis⟩ :=
    L.exists_rationalOrthogonal_of_attached_isometryMatrix
      g.1 g'.1 T hTunit hTform
  have hCselfQ :
      C.map (Int.castRingHom ℚ) * C.map (Int.castRingHom ℚ) = 1 := by
    calc
      C.map (Int.castRingHom ℚ) * C.map (Int.castRingHom ℚ) =
          (C * C).map (Int.castRingHom ℚ) := by rw [Matrix.map_mul]
      _ = 1 := by
        rw [hCself]
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  have horientedBasis :
      q.1.1 *
          (L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
            C.map (Int.castRingHom ℚ)) =
        (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
            C'.map (Int.castRingHom ℚ)) *
          U.map (Int.castRingHom ℚ) := by
    calc
      q.1.1 *
            (L.concreteAttachedRationalLatticeBasisMatrixRat g.1 *
              C.map (Int.castRingHom ℚ)) =
          (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
              T.map (Int.castRingHom ℚ)) *
            C.map (Int.castRingHom ℚ) := by rw [← Matrix.mul_assoc, hbasis]
      _ = (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
              C'.map (Int.castRingHom ℚ)) *
            U.map (Int.castRingHom ℚ) := by
        rw [show T = C' * U * C by rfl, Matrix.map_mul, Matrix.map_mul]
        calc
          (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
                ((C'.map (Int.castRingHom ℚ) *
                    U.map (Int.castRingHom ℚ)) *
                  C.map (Int.castRingHom ℚ))) *
              C.map (Int.castRingHom ℚ) =
            (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
                C'.map (Int.castRingHom ℚ)) *
              U.map (Int.castRingHom ℚ) *
              (C.map (Int.castRingHom ℚ) *
                C.map (Int.castRingHom ℚ)) := by noncomm_ring
          _ = (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1 *
                C'.map (Int.castRingHom ℚ)) *
              U.map (Int.castRingHom ℚ) := by rw [hCselfQ, Matrix.mul_one]
  have hdetEq := congrArg Matrix.det horientedBasis
  have hUdetQ : (U.map (Int.castRingHom ℚ)).det = 1 := by
    simpa [hUdet] using
      (RingHom.map_det (Int.castRingHom ℚ) U).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    hUdetQ, mul_one] at hdetEq
  have hgpos :=
    L.concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos
      g.1
  have hg'pos :=
    L.concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos
      g'.1
  rw [Matrix.det_mul] at hgpos hg'pos
  change 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g.1).det *
      (C.map (Int.castRingHom ℚ)).det at hgpos
  change 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g'.1).det *
      (C'.map (Int.castRingHom ℚ)).det at hg'pos
  have hqdet_pos : 0 < q.1.1.det := by
    nlinarith
  have hqform := q.2
  have hqformDet := congrArg Matrix.det hqform
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hqformDet
  have hqdet_sq : q.1.1.det * q.1.1.det = 1 := by
    apply mul_right_cancel₀ L.rationalFormMatrix_det_ne_zero
    calc
      (q.1.1.det * q.1.1.det) * L.rationalFormMatrix.det =
          q.1.1.det * L.rationalFormMatrix.det * q.1.1.det := by ring
      _ = L.rationalFormMatrix.det := hqformDet
      _ = 1 * L.rationalFormMatrix.det := by ring
  have hqdet : q.1.1.det = 1 := by nlinarith
  let qSO : L.rationalSpecialOrthogonalMatrixSubgroup :=
    ⟨q, (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff q).2 hqdet⟩
  exact ⟨qSO, T, hTunit, hbasis⟩

/-- Equal proper classes of oriented attached lattices recover the defining
proper left-right double-coset relation. -/
theorem concreteOrientedAttached_properGlobalIsometryClass_eq_implies_related
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g g' : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (hclass :
      (L.concreteOrientedAttachedIntegralLattice g.1).properGlobalIsometryClass =
        (L.concreteOrientedAttachedIntegralLattice g'.1).properGlobalIsometryClass) :
    IsLeftRightDoubleCosetRelated
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup g g' := by
  have hiso := isProperGlobalIsometry_of_properGlobalIsometryClass_eq hclass
  obtain ⟨q, T, hTunit, hbasis⟩ :=
    L.exists_rationalSpecialOrthogonal_of_orientedAttached_properGlobalIsometry
      g g' hiso
  let gamma : L.rationalSpecialOrthogonalDiagonalSubgroup :=
    ⟨L.rationalSpecialOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩
  let hval : L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    g⁻¹ * (L.rationalSpecialOrthogonalDiagonalHom q)⁻¹ * g'
  have hhval : hval ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
    exact L.concreteAttachedResidual_mem_finiteLocalLatticeStabilizerSubgroup
      g.1 g'.1 q.1 T hTunit hbasis
  let h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := ⟨hval, hhval⟩
  refine ⟨gamma, h, ?_⟩
  simp [gamma, h, hval, mul_assoc]

/-- The orientation-normalized attached-lattice map is injective on the
proper rational double quotient. -/
theorem concreteProperDoubleCosetToProperGenus_injective
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    Function.Injective L.concreteProperDoubleCosetToProperGenus := by
  intro C D hCD
  rw [← Quot.out_eq C, ← Quot.out_eq D]
  exact Quotient.sound
    (L.concreteOrientedAttached_properGlobalIsometryClass_eq_implies_related
      (Quot.out C) (Quot.out D) (Subtype.ext_iff.mp hCD))

/-! ## Surjectivity -/

/-- Every positive-definite rational quadratic space of positive dimension
has a rational orthogonal reflection of determinant `-1`. -/
theorem exists_rationalOrthogonalMatrix_det_neg_one
    (M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    ∃ R : GL (Fin n) ℚ,
      R.1ᵀ * M.rationalFormMatrix * R.1 = M.rationalFormMatrix ∧
      R.1.det = -1 := by
  classical
  let i : Fin n := Classical.arbitrary (Fin n)
  let z : Fin n → ℤ := Pi.single i 1
  let w : Fin n → ℚ := intVectorToRatLinear n z
  have hz : z ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [z] at hi
  have hqz : M.quadForm z ≠ 0 := ne_of_gt (M.quadForm_pos hz)
  have hw : gramQuadraticValue M.rationalFormMatrix w ≠ 0 := by
    have hcast :
        gramQuadraticValue M.rationalFormMatrix w = (M.quadForm z : ℚ) := by
      simp [gramQuadraticValue, rationalFormMatrix, w, z,
        PositiveDefiniteIntegralLattice.quadForm_eq_dotProduct, Matrix.mulVec, dotProduct]
    rw [hcast]
    exact_mod_cast hqz
  let Rmat := gramReflectionMatrix M.rationalFormMatrix w
  have hRdet : Rmat.det = -1 := by
    dsimp [Rmat]
    rw [gramReflectionMatrix, sub_eq_add_neg,
      show -((2 / gramQuadraticValue M.rationalFormMatrix w) •
          Matrix.vecMulVec w (M.rationalFormMatrix *ᵥ w)) =
          Matrix.vecMulVec
            (-(2 / gramQuadraticValue M.rationalFormMatrix w) • w)
            (M.rationalFormMatrix *ᵥ w) by
        ext a b
        simp [Matrix.vecMulVec_apply]
        ring]
    rw [Matrix.vecMulVec_eq Unit,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
    have hsum :
        (∑ x, (M.rationalFormMatrix *ᵥ w) x *
          (-(2 / gramQuadraticValue M.rationalFormMatrix w) * w x)) =
        -(2 / gramQuadraticValue M.rationalFormMatrix w) *
          ∑ x, w x * (M.rationalFormMatrix *ᵥ w) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    rw [hsum]
    change 1 + -(2 / gramQuadraticValue M.rationalFormMatrix w) *
        gramQuadraticValue M.rationalFormMatrix w = -1
    field_simp [hw]
    norm_num
  let R : GL (Fin n) ℚ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Rmat (by rw [hRdet]; norm_num)
  refine ⟨R, ?_, ?_⟩
  · exact gramReflectionMatrix_preserves M.rationalFormMatrix
      (M.form_symm.map _) w hw
  · exact hRdet

/-- A rational comparison into a positive-definite target can be chosen with
positive determinant by composing with a rational target reflection. -/
theorem exists_positive_det_rationalComparison_of_isSameGenus
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (h : L.IsSameGenus M) :
    ∃ P : GL (Fin n) ℚ,
      P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix ∧
      0 < P.1.det := by
  obtain ⟨P, hP⟩ := L.exists_rationalComparison_of_isSameGenus M h
  by_cases hPpos : 0 < P.1.det
  · exact ⟨P, hP, hPpos⟩
  · obtain ⟨R, hRform, hRdet⟩ :=
      M.exists_rationalOrthogonalMatrix_det_neg_one
    refine ⟨P * R, ?_, ?_⟩
    · change (P.1 * R.1)ᵀ * L.rationalFormMatrix * (P.1 * R.1) = _
      rw [Matrix.transpose_mul]
      calc
        R.1ᵀ * P.1ᵀ * L.rationalFormMatrix * (P.1 * R.1) =
            R.1ᵀ * (P.1ᵀ * L.rationalFormMatrix * P.1) * R.1 := by
              noncomm_ring
        _ = R.1ᵀ * M.rationalFormMatrix * R.1 := by rw [hP]
        _ = M.rationalFormMatrix := hRform
    · change 0 < (P.1 * R.1).det
      rw [Matrix.det_mul, hRdet]
      have hPdet : P.1.det ≠ 0 := by
        exact isUnit_iff_ne_zero.mp
          ((Matrix.isUnit_iff_isUnit_det P.1).mp P.isUnit)
      have hPneg : P.1.det < 0 :=
        lt_of_le_of_ne (le_of_not_gt hPpos) hPdet
      nlinarith

/-- With a positive-determinant rational comparison, the orientation-corrected
attached lattice of `diag(P) U` is properly globally isometric to the target. -/
theorem concreteOrientedAttachedIntegralLattice_representativeOfRationalComparison_isProperGlobalIsometry
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (hPpos : 0 < P.1.det)
    (Ulocal : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      GL (Fin n) (v.adicCompletionIntegers ℚ))
    (hUlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
        Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype (Ulocal v)
      Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
        L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) :
    (L.concreteOrientedAttachedIntegralLattice
      (L.concreteFiniteAdelicRepresentativeOfRationalComparison
        M P hP Ulocal hUlocal)).IsProperGlobalIsometry M := by
  classical
  let g := L.concreteFiniteAdelicRepresentativeOfRationalComparison
    M P hP Ulocal hUlocal
  obtain ⟨T, hTunit, hchange, hTform⟩ :=
    L.exists_concreteAttachedIntegralLattice_representativeOfRationalComparison_basisChange
      M P hP Ulocal hUlocal
  let C := L.concreteAttachedOrientationCorrectionMatrix g
  let V : Matrix (Fin n) (Fin n) ℤ := T * C
  have hCunit : IsUnit C :=
    L.concreteAttachedOrientationCorrectionMatrix_isUnit g
  have hVunit : IsUnit V := hTunit.mul hCunit
  have hVdet : V.det = 1 := by
    have hVdet_unit : IsUnit V.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hVunit
    rcases Int.isUnit_iff.mp hVdet_unit with hVdet | hVdet
    · exact hVdet
    · have hchange_oriented :
          P.1 * V.map (Int.castRingHom ℚ) =
            L.concreteAttachedRationalLatticeBasisMatrixRat g *
              C.map (Int.castRingHom ℚ) := by
        have hmapV :
            V.map (Int.castRingHom ℚ) =
              T.map (Int.castRingHom ℚ) * C.map (Int.castRingHom ℚ) := by
          dsimp [V]
          ext i j
          simp [Matrix.mul_apply]
        rw [hmapV]
        calc
          P.1 * (T.map (Int.castRingHom ℚ) * C.map (Int.castRingHom ℚ)) =
              (P.1 * T.map (Int.castRingHom ℚ)) *
                C.map (Int.castRingHom ℚ) := by noncomm_ring
          _ = L.concreteAttachedRationalLatticeBasisMatrixRat g *
                C.map (Int.castRingHom ℚ) := by rw [hchange]
      have hdetEq := congrArg Matrix.det hchange_oriented
      rw [Matrix.det_mul, Matrix.det_mul] at hdetEq
      have hmapdet :
          (V.map (Int.castRingHom ℚ)).det = (V.det : ℚ) :=
        (RingHom.map_det (Int.castRingHom ℚ) V).symm
      rw [hmapdet, hVdet] at hdetEq
      norm_num at hdetEq
      have hright :=
        L.concreteAttachedRationalLatticeBasisMatrixRat_mul_orientationCorrection_det_pos g
      rw [Matrix.det_mul] at hright
      change 0 < (L.concreteAttachedRationalLatticeBasisMatrixRat g).det *
          (C.map (Int.castRingHom ℚ)).det at hright
      have hneg : 0 < -P.1.det := by
        rw [hdetEq]
        exact hright
      exfalso
      nlinarith [hneg, hPpos]
  refine ⟨V, hVunit, hVdet, ?_⟩
  rw [L.concreteOrientedAttachedIntegralLattice_pairingMatrix]
  dsimp [V]
  rw [Matrix.transpose_mul]
  calc
    (Cᵀ * Tᵀ) * M.pairingMatrix * (T * C) =
        Cᵀ * (Tᵀ * M.pairingMatrix * T) * C := by noncomm_ring
    _ = Cᵀ * (L.concreteAttachedIntegralLattice g).pairingMatrix * C := by
      rw [hTform]

/-- Every proper genus class is represented by a determinant-one rational
finite-adelic double coset. -/
theorem concreteProperDoubleCosetToProperGenus_surjective
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    Function.Surjective L.concreteProperDoubleCosetToProperGenus := by
  intro D
  rcases D.property with ⟨M, hsame, hD⟩
  obtain ⟨P, hP, hPpos⟩ :=
    L.exists_positive_det_rationalComparison_of_isSameGenus M hsame
  obtain ⟨U, hU, hdet⟩ :=
    L.exists_orientedHeightOneLocalIntegralMatrixUnits_of_isSameGenus
      M hsame P hP
  let g := L.concreteFiniteAdelicSpecialOrthogonalRepresentativeOfRationalComparison
    M P hP U hU hdet
  refine ⟨Quot.mk (leftRightDoubleCosetSetoid
    L.rationalSpecialOrthogonalDiagonalSubgroup
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) g, ?_⟩
  rw [L.concreteProperDoubleCosetToProperGenus_mk]
  apply Subtype.ext
  change (L.concreteOrientedAttachedIntegralLattice g.1).properGlobalIsometryClass = D.1
  rw [hD]
  exact properGlobalIsometryClass_eq_of_isProperGlobalIsometry
    (by
      simpa [g,
        concreteFiniteAdelicSpecialOrthogonalRepresentativeOfRationalComparison]
        using
          L.concreteOrientedAttachedIntegralLattice_representativeOfRationalComparison_isProperGlobalIsometry
            M P hP hPpos U hU)

/-- The concrete Schulze--Pillot parametrization of the proper genus by
determinant-one rational finite-adelic double cosets. -/
noncomputable def concreteProperAdelicGenusParametrization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    L.properGenus ≃ L.ConcreteProperRationalDoubleCosetSet :=
  (Equiv.ofBijective L.concreteProperDoubleCosetToProperGenus
    ⟨L.concreteProperDoubleCosetToProperGenus_injective,
      L.concreteProperDoubleCosetToProperGenus_surjective⟩).symm

/-- The concrete proper rational double quotient is finite, by injection into
the already finite proper genus. -/
noncomputable instance concreteProperRationalDoubleCosetSetFintype
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    Fintype L.ConcreteProperRationalDoubleCosetSet :=
  Fintype.ofInjective L.concreteProperDoubleCosetToProperGenus
    L.concreteProperDoubleCosetToProperGenus_injective

/-! ## Proper arithmetic stabilizers -/

/-- The proper arithmetic stabilizer
`SO(V)(Q) ∩ g H_f^+ g⁻¹` at a finite-adelic representative. -/
def concreteProperArithmeticStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.rationalSpecialOrthogonalDiagonalSubgroup ⊓
    conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup g

/-- Rational special-orthogonal matrices whose diagonal image belongs to the
proper arithmetic stabilizer at `g`. -/
def concreteRationalProperArithmeticStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Subgroup L.rationalSpecialOrthogonalMatrixSubgroup :=
  (conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup g).comap
    L.rationalSpecialOrthogonalDiagonalHom

/-- Faithfulness of the rational diagonal embedding identifies the ambient
proper arithmetic stabilizer with its rational special-orthogonal preimage. -/
noncomputable def concreteRationalProperArithmeticStabilizerEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteRationalProperArithmeticStabilizerSubgroup g ≃
      L.concreteProperArithmeticStabilizerSubgroup g where
  toFun q := ⟨L.rationalSpecialOrthogonalDiagonalHom q.1,
    ⟨⟨q.1, rfl⟩, q.2⟩⟩
  invFun a := by
    let q : L.rationalSpecialOrthogonalMatrixSubgroup := Classical.choose a.2.1
    have hq : L.rationalSpecialOrthogonalDiagonalHom q = a.1 :=
      Classical.choose_spec a.2.1
    refine ⟨q, ?_⟩
    change L.rationalSpecialOrthogonalDiagonalHom q ∈
      conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup g
    rw [hq]
    exact a.2.2
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply L.rationalOrthogonalDiagonalHom_injective
    exact congrArg Subtype.val (Classical.choose_spec
      ((show L.rationalSpecialOrthogonalDiagonalHom q.1 ∈
          L.rationalSpecialOrthogonalDiagonalSubgroup from ⟨q.1, rfl⟩)))
  right_inv a := by
    apply Subtype.ext
    exact Classical.choose_spec a.2.1

/-- Forgetting determinant-one structure sends a rational proper arithmetic
stabilizer element to the existing ordinary rational stabilizer. -/
noncomputable def concreteRationalProperArithmeticStabilizerToOrdinary
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalProperArithmeticStabilizerSubgroup g) :
    L.concreteRationalArithmeticStabilizerSubgroup g.1 := by
  refine ⟨q.1.1, ?_⟩
  rcases q.2 with ⟨h, hh⟩
  refine ⟨⟨h.1.1, h.2⟩, ?_⟩
  exact congrArg Subtype.val hh

/-- The action of a rational proper arithmetic stabilizer on the
orientation-corrected attached basis. -/
noncomputable def concreteRationalProperArithmeticStabilizerActionMatrix
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalProperArithmeticStabilizerSubgroup g) :
    Matrix (Fin n) (Fin n) ℤ :=
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  C * L.concreteRationalArithmeticStabilizerActionMatrix g.1
      (L.concreteRationalProperArithmeticStabilizerToOrdinary g q) * C

theorem concreteRationalProperArithmeticStabilizerActionMatrix_isUnit
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalProperArithmeticStabilizerSubgroup g) :
    IsUnit (L.concreteRationalProperArithmeticStabilizerActionMatrix g q) := by
  exact ((L.concreteAttachedOrientationCorrectionMatrix_isUnit g.1).mul
    (L.concreteRationalArithmeticStabilizerActionMatrix_isUnit g.1
      (L.concreteRationalProperArithmeticStabilizerToOrdinary g q))).mul
        (L.concreteAttachedOrientationCorrectionMatrix_isUnit g.1)

theorem concreteRationalProperArithmeticStabilizerActionMatrix_det
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalProperArithmeticStabilizerSubgroup g) :
    (L.concreteRationalProperArithmeticStabilizerActionMatrix g q).det = 1 := by
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let qo := L.concreteRationalProperArithmeticStabilizerToOrdinary g q
  let T := L.concreteRationalArithmeticStabilizerActionMatrix g.1 qo
  have hTdetQ : (T.det : ℚ) = 1 := by
    rw [L.concreteRationalArithmeticStabilizerActionMatrix_det_cast]
    exact (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff q.1.1).mp q.1.2
  have hTdet : T.det = 1 := by exact_mod_cast hTdetQ
  have hCself := L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hCdet := congrArg Matrix.det hCself
  change (C * T * C).det = 1
  rw [Matrix.det_mul, Matrix.det_one] at hCdet
  rw [Matrix.det_mul, Matrix.det_mul, hTdet]
  simpa [mul_assoc] using hCdet

theorem concreteRationalProperArithmeticStabilizerActionMatrix_form
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalProperArithmeticStabilizerSubgroup g) :
    (L.concreteRationalProperArithmeticStabilizerActionMatrix g q).transpose *
        (L.concreteOrientedAttachedIntegralLattice g.1).pairingMatrix *
          L.concreteRationalProperArithmeticStabilizerActionMatrix g q =
      (L.concreteOrientedAttachedIntegralLattice g.1).pairingMatrix := by
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let qo := L.concreteRationalProperArithmeticStabilizerToOrdinary g q
  let T := L.concreteRationalArithmeticStabilizerActionMatrix g.1 qo
  have hTform :
      T.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * T =
        (L.concreteAttachedIntegralLattice g.1).pairingMatrix :=
    L.concreteRationalArithmeticStabilizerActionMatrix_form g.1 qo
  have hCself : C * C = 1 :=
    L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hCtrans : C.transpose = C :=
    L.concreteAttachedOrientationCorrectionMatrix_transpose g.1
  rw [L.concreteOrientedAttachedIntegralLattice_pairingMatrix]
  change (C * T * C).transpose *
      (C.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) *
      (C * T * C) =
    C.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hCtrans]
  calc
    (C * (T.transpose * C)) *
          (C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) *
          (C * T * C) =
        C * T.transpose * (C * C) *
          (L.concreteAttachedIntegralLattice g.1).pairingMatrix *
          (C * C) * T * C := by noncomm_ring
    _ = C * (T.transpose *
          (L.concreteAttachedIntegralLattice g.1).pairingMatrix * T) * C := by
      rw [hCself]
      simp
      noncomm_ring
    _ = C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C := by
      rw [hTform]

/-- The corrected-basis action of the rational proper arithmetic stabilizer
on the proper isometry group of the oriented attached lattice. -/
noncomputable def concreteRationalProperArithmeticStabilizerToProperIsometryGroup
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteRationalProperArithmeticStabilizerSubgroup g →
      (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup :=
  fun q => ⟨L.concreteRationalProperArithmeticStabilizerActionMatrix g q,
    ⟨L.concreteRationalProperArithmeticStabilizerActionMatrix_isUnit g q,
      L.concreteRationalProperArithmeticStabilizerActionMatrix_form g q⟩,
    L.concreteRationalProperArithmeticStabilizerActionMatrix_det g q⟩

theorem concreteRationalProperArithmeticStabilizerToProperIsometryGroup_injective
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Function.Injective
      (L.concreteRationalProperArithmeticStabilizerToProperIsometryGroup g) := by
  intro q r hqr
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let qo := L.concreteRationalProperArithmeticStabilizerToOrdinary g q
  let ro := L.concreteRationalProperArithmeticStabilizerToOrdinary g r
  let Tq := L.concreteRationalArithmeticStabilizerActionMatrix g.1 qo
  let Tr := L.concreteRationalArithmeticStabilizerActionMatrix g.1 ro
  have hCself : C * C = 1 :=
    L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hU : C * Tq * C = C * Tr * C :=
    congrArg Subtype.val hqr
  have hT : Tq = Tr := by
    calc
      Tq = (C * C) * Tq * (C * C) := by rw [hCself]; simp
      _ = C * (C * Tq * C) * C := by noncomm_ring
      _ = C * (C * Tr * C) * C := by rw [hU]
      _ = (C * C) * Tr * (C * C) := by noncomm_ring
      _ = Tr := by rw [hCself]; simp
  have hiso :
      L.concreteRationalArithmeticStabilizerToIsometryGroup g.1 qo =
        L.concreteRationalArithmeticStabilizerToIsometryGroup g.1 ro := by
    exact Subtype.ext hT
  have hqo :=
    L.concreteRationalArithmeticStabilizerToIsometryGroup_injective g.1 hiso
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun x : L.concreteRationalArithmeticStabilizerSubgroup g.1 => x.1) hqo

/-- An ordinary rational arithmetic stabilizer of determinant one lifts to
the proper rational arithmetic stabilizer. -/
noncomputable def concreteRationalProperArithmeticStabilizerOfOrdinary
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q : L.concreteRationalArithmeticStabilizerSubgroup g.1)
    (hqdet : q.1.1.1.det = 1) :
    L.concreteRationalProperArithmeticStabilizerSubgroup g := by
  let qSO : L.rationalSpecialOrthogonalMatrixSubgroup :=
    ⟨q.1, (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff q.1).2 hqdet⟩
  let hO : L.finiteLocalLatticeStabilizerSubgroup := Classical.choose q.2
  have hhO : L.rationalOrthogonalDiagonalHom q.1 = g.1 * hO.1 * g.1⁻¹ :=
    Classical.choose_spec q.2
  let hval : L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    g⁻¹ * L.rationalSpecialOrthogonalDiagonalHom qSO * g
  have hval_eq : hval.1 = hO.1 := by
    change g.1⁻¹ * L.rationalOrthogonalDiagonalHom q.1 * g.1 = hO.1
    rw [hhO]
    simp [mul_assoc]
  let hSO : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
    ⟨hval, by
      change hval.1 ∈ L.finiteLocalLatticeStabilizerSubgroup
      rw [hval_eq]
      exact hO.2⟩
  refine ⟨qSO, ⟨hSO, ?_⟩⟩
  simp [hSO, hval, mul_assoc]

theorem concreteRationalProperArithmeticStabilizerToProperIsometryGroup_surjective
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Function.Surjective
      (L.concreteRationalProperArithmeticStabilizerToProperIsometryGroup g) := by
  intro V
  let C := L.concreteAttachedOrientationCorrectionMatrix g.1
  let U : Matrix (Fin n) (Fin n) ℤ := V.1
  let T : Matrix (Fin n) (Fin n) ℤ := C * U * C
  have hCunit : IsUnit C :=
    L.concreteAttachedOrientationCorrectionMatrix_isUnit g.1
  have hCself : C * C = 1 :=
    L.concreteAttachedOrientationCorrectionMatrix_mul_self g.1
  have hCtrans : C.transpose = C :=
    L.concreteAttachedOrientationCorrectionMatrix_transpose g.1
  have hTunit : IsUnit T := (hCunit.mul V.2.1.1).mul hCunit
  have hTdet : T.det = 1 := by
    have hCdet := congrArg Matrix.det hCself
    rw [Matrix.det_mul, Matrix.det_one] at hCdet
    change (C * U * C).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, V.2.2]
    simpa [mul_assoc] using hCdet
  have hTform :
      T.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * T =
        (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
    have hUform := V.2.1.2
    rw [L.concreteOrientedAttachedIntegralLattice_pairingMatrix] at hUform
    change U.transpose *
        (C.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * U =
      C.transpose * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C at hUform
    rw [hCtrans] at hUform
    dsimp [T]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hCtrans]
    calc
      (C * (U.transpose * C)) *
            (L.concreteAttachedIntegralLattice g.1).pairingMatrix *
            (C * U * C) =
          C * (U.transpose *
            (C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * U) * C := by
        noncomm_ring
      _ = C * (C *
            (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * C := by
        rw [hUform]
      _ = (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
        calc
          C * (C * (L.concreteAttachedIntegralLattice g.1).pairingMatrix * C) * C =
              (C * C) * (L.concreteAttachedIntegralLattice g.1).pairingMatrix *
                (C * C) := by noncomm_ring
          _ = (L.concreteAttachedIntegralLattice g.1).pairingMatrix := by
            rw [hCself]
            simp
  let W : (L.concreteAttachedIntegralLattice g.1).IsometryGroup :=
    ⟨T, hTunit, hTform⟩
  obtain ⟨qo, hqo⟩ :=
    L.concreteRationalArithmeticStabilizerToIsometryGroup_surjective g.1 W
  have haction :
      L.concreteRationalArithmeticStabilizerActionMatrix g.1 qo = T :=
    congrArg Subtype.val hqo
  have hqdet : qo.1.1.1.det = 1 := by
    rw [← L.concreteRationalArithmeticStabilizerActionMatrix_det_cast g.1 qo,
      haction, hTdet]
    norm_num
  let q := L.concreteRationalProperArithmeticStabilizerOfOrdinary g qo hqdet
  refine ⟨q, ?_⟩
  apply Subtype.ext
  have hqo' :
      L.concreteRationalProperArithmeticStabilizerToOrdinary g q = qo := by
    apply Subtype.ext
    change q.1.1 = qo.1
    rfl
  change C *
      L.concreteRationalArithmeticStabilizerActionMatrix g.1
        (L.concreteRationalProperArithmeticStabilizerToOrdinary g q) * C = U
  rw [hqo', haction]
  dsimp [T]
  calc
    C * (C * U * C) * C = (C * C) * U * (C * C) := by noncomm_ring
    _ = U := by rw [hCself]; simp

/-- The rational proper arithmetic stabilizer is equivalent to the proper
isometry group of the orientation-normalized attached lattice. -/
noncomputable def concreteRationalProperArithmeticStabilizerProperIsometryEquiv
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteRationalProperArithmeticStabilizerSubgroup g ≃
      (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup :=
  Equiv.ofBijective
    (L.concreteRationalProperArithmeticStabilizerToProperIsometryGroup g)
    ⟨L.concreteRationalProperArithmeticStabilizerToProperIsometryGroup_injective g,
      L.concreteRationalProperArithmeticStabilizerToProperIsometryGroup_surjective g⟩

/-- The ambient proper arithmetic stabilizer is equivalent to the proper
isometry group of the orientation-normalized attached lattice. -/
noncomputable def concreteProperArithmeticStabilizerProperIsometryEquiv
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperArithmeticStabilizerSubgroup g ≃
      (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup :=
  (L.concreteRationalProperArithmeticStabilizerEquiv g).symm.trans
    (L.concreteRationalProperArithmeticStabilizerProperIsometryEquiv g)

/-- The proper arithmetic stabilizer has the proper isometry-group cardinality
of the orientation-normalized attached lattice. -/
theorem concreteProperArithmeticStabilizer_cardinality
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Nat.card (L.concreteProperArithmeticStabilizerSubgroup g) =
      Fintype.card
        (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (L.concreteProperArithmeticStabilizerProperIsometryEquiv g)

/-- The oriented attached lattice and the chosen representative of its proper
genus class have proper isometry groups of the same cardinality. -/
theorem concreteOrientedAttachedIntegralLattice_card_eq_properGenusRepresentative
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Fintype.card
        (L.concreteOrientedAttachedIntegralLattice
          (Quot.out C).1).ProperIsometryGroup =
      Fintype.card
        (properGenusClassRepresentative L
          (L.concreteProperAdelicGenusParametrization.symm C)).ProperIsometryGroup := by
  apply properIsometryGroup_card_eq_of_isGlobalIsometry
  apply isGlobalIsometry_of_isProperGlobalIsometry
  apply isProperGlobalIsometry_of_properGlobalIsometryClass_eq
  calc
    (L.concreteOrientedAttachedIntegralLattice
        (Quot.out C).1).properGlobalIsometryClass =
        (L.concreteProperAdelicGenusParametrization.symm C).1 := rfl
    _ = (properGenusClassRepresentative L
          (L.concreteProperAdelicGenusParametrization.symm C)).properGlobalIsometryClass :=
      properGenusClassRepresentative_spec L
        (L.concreteProperAdelicGenusParametrization.symm C) |>.2

/-- The proper arithmetic stabilizer cardinality, indexed by the chosen
proper adelic genus parametrization. -/
theorem concreteChosenProperArithmeticStabilizer_cardinality
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (C : L.ConcreteProperRationalDoubleCosetSet) :
    Nat.card
        ((L.rationalSpecialOrthogonalDiagonalSubgroup ⊓
          conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
            (Quot.out C)) :
          Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup) =
      Fintype.card
        (properGenusClassRepresentative L
          (L.concreteProperAdelicGenusParametrization.symm C)).ProperIsometryGroup := by
  calc
    Nat.card
        ((L.rationalSpecialOrthogonalDiagonalSubgroup ⊓
          conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
            (Quot.out C)) :
          Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup) =
        Fintype.card
          (L.concreteOrientedAttachedIntegralLattice
            (Quot.out C).1).ProperIsometryGroup :=
      L.concreteProperArithmeticStabilizer_cardinality (Quot.out C)
    _ = Fintype.card
        (properGenusClassRepresentative L
          (L.concreteProperAdelicGenusParametrization.symm C)).ProperIsometryGroup :=
      L.concreteOrientedAttachedIntegralLattice_card_eq_properGenusRepresentative C

/-- The reciprocal proper arithmetic-stabilizer sum over the finite adelic
double quotient is the proof-note proper genus mass. -/
theorem concreteProperArithmeticStabilizerMassSum_eq_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    (∑ C : L.ConcreteProperRationalDoubleCosetSet,
        ((Nat.card
          ((L.rationalSpecialOrthogonalDiagonalSubgroup ⊓
            conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
              (Quot.out C)) :
            Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup) : ℚ)⁻¹)) =
      L.properClassGenusMass := by
  classical
  unfold properClassGenusMass
  let f : L.ConcreteProperRationalDoubleCosetSet → ℚ := fun C =>
    ((Nat.card
      ((L.rationalSpecialOrthogonalDiagonalSubgroup ⊓
        conjugateSubgroupCore L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
          (Quot.out C)) :
        Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup) : ℚ)⁻¹)
  let h : L.properGenus → ℚ := fun D =>
    ((Fintype.card
      (properGenusClassRepresentative L D).ProperIsometryGroup : ℚ)⁻¹)
  change (∑ C, f C) = ∑ D, h D
  refine Fintype.sum_equiv L.concreteProperAdelicGenusParametrization.symm f h ?_
  intro C
  dsimp [f, h]
  rw [L.concreteChosenProperArithmeticStabilizer_cardinality]

/-! ## Proper local right stabilizers -/

/-- The proper right-piece stabilizer at `g`, namely
`H_f^+ ∩ g⁻¹ SO(V)(ℚ) g`. -/
def concreteProperLocalRightStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Subgroup L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ⊓
    conjugateSubgroupCore L.rationalSpecialOrthogonalDiagonalSubgroup g⁻¹

theorem mem_concreteProperLocalRightStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g x : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    x ∈ L.concreteProperLocalRightStabilizerSubgroup g ↔
      x ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup ∧
        ∃ q : L.rationalSpecialOrthogonalMatrixSubgroup,
          x = g⁻¹ * L.rationalSpecialOrthogonalDiagonalHom q * g := by
  constructor
  · rintro ⟨hxH, q, hq⟩
    rcases q.2 with ⟨q, hqdiag⟩
    refine ⟨hxH, q, ?_⟩
    rw [hqdiag]
    simpa using hq
  · rintro ⟨hxH, q, rfl⟩
    refine ⟨hxH, ⟨L.rationalSpecialOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩, ?_⟩
    simp

/-- The proper local right stabilizer, regarded as a subgroup of the proper
compact open `H_f^+`. -/
def concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Subgroup L.finiteSpecialOrthogonalLatticeStabilizerSubgroup where
  carrier := {h | (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) ∈
    L.concreteProperLocalRightStabilizerSubgroup g}
  one_mem' := by
    exact (L.concreteProperLocalRightStabilizerSubgroup g).one_mem
  mul_mem' := by
    intro ha hb hha hhb
    exact (L.concreteProperLocalRightStabilizerSubgroup g).mul_mem hha hhb
  inv_mem' := by
    intro h hh
    exact (L.concreteProperLocalRightStabilizerSubgroup g).inv_mem hh

@[simp]
theorem mem_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    h ∈ L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g ↔
      (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) ∈
        L.concreteProperLocalRightStabilizerSubgroup g :=
  Iff.rfl

/-- Forgetting the ambient proper compact open identifies its selected
right-piece stabilizer with the corresponding ambient intersection. -/
def concreteProperLocalRightStabilizerInCompactOpenEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g ≃
      L.concreteProperLocalRightStabilizerSubgroup g where
  toFun h := ⟨h.1.1,
    (L.mem_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer_iff
      g h.1).mp h.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩,
    (L.mem_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer_iff
      g ⟨x.1, x.2.1⟩).mpr x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Conjugation by `g` identifies the proper local right stabilizer with the
proper arithmetic stabilizer. -/
def concreteProperLocalRightStabilizerArithmeticEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperLocalRightStabilizerSubgroup g ≃
      L.concreteProperArithmeticStabilizerSubgroup g where
  toFun x := by
    refine ⟨g * x.1 * g⁻¹, ?_⟩
    constructor
    · rcases x.2.2 with ⟨q, hq⟩
      rw [hq]
      simp [mul_assoc]
    · exact ⟨⟨x.1, x.2.1⟩, rfl⟩
  invFun a := by
    refine ⟨g⁻¹ * a.1 * g, ?_⟩
    constructor
    · rcases a.2.2 with ⟨h, hh⟩
      rw [hh]
      simp [mul_assoc]
    · exact ⟨⟨a.1, a.2.1⟩, by simp [mul_assoc]⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv a := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The selected right-piece stabilizer inside `H_f^+` is equivalent to the
proper arithmetic stabilizer. -/
def concreteProperLocalRightStabilizerInCompactOpenArithmeticEquiv
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g ≃
      L.concreteProperArithmeticStabilizerSubgroup g :=
  (L.concreteProperLocalRightStabilizerInCompactOpenEquiv g).trans
    (L.concreteProperLocalRightStabilizerArithmeticEquiv g)

/-- Every proper ambient local right stabilizer is finite. -/
theorem finite_concreteProperLocalRightStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Finite (L.concreteProperLocalRightStabilizerSubgroup g) :=
  Finite.of_equiv
    (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup
    ((L.concreteProperLocalRightStabilizerArithmeticEquiv g).trans
      (L.concreteProperArithmeticStabilizerProperIsometryEquiv g)).symm

/-- The ambient proper local and arithmetic stabilizers have equal
cardinality. -/
theorem concreteProperLocalRightStabilizer_cardinality
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Nat.card (L.concreteProperLocalRightStabilizerSubgroup g) =
      Nat.card (L.concreteProperArithmeticStabilizerSubgroup g) :=
  Nat.card_congr (L.concreteProperLocalRightStabilizerArithmeticEquiv g)

/-- The selected proper local right stabilizer inside `H_f^+` is finite. -/
theorem finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
  Finite.of_equiv
    (L.concreteOrientedAttachedIntegralLattice g.1).ProperIsometryGroup
    ((L.concreteProperLocalRightStabilizerInCompactOpenArithmeticEquiv g).trans
      (L.concreteProperArithmeticStabilizerProperIsometryEquiv g)).symm

/-- The selected proper local right stabilizer inside `H_f^+` has the proper
arithmetic stabilizer cardinality. -/
theorem concreteProperLocalRightStabilizerInCompactOpen_cardinality
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Nat.card
        (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) =
      Nat.card (L.concreteProperArithmeticStabilizerSubgroup g) :=
  Nat.card_congr
    (L.concreteProperLocalRightStabilizerInCompactOpenArithmeticEquiv g)

/-! ## Proper finite-stabilizer selectors -/

/-- The canonical measurable transversal in `H_f^+` for the finite proper
local right stabilizer. -/
noncomputable def concreteProperLocalRightStabilizerEmbeddingRealSlice
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    Set L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
  finiteSubgroupEmbeddingRealSlice
    (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g)

/-- Every proper local `embeddingReal` slice is measurable in `H_f^+`. -/
theorem concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    MeasurableSet (L.concreteProperLocalRightStabilizerEmbeddingRealSlice g) := by
  letI : Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    L.finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g
  letI : Fintype
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    Fintype.ofFinite _
  exact finiteSubgroupEmbeddingRealSlice_measurableSet
    (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g)
    (fun gamma => measurable_const_mul
      (gamma : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup))

/-- Every proper local `embeddingReal` slice is a left-coset transversal for
the finite proper local right stabilizer inside `H_f^+`. -/
theorem concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    IsLeftCosetTransversal
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g)
      (L.concreteProperLocalRightStabilizerEmbeddingRealSlice g) := by
  letI : Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    L.finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g
  letI : Fintype
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    Fintype.ofFinite _
  exact finiteSubgroupEmbeddingRealSlice_isLeftCosetTransversal
    (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g)

/-- The normalized Haar mass of a proper local selector is the reciprocal
cardinality of its finite proper local right stabilizer. -/
theorem concreteProperLocalRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure
        (L.concreteProperLocalRightStabilizerEmbeddingRealSlice g) =
      ENNReal.ofReal
        (1 / (Nat.card
          (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :
            ℝ)) := by
  letI : Finite
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    L.finite_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g
  letI : Fintype
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :=
    Fintype.ofFinite _
  letI : Measure.IsMulLeftInvariant
      L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure :=
    concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_isMulLeftInvariant L
  have hμ_univ :
      L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure Set.univ =
        ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using
      L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_univ
  exact finiteSubgroupEmbeddingRealSlice_measure_eq_inv_natCard
    (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g)
    (μ := L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure)
    hμ_univ

/-! ## Proper finite-transversal fundamental domain -/

/-- The finite proper transversal obtained by right-translating the canonical
local selector at every rational special-orthogonal double coset. -/
noncomputable def concreteProperFiniteTransversalFundamentalDomain
    (L : PositiveDefiniteIntegralLattice n) :
    Set L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  finiteRightTransversalFundamentalDomain
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
    (fun C : L.ConcreteProperRationalDoubleCosetSet =>
      L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C))

/-- Every element of the proper local right stabilizer conjugates its selected
representative through a rational special-orthogonal element. -/
theorem concreteProperLocalRightStabilizer_conjugates
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (s : L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer g) :
    ∃ gamma : L.rationalSpecialOrthogonalDiagonalSubgroup,
      (gamma : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) * g =
        g * ((s : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
          L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
  have hs := (L.mem_concreteProperLocalRightStabilizerSubgroup_iff g s.1.1).mp s.2
  rcases hs.2 with ⟨q, hq⟩
  refine ⟨⟨L.rationalSpecialOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩, ?_⟩
  rw [hq]
  simp [mul_assoc]

/-- The finite union of right-translated proper local selectors is
measurable. -/
theorem concreteProperFiniteTransversalFundamentalDomain_measurableSet
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    MeasurableSet L.concreteProperFiniteTransversalFundamentalDomain := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
  exact finiteRightTransversalFundamentalDomain_measurableSet_of_subgroup_comap
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
    (fun C : L.ConcreteProperRationalDoubleCosetSet =>
      L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C))
    hsub_comap L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C =>
      L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))

/- The finite proper transversal is a measurable fundamental domain for the
rational special-orthogonal subgroup. -/
set_option synthInstance.maxHeartbeats 100000 in
theorem concreteProperFiniteTransversalFundamentalDomain_isFundamentalDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    IsFundamentalDomain L.rationalSpecialOrthogonalDiagonalSubgroup
      L.concreteProperFiniteTransversalFundamentalDomain
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  let slice : L.ConcreteProperRationalDoubleCosetSet →
      Set L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have htrans : ∀ C : L.ConcreteProperRationalDoubleCosetSet,
      IsLeftCosetTransversal
        (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
          (Quot.out C))
        (slice C) := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      (Quot.out C)
  have hlocal : ∀ C : L.ConcreteProperRationalDoubleCosetSet,
      ∀ h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup,
        ∃ gamma : L.rationalSpecialOrthogonalDiagonalSubgroup,
          ∃ c : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup,
            c ∈ slice C ∧
              (gamma : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) *
                  (Quot.out C *
                    (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)) =
                Quot.out C *
                  (c : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
    intro C
    exact local_right_cover_of_stabilizer_transversal
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup (Quot.out C)
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        (Quot.out C))
      (slice C)
      (L.concreteProperLocalRightStabilizer_conjugates (Quot.out C))
      (htrans C).decomp
  have hcover := finiteRightTransversalFundamentalDomain_cover_of_local_right_cover
    L.rationalSpecialOrthogonalDiagonalSubgroup
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
    (fun C => Quot.out_eq C) slice hlocal
  have hlocal_unique : ∀ (C : L.ConcreteProperRationalDoubleCosetSet)
      (h₁ h₂ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup),
      h₁ ∈ slice C → h₂ ∈ slice C →
      (∃ gamma : L.rationalSpecialOrthogonalDiagonalSubgroup,
        (((h₂ * h₁⁻¹ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
            L.ConcreteFiniteAdelicSpecialOrthogonalGroup) =
          (Quot.out C)⁻¹ *
            (gamma : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) * Quot.out C)) →
      h₂ = h₁ := by
    intro C h₁ h₂ hh₁ hh₂ hstab
    apply (htrans C).unique h₁ h₂ hh₁ hh₂
    rw [L.mem_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer_iff]
    apply (L.mem_concreteProperLocalRightStabilizerSubgroup_iff
      (Quot.out C)
      ((h₂ * h₁⁻¹ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup)).2
    refine ⟨(h₂ * h₁⁻¹).property, ?_⟩
    rcases hstab with ⟨gamma, hgamma⟩
    rcases gamma.2 with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hq]
    exact hgamma
  have hgamma_unique :=
    finiteRightTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice hlocal_unique
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
  exact finiteRightTransversalFundamentalDomain_isFundamentalDomain_of_cover_unique_witness
    L.rationalSpecialOrthogonalDiagonalSubgroup
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C) slice
    hsub_comap L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup
    (fun C =>
      L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))
    hcover hgamma_unique

/-- The normalized proper Haar mass of the finite transversal is the sum of
the inverse proper local-right-stabilizer cardinalities. -/
theorem concreteProperFiniteTransversalFundamentalDomain_measure_eq_sum
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
        L.concreteProperFiniteTransversalFundamentalDomain =
      @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C => ENNReal.ofReal
          (1 / (Nat.card
            (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
              (Quot.out C)) : ℝ))) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  let slice : L.ConcreteProperRationalDoubleCosetSet →
      Set L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have hsub_comap := subgroup_comap_mspace_of_subtype_mspace
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
    L.concreteFiniteSpecialOrthogonalLatticeStabilizerMeasurableSpace_eq
  have hdisj :=
    rightTranslateSliceSet_pairwiseDisjoint_of_leftRightDoubleCosetRepresentatives
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice
  calc
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
        L.concreteProperFiniteTransversalFundamentalDomain =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure (slice C) := by
      exact finiteRightTransversalFundamentalDomain_measure_eq_sum_subgroupHaar
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
        (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C) slice
        hsub_comap L.measurableSet_finiteSpecialOrthogonalLatticeStabilizerSubgroup
        L.concreteFiniteSpecialOrthogonalLatticeStabilizerHaarMeasure_map_eq_restrict
        (fun C =>
          L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measurableSet (Quot.out C))
        hdisj
    _ = ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          ENNReal.ofReal
            (1 / (Nat.card
              (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
                (Quot.out C)) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro C _
      exact L.concreteProperLocalRightStabilizerEmbeddingRealSlice_measure_eq_inv_natCard
        (Quot.out C)

/-- The normalized proper Haar mass of the finite transversal is finite. -/
theorem concreteProperFiniteTransversalFundamentalDomain_measure_ne_top
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
        L.concreteProperFiniteTransversalFundamentalDomain ≠ ∞ := by
  rw [L.concreteProperFiniteTransversalFundamentalDomain_measure_eq_sum inst]
  exact ENNReal.sum_ne_top.2 fun C _ => ENNReal.ofReal_ne_top

/-- The proper finite-transversal quotient volume is the real sum of inverse
proper local-right-stabilizer cardinalities. -/
theorem concreteProperFiniteTransversalFundamentalDomain_volume_eq_sum
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteProperFiniteAdelicQuotientVolume
        L.concreteProperFiniteTransversalFundamentalDomain =
      @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C =>
          1 / (Nat.card
            (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
              (Quot.out C)) : ℝ)) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  let v : L.ConcreteProperRationalDoubleCosetSet → ℝ := fun C =>
    1 / (Nat.card
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        (Quot.out C)) : ℝ)
  have hv_nonneg : ∀ C, 0 ≤ v C := fun C =>
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hsum_ofReal :
      ENNReal.ofReal (∑ C : L.ConcreteProperRationalDoubleCosetSet, v C) =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet, ENNReal.ofReal (v C) :=
    ENNReal.ofReal_sum_of_nonneg (fun C _ => hv_nonneg C)
  calc
    L.concreteProperFiniteAdelicQuotientVolume
        L.concreteProperFiniteTransversalFundamentalDomain =
        (L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure
          L.concreteProperFiniteTransversalFundamentalDomain).toReal :=
      L.concreteProperFiniteAdelicQuotientVolume_eq_ambient _
    _ = (∑ C : L.ConcreteProperRationalDoubleCosetSet,
          ENNReal.ofReal (v C)).toReal := by
      rw [L.concreteProperFiniteTransversalFundamentalDomain_measure_eq_sum inst]
    _ = (ENNReal.ofReal
          (∑ C : L.ConcreteProperRationalDoubleCosetSet, v C)).toReal := by
      rw [hsum_ofReal]
    _ = ∑ C : L.ConcreteProperRationalDoubleCosetSet, v C := by
      exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun C _ => hv_nonneg C)

/-- The proper finite-adelic quotient volume of the finite transversal is the
real cast of the proper genus mass. -/
theorem concreteProperFiniteTransversalFundamentalDomain_volume_eq_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    L.concreteProperFiniteAdelicQuotientVolume
        L.concreteProperFiniteTransversalFundamentalDomain =
      ((L.properClassGenusMass : ℚ) : ℝ) := by
  rw [L.concreteProperFiniteTransversalFundamentalDomain_volume_eq_sum inferInstance]
  calc
    (∑ C : L.ConcreteProperRationalDoubleCosetSet,
        1 / (Nat.card
          (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
            (Quot.out C)) : ℝ)) =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          1 / (Nat.card
            (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro C _
      rw [L.concreteProperLocalRightStabilizerInCompactOpen_cardinality]
    _ = ((∑ C : L.ConcreteProperRationalDoubleCosetSet,
          ((Nat.card
            (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) : ℚ)⁻¹) : ℚ) : ℝ) := by
      push_cast
      simp only [one_div]
    _ = ((L.properClassGenusMass : ℚ) : ℝ) := by
      apply congrArg (fun x : ℚ => (x : ℝ))
      simpa [concreteProperArithmeticStabilizerSubgroup] using
        L.concreteProperArithmeticStabilizerMassSum_eq_properClassGenusMass

end PositiveDefiniteIntegralLattice

end
