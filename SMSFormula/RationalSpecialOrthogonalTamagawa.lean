import SMSFormula.AdelicProperFullPresentation
import SMSFormula.AdelicWeilQuotient
import SMSFormula.SkewAdjointBaseChange

/-!
# Rational special-orthogonal adelic quotients

This module isolates the non-lattice objects needed to state a normalized
Tamagawa-number theorem for a rational special orthogonal group:

* a nonsingular symmetric rational form matrix;
* its rational and full-adelic special orthogonal groups;
* the diagonal rational subgroup and abstract left quotient;
* the rational skew-adjoint determinant form at the identity;
* ambient and quotient measures satisfying the left Weil formula.

The final structure in this file is deliberately only Weil-normalized.
Simultaneously rescaling its ambient and quotient measures preserves all its
fields.  It is therefore not a differential-induced Tamagawa
normalization, and no theorem asserting that its quotient mass is `2` is
stated here.  The differential normalization and the value `τ(SO) = 2` for
the raw lattice differential datum are proved in
`SMSFormula.RationalSpecialOrthogonalTamagawaNumberFromSpin`, through intrinsic
`τ(Spin) = 1`.
-/

noncomputable section

variable {n : ℕ}

open MeasureTheory
open TopologicalSpace
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

/-- A rational quadratic space presented by a nonsingular symmetric matrix.

This contains no integral lattice or positivity datum.  The matrix presentation
is the one used by the existing rational skew-adjoint tangent construction. -/
structure RationalQuadraticSpaceMatrix (n : ℕ) where
  pairingMatrix : Matrix (Fin n) (Fin n) ℚ
  form_symm : pairingMatrix.IsSymm
  form_det_ne_zero : pairingMatrix.det ≠ 0

namespace RationalQuadraticSpaceMatrix

/-- The tangent space at the identity of the matrix special orthogonal group. -/
abbrev skewAdjointTangent (V : RationalQuadraticSpaceMatrix n) :=
  skewAdjointMatricesLieSubalgebra V.pairingMatrix

/-- The fixed rational top form on the skew-adjoint tangent space.

Its scalar extensions are the placewise forms already used by the real and
p-adic coordinate developments. -/
def invariantTopDifferential (V : RationalQuadraticSpaceMatrix n) :
    V.skewAdjointTangent
      [⋀^Fin (Module.finrank ℚ V.skewAdjointTangent)]→ₗ[ℚ] ℚ :=
  Matrix.skewAdjointDetForm V.pairingMatrix

theorem invariantTopDifferential_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.invariantTopDifferential ≠ 0 :=
  Matrix.skewAdjointDetForm_ne_zero V.pairingMatrix

/-- The rational orthogonal matrix group of `V`. -/
def rationalOrthogonalMatrixSubgroup (V : RationalQuadraticSpaceMatrix n) :
    Subgroup (Matrix (Fin n) (Fin n) ℚ)ˣ :=
  formPreservingMatrixSubgroup V.pairingMatrix

/-- The rational special orthogonal matrix group of `V`. -/
def rationalSpecialOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.rationalOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup V.pairingMatrix

abbrev RationalSpecialOrthogonalGroup
    (V : RationalQuadraticSpaceMatrix n) :=
  V.rationalSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_rationalOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    g ∈ V.rationalOrthogonalMatrixSubgroup ↔
      g.1ᵀ * V.pairingMatrix * g.1 = V.pairingMatrix :=
  Iff.rfl

@[simp]
theorem mem_rationalSpecialOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.rationalOrthogonalMatrixSubgroup) :
    g ∈ V.rationalSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff V.pairingMatrix g

/-- The form matrix transported diagonally to the full rational adeles. -/
def fullAdelicFormMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) RationalAdele :=
  V.pairingMatrix.map (algebraMap ℚ RationalAdele)

/-- The full-adelic orthogonal matrix group of `V`. -/
def fullAdelicOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalAdele)ˣ :=
  formPreservingMatrixSubgroup V.fullAdelicFormMatrix

/-- The full-adelic special orthogonal matrix group of `V`. -/
def fullAdelicSpecialOrthogonalMatrixSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.fullAdelicOrthogonalMatrixSubgroup :=
  specialFormPreservingMatrixSubgroup V.fullAdelicFormMatrix

abbrev FullAdelicSpecialOrthogonalGroup
    (V : RationalQuadraticSpaceMatrix n) :=
  V.fullAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_fullAdelicOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    g ∈ V.fullAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * V.fullAdelicFormMatrix * g.1 = V.fullAdelicFormMatrix :=
  Iff.rfl

@[simp]
theorem mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    g ∈ V.fullAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff V.fullAdelicFormMatrix g

/-- Diagonal scalar extension from rational orthogonal matrices to the full
adelic orthogonal group. -/
def rationalOrthogonalFullAdelicDiagonalHom
    (V : RationalQuadraticSpaceMatrix n) :
    V.rationalOrthogonalMatrixSubgroup →*
      V.fullAdelicOrthogonalMatrixSubgroup where
  toFun g := by
    let mapped := Matrix.GeneralLinearGroup.map
      (n := Fin n) (algebraMap ℚ RationalAdele) g.1
    refine ⟨mapped, ?_⟩
    rw [V.mem_fullAdelicOrthogonalMatrixSubgroup_iff]
    have hmapped := congrArg
      (fun M ↦ M.map (algebraMap ℚ RationalAdele)) g.2
    simpa [fullAdelicFormMatrix, mapped, Matrix.map_mul,
      Matrix.transpose_map] using hmapped
  map_one' := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_one
      (n := Fin n) (algebraMap ℚ RationalAdele)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_mul
      (n := Fin n) (algebraMap ℚ RationalAdele) g.1 h.1

@[simp]
theorem rationalOrthogonalFullAdelicDiagonalHom_apply_matrix
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.rationalOrthogonalMatrixSubgroup) :
    (V.rationalOrthogonalFullAdelicDiagonalHom g).1.1 =
      g.1.1.map (algebraMap ℚ RationalAdele) :=
  rfl

/-- The diagonal embedding restricted to determinant-one matrices. -/
def rationalSpecialOrthogonalFullAdelicDiagonalHom
    (V : RationalQuadraticSpaceMatrix n) :
    V.RationalSpecialOrthogonalGroup →*
      V.FullAdelicSpecialOrthogonalGroup :=
  (V.rationalOrthogonalFullAdelicDiagonalHom.restrict
      V.rationalSpecialOrthogonalMatrixSubgroup).codRestrict
    V.fullAdelicSpecialOrthogonalMatrixSubgroup (by
      intro g
      rw [V.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff]
      have hdet : g.1.1.1.det = 1 :=
        (V.mem_rationalSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
      change
        (Matrix.GeneralLinearGroup.map
          (algebraMap ℚ RationalAdele) g.1.1).1.det = 1
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := algebraMap ℚ RationalAdele) g.1.1)
      simpa [hdet] using hmap)

@[simp]
theorem rationalSpecialOrthogonalFullAdelicDiagonalHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.RationalSpecialOrthogonalGroup) :
    (V.rationalSpecialOrthogonalFullAdelicDiagonalHom g).1 =
      V.rationalOrthogonalFullAdelicDiagonalHom g.1 :=
  rfl

/-- The diagonal rational `SO(V)(ℚ)` subgroup in `SO(V)(A_ℚ)`. -/
def rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
    (V : RationalQuadraticSpaceMatrix n) :
    Subgroup V.FullAdelicSpecialOrthogonalGroup :=
  V.rationalSpecialOrthogonalFullAdelicDiagonalHom.range

/-- The abstract rational left quotient `SO(V)(ℚ) \ SO(V)(A_ℚ)`. -/
abbrev FullAdelicSpecialOrthogonalLeftQuotient
    (V : RationalQuadraticSpaceMatrix n) :=
  leftCosetSet V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- The canonical map to the rational full-adelic left quotient. -/
def fullAdelicSpecialOrthogonalLeftQuotientMap
    (V : RationalQuadraticSpaceMatrix n) :
    V.FullAdelicSpecialOrthogonalGroup →
      V.FullAdelicSpecialOrthogonalLeftQuotient :=
  leftCosetMap V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- The full-adelic matrix group uses its inherited Borel measurable space. -/
instance fullAdelicSpecialOrthogonalGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FullAdelicSpecialOrthogonalGroup :=
  borel V.FullAdelicSpecialOrthogonalGroup

instance fullAdelicSpecialOrthogonalGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The quotient measurable structure generated by the left-quotient map. -/
instance fullAdelicSpecialOrthogonalLeftQuotientMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FullAdelicSpecialOrthogonalLeftQuotient :=
  MeasurableSpace.map V.fullAdelicSpecialOrthogonalLeftQuotientMap
    (borel V.FullAdelicSpecialOrthogonalGroup)

theorem fullAdelicSpecialOrthogonalLeftQuotientMap_measurable
    (V : RationalQuadraticSpaceMatrix n) :
    Measurable V.fullAdelicSpecialOrthogonalLeftQuotientMap :=
  leftCosetMap_measurable_map
    V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

/-- Ambient and quotient measures satisfying the left Weil formula.

This packages the quotient normalization relative to the supplied ambient
measure.  It does **not** certify that the ambient measure is induced by
`V.invariantTopDifferential`: simultaneous nonzero rescaling remains possible.
-/
structure SpecialOrthogonalAdelicWeilMeasureData
    (V : RationalQuadraticSpaceMatrix n) where
  adelicMeasure : Measure V.FullAdelicSpecialOrthogonalGroup
  quotientMeasure : Measure V.FullAdelicSpecialOrthogonalLeftQuotient
  isWeilQuotientMeasure :
    IsLeftWeilQuotientMeasure
      V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      adelicMeasure quotientMeasure

namespace SpecialOrthogonalAdelicWeilMeasureData

/-- Common scalar rescaling preserves the left Weil formula.

This is the formal reason that `SpecialOrthogonalAdelicWeilMeasureData` alone
cannot be the normalization hypothesis of a `tau = 2` theorem. -/
theorem isLeftWeilQuotientMeasure_smul
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) (c : ℝ≥0∞) :
    IsLeftWeilQuotientMeasure
      V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      (c • D.adelicMeasure) (c • D.quotientMeasure) where
  lintegral_leftPeriodize_eq f := by
    rw [lintegral_smul_measure, lintegral_smul_measure,
      D.isWeilQuotientMeasure.lintegral_leftPeriodize_eq]

/-- Simultaneously rescale the ambient and quotient measures in a Weil datum. -/
def smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0∞) (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    SpecialOrthogonalAdelicWeilMeasureData V where
  adelicMeasure := c • D.adelicMeasure
  quotientMeasure := c • D.quotientMeasure
  isWeilQuotientMeasure := D.isLeftWeilQuotientMeasure_smul c

/-- The `ENNReal` total mass of the Weil-normalized adelic quotient. -/
def tamagawaNumberENNReal
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) : ℝ≥0∞ :=
  D.quotientMeasure Set.univ

/-- The real-valued total mass of the Weil-normalized adelic quotient. -/
def tamagawaNumber
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) : ℝ :=
  D.tamagawaNumberENNReal.toReal

@[simp]
theorem tamagawaNumberENNReal_eq
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    D.tamagawaNumberENNReal = D.quotientMeasure Set.univ :=
  rfl

@[simp]
theorem tamagawaNumberENNReal_smul
    {V : RationalQuadraticSpaceMatrix n}
    (c : ℝ≥0∞) (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    (D.smul c).tamagawaNumberENNReal = c * D.tamagawaNumberENNReal := by
  change (c • D.quotientMeasure) Set.univ =
    c * D.quotientMeasure Set.univ
  rw [Measure.smul_apply, smul_eq_mul]

@[simp]
theorem tamagawaNumber_eq
    {V : RationalQuadraticSpaceMatrix n}
    (D : SpecialOrthogonalAdelicWeilMeasureData V) :
    D.tamagawaNumber = (D.quotientMeasure Set.univ).toReal :=
  rfl

end SpecialOrthogonalAdelicWeilMeasureData

end RationalQuadraticSpaceMatrix

end
