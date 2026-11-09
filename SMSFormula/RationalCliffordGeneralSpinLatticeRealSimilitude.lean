import SMSFormula.RationalCliffordGeneralSpinAdelicProduct
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRange
import SMSFormula.SpecialOrthogonalRealLatticeReference

/-!
# Real similitudes of the lattice intrinsic general-Spin group

For the positive-definite real form attached to an integral lattice, every
intrinsic general-Spin similitude is positive. Conversely every positive real
unit is the similitude of a central scalar point, using its positive square
root. Thus the real similitude image is exactly `R_{>0}`. This is the
archimedean image used by the crossed logarithmic cutoff.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open QuadraticMap.ReflectionWord

namespace RationalQuadraticSpaceMatrix

/-- Positive real units as the subgroup relevant to a positive-definite
general-Spin similitude. -/
def positiveRealUnitsSubgroup : Subgroup ℝˣ where
  carrier := {a | 0 < (a : ℝ)}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    simpa only [Set.mem_setOf_eq, Units.val_mul] using mul_pos ha hb
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] using inv_pos.mpr ha

/-- Positive rational units, the only possible rational similitudes of a
positive-definite intrinsic general-Spin group. -/
def positiveRationalUnitsSubgroup : Subgroup ℚˣ where
  carrier := {a | 0 < (a : ℚ)}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    simpa only [Set.mem_setOf_eq, Units.val_mul] using mul_pos ha hb
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] using inv_pos.mpr ha

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

theorem latticeRealQuadraticForm_pos
    (v : (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
      ℝ).AnisotropicVector) :
    0 < L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
      ℝ v := by
  have hv : (v : Fin n → ℝ) ≠ 0 := by
    intro hv0
    apply v.property
    simp [hv0]
  rw [L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
  have hmatrix : L.rationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix ℝ =
      L.pairingMatrix_real := by
    simpa [specialOrthogonalMappedFormMatrix,
      PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix] using
      L.rationalFormMatrix_map_real
  rw [hmatrix]
  exact L.form_posDef.dotProduct_mulVec_pos hv

theorem latticeRealReflectionPairQuadraticUnit_pos
    (p : L.rationalQuadraticSpaceMatrix.ReflectionPair ℝ) :
    0 < (reflectionPairQuadraticUnit
      (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℝ)
      p : ℝ) := by
  change 0 < L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
      ℝ p.1 *
    L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℝ p.2
  exact mul_pos (latticeRealQuadraticForm_pos L p.1)
    (latticeRealQuadraticForm_pos L p.2)

theorem latticeRealReflectionPairsQuadraticUnit_pos
    (ps : List (L.rationalQuadraticSpaceMatrix.ReflectionPair ℝ)) :
    0 < (reflectionPairsQuadraticUnit
      (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℝ)
      ps : ℝ) := by
  induction ps with
  | nil => norm_num
  | cons p ps ih =>
      rw [reflectionPairsQuadraticUnit_cons]
      exact mul_pos (latticeRealReflectionPairQuadraticUnit_pos L p) ih

theorem realCliffordGeneralSpinSimilitude_pos
    (x : L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup) :
    0 < (L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitudeHom x : ℝ) := by
  obtain ⟨ps, hps, z, hx⟩ :=
    CliffordGeneralSpinIntrinsicPoint.exists_scalar_mul_reflectionPairs_eq
      L.rationalQuadraticSpaceMatrix ℝ x
  have hnu : x.similitude = z ^ 2 *
      reflectionPairsQuadraticUnit
        (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℝ)
        ps := by
    have h := congrArg
      (fun y : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint ℝ =>
        y.similitude) hx
    simpa [CliffordGeneralSpinIntrinsicPoint.mul_similitude] using h
  rw [show L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitudeHom x =
      x.similitude from rfl,
    hnu]
  change 0 < (z : ℝ) ^ 2 *
    (reflectionPairsQuadraticUnit
      (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm ℝ)
      ps : ℝ)
  exact mul_pos (sq_pos_of_ne_zero z.ne_zero)
    (latticeRealReflectionPairsQuadraticUnit_pos L ps)

theorem exists_realCliffordGeneralSpin_similitude_eq_of_pos
    (a : ℝˣ) (ha : 0 < (a : ℝ)) :
    ∃ x : L.rationalQuadraticSpaceMatrix.RealCliffordGeneralSpinGroup,
      L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitudeHom x = a := by
  let z : ℝˣ := Units.mk0 (Real.sqrt (a : ℝ))
    (ne_of_gt (Real.sqrt_pos.2 ha))
  refine ⟨CliffordGeneralSpinIntrinsicPoint.ofScalar
    L.rationalQuadraticSpaceMatrix ℝ z, ?_⟩
  apply Units.ext
  change Real.sqrt (a : ℝ) ^ 2 = (a : ℝ)
  exact Real.sq_sqrt (le_of_lt ha)

/-- The real similitude image of the positive-definite lattice intrinsic
general-Spin group is exactly the positive real units. -/
theorem range_realCliffordGeneralSpinSimilitudeHom :
    L.rationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitudeHom.range =
      positiveRealUnitsSubgroup := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact realCliffordGeneralSpinSimilitude_pos L x
  · intro ha
    exact exists_realCliffordGeneralSpin_similitude_eq_of_pos L a ha

/-- A rational intrinsic general-Spin similitude for a positive-definite
lattice form is positive. This is transported from the real image theorem
through the literal rational diagonal. -/
theorem rationalCliffordGeneralSpinSimilitude_pos
    (x : L.rationalQuadraticSpaceMatrix.RationalCliffordGeneralSpinGroup) :
    0 < (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
      L.rationalQuadraticSpaceMatrix ℚ x : ℚ) := by
  have hreal := realCliffordGeneralSpinSimilitude_pos L
    (L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinRealDiagonalHom x)
  rw [L.rationalQuadraticSpaceMatrix.rational_real_diagonal_generalSpin_similitude]
    at hreal
  change 0 < (((x.similitude : ℚ) : ℝ)) at hreal
  exact_mod_cast hreal

/-- The rational similitude image is contained in the positive rational
units. The reverse inclusion is the remaining rational common-value/Hasse
calculation. -/
theorem range_rationalCliffordGeneralSpinSimilitudeHom_le_positive :
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
      L.rationalQuadraticSpaceMatrix ℚ).range ≤
      positiveRationalUnitsSubgroup := by
  rintro a ⟨x, rfl⟩
  exact rationalCliffordGeneralSpinSimilitude_pos L x

end RationalQuadraticSpaceMatrix
