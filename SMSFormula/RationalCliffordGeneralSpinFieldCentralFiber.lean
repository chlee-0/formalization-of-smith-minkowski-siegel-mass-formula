import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity

/-!
# The two-point central fiber of intrinsic general Spin

Over a characteristic-zero rational field, combine the intrinsic similitude
character with the projection to special orthogonal.  Horizontal exactness
first forces a point in the kernel of this combined map to be central scalar.
The literal formula `nu(z) = z^2` then reduces the remaining kernel to the
two scalar points `1` and `-1`.

This is the algebraic central-fiber normalization needed before transporting
local Haar measure through the crossed `GSpin` chart.  It introduces no Haar
scale or quotient normalization.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (K : Type*) [Field K] [Algebra ℚ K]

namespace CliffordGeneralSpinIntrinsicPoint

/-- The crossed field-valued map `(nu, pi) : GSpin(K) -> K^* x SO(K)`. -/
def centralFiberGroupHom :
    V.CliffordGeneralSpinIntrinsicPoint K →*
      Kˣ × V.specialOrthogonalMatrixGroup K :=
  (similitudeGroupHom V K).prod (toSpecialOrthogonalGroupHom V K)

@[simp]
theorem centralFiberGroupHom_apply
    (x : V.CliffordGeneralSpinIntrinsicPoint K) :
    centralFiberGroupHom V K x = (x.similitude, x.matrixGroup) :=
  rfl

/-- The nontrivial scalar point in the central fiber. -/
def centralFiberNegOnePoint :
    V.CliffordGeneralSpinIntrinsicPoint K :=
  scalarGroupHom V K (-1)

@[simp]
theorem centralFiberGroupHom_negOnePoint :
    centralFiberGroupHom V K (centralFiberNegOnePoint V K) = 1 := by
  apply Prod.ext
  · simp [centralFiberNegOnePoint, centralFiberGroupHom]
  · change (ofScalar V K (-1)).matrixGroup = 1
    exact ofScalar_matrixGroup V K (-1)

/-- Every point killed by both the similitude and the special-orthogonal
projection is literally scalar `1` or scalar `-1`. -/
theorem eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
    (x : V.CliffordGeneralSpinIntrinsicPoint K)
    (hx : centralFiberGroupHom V K x = 1) :
    x = 1 ∨ x = centralFiberNegOnePoint V K := by
  have hmatrix : x.matrixGroup = 1 := by
    exact congrArg Prod.snd hx
  obtain ⟨z, hz⟩ := exists_scalar_eq_of_matrixGroup_eq_one V K x hmatrix
  subst x
  have hzsqUnits : z ^ 2 = 1 := by
    simpa [centralFiberGroupHom] using congrArg Prod.fst hx
  have hzsq : ((z : K)) ^ 2 = 1 := by
    exact congrArg Units.val hzsqUnits
  rcases sq_eq_one_iff.mp hzsq with hzOne | hzNeg
  · left
    have hz : z = 1 := by
      apply Units.ext
      exact hzOne
    rw [hz]
    change scalarGroupHom V K 1 = 1
    exact map_one (scalarGroupHom V K)
  · right
    have hz : z = -1 := by
      apply Units.ext
      exact hzNeg
    rw [hz]
    rfl

/-- Set-level form of the literal two-point kernel. -/
theorem centralFiberGroupHom_ker_eq_pair :
    ((centralFiberGroupHom V K).ker :
        Set (V.CliffordGeneralSpinIntrinsicPoint K)) =
      {1, centralFiberNegOnePoint V K} := by
  ext x
  constructor
  · intro hx
    exact eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
      V K x hx
  · intro hx
    rcases hx with rfl | rfl
    · exact map_one (centralFiberGroupHom V K)
    · exact centralFiberGroupHom_negOnePoint V K

/-- The two scalar points in the central fiber are distinct. -/
theorem centralFiberNegOnePoint_ne_one :
    centralFiberNegOnePoint V K ≠ 1 := by
  intro h
  have hclifford := congrArg
    (fun x : V.CliffordGeneralSpinIntrinsicPoint K =>
      (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra K)) h
  have hscalar : (-1 : K) = 1 := by
    apply V.cliffordCoordinateBaseChange_algebraMap_injective K
    simpa [centralFiberNegOnePoint, scalarGroupHom, scalarMonoidHom,
      ofScalar] using hclifford
  have hscalarQ : (-1 : ℚ) = 1 := by
    apply (algebraMap ℚ K).injective
    simpa using hscalar
  norm_num at hscalarQ

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix
