import SMSFormula.QuadraticRelativeTopForm
import SMSFormula.QuadraticAnisotropicVectorHaar
import SMSFormula.RationalCliffordGeneralSpinUnitSquareLocalChart
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Algebra.IsOpenUnits
import SMSFormula.QuadraticPadicSquareBranchFiberMeasure

/-!
# Relative coordinate form throughout the last-coordinate value branch

At any point whose last coordinate is nonzero, the polar kernel is a
linear graph over the lower coordinates. This is a tangent map, not a
chart. The relative form on that graph has the varying denominator
`2 * a * y_last`.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The polar functional in the last-coordinate normal direction at any point. -/
theorem nonisotropicLastExtension_polar_normal (y : Fin (n + 1) → K) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin
      y lastCoordinateVector = 2 * algebraMap ℚ K a * y (Fin.last n) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, W.nonisotropicLastExtension_polar_last]

/-- The unique tangent graph over the lower coordinate projection. -/
def lastValueTangent (y : Fin (n + 1) → K) (hy : y (Fin.last n) ≠ 0)
    (w : Fin n → K) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin y).ker :=
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K
  let d := 2 * algebraMap ℚ K a * y (Fin.last n)
  ⟨Fin.snoc w 0 - (q.polarBilin y (Fin.snoc w 0) / d) • lastCoordinateVector, by
    change q.polarBilin y _ = 0
    rw [map_sub, map_smul, W.nonisotropicLastExtension_polar_normal]
    change _ - (_ / d) * d = 0
    rw [div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha)) hy), sub_self]⟩

@[simp] theorem lastValueTangent_castSucc (y : Fin (n + 1) → K)
    (hy : y (Fin.last n) ≠ 0) (w : Fin n → K) (i : Fin n) :
    (W.lastValueTangent a ha y hy w).1 i.castSucc = w i := by
  simp [lastValueTangent, lastCoordinateVector]

/-- Any supplied tangent with these lower coordinates is the same tangent.
No ambient or fiber representative is selected. -/
theorem lastValueTangent_unique (y : Fin (n + 1) → K)
    (hy : y (Fin.last n) ≠ 0)
    (v : (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin y).ker) :
    W.lastValueTangent a ha y hy (fun i ↦ v.1 i.castSucc) = v := by
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K
  have hv : v.1 = Fin.snoc (fun i ↦ v.1 i.castSucc) 0 + v.1 (Fin.last n) • lastCoordinateVector := by
    ext i
    cases i using Fin.lastCases <;> simp [lastCoordinateVector]
  have hp := v.2
  change q.polarBilin y v.1 = 0 at hp
  rw [hv, map_add, map_smul, W.nonisotropicLastExtension_polar_normal] at hp
  apply Subtype.ext
  conv_rhs => rw [hv]
  change _ - _ • _ = _ + _ • _
  have hd : 2 * algebraMap ℚ K a * y (Fin.last n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha)) hy
  have hc : -(q.polarBilin y (Fin.snoc (fun i ↦ v.1 i.castSucc) 0) /
      (2 * algebraMap ℚ K a * y (Fin.last n))) = v.1 (Fin.last n) := by
    rw [← neg_div, div_eq_iff hd]
    simpa only [smul_eq_mul] using (neg_eq_iff_add_eq_zero.mpr hp)
  rw [sub_eq_add_neg, ← neg_smul, hc]

/-- The full variable relative-form coefficient, at nonzero values.
The last coordinate is not replaced by its value one at the basepoint. -/
theorem relativeCoordinateTopForm_lastValueTangent
    (y : Fin (n + 1) → K) (hy : y (Fin.last n) ≠ 0)
    (hq : (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K y ≠ 0)
    (w : Fin n → Fin n → K) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).relativeCoordinateTopForm y
      (fun i ↦ W.lastValueTangent a ha y hy (w i)) =
      ((-1 : K)^n / (2 * algebraMap ℚ K a * y (Fin.last n))) * (Pi.basisFun K (Fin n)).det w := by
  let d := 2 * algebraMap ℚ K a * y (Fin.last n)
  have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha)) hy
  rw [QuadraticMap.relativeCoordinateTopForm_eq_of_lift _ y hq (d⁻¹ • lastCoordinateVector)
    (by rw [map_smul, W.nonisotropicLastExtension_polar_normal]; exact inv_mul_cancel₀ hd)]
  have hgraph (i : Fin n) : (W.lastValueTangent a ha y hy (w i)).1 =
      Fin.snoc (w i) ((W.lastValueTangent a ha y hy (w i)).1 (Fin.last n)) := by
    ext j
    cases j using Fin.lastCases <;> simp
  rw [show (fun i ↦ (W.lastValueTangent a ha y hy (w i)).1) =
      (fun i ↦ Fin.snoc (w i) ((W.lastValueTangent a ha y hy (w i)).1 (Fin.last n)))
    from funext hgraph]
  rw [coordinateDet_last_normal_snoc]
  simp only [d, div_eq_mul_inv]

/-- Orthogonality to the supplied last vector means its last coordinate is zero. -/
theorem lastOrthogonal_coordinate_zero
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).anisotropicOrthogonal
      lastCoordinateVector) : z.1 (Fin.last n) = 0 := by
  let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K
  have hz := q.mem_anisotropicOrthogonal_iff.mp z.2
  change q.associated lastCoordinateVector z.1 = 0 at hz
  have hp : q.polarBilin lastCoordinateVector z.1 = 0 := by
    rw [← q.two_nsmul_associated ℕ]
    simp only [two_smul, LinearMap.add_apply]
    change q.associated lastCoordinateVector z.1 + q.associated lastCoordinateVector z.1 = 0
    rw [hz, zero_add]
  rw [W.nonisotropicLastExtension_polar_last] at hp
  exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha))

/-- On the orthogonal splitting, the tangent graph has the actual implicit
square-branch differential expression. The splitting and its transverse input
are supplied; no chart or section is constructed. -/
theorem lastValueTangent_eq_of_split
    (y : Fin (n + 1) → K) (hy : y (Fin.last n) ≠ 0) (s : K)
    (z v : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).anisotropicOrthogonal
      lastCoordinateVector)
    (hyz : y = s • lastCoordinateVector + z.1) :
    (W.lastValueTangent a ha y hy (fun i ↦ v.1 i.castSucc)).1 =
      v.1 - ((((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin
        z.1 v.1) / (2 * algebraMap ℚ K a * s)) • lastCoordinateVector := by
  have hv : Fin.snoc (fun i ↦ v.1 i.castSucc) 0 = v.1 := by
    ext i
    cases i using Fin.lastCases <;> simp [W.lastOrthogonal_coordinate_zero a ha v]
  have hys : y (Fin.last n) = s := by
    rw [hyz]
    simp [lastCoordinateVector, W.lastOrthogonal_coordinate_zero a ha z]
  have hp : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin y v.1 =
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm K).polarBilin z.1 v.1 := by
    rw [hyz, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      W.nonisotropicLastExtension_polar_last, W.lastOrthogonal_coordinate_zero a ha v]
    simp
  change _ - _ • _ = _
  rw [hv, hp, hys]

section Real

end Real

section Padic
variable (p : ℕ) [Fact (Nat.Prime p)]
local instance squareBranchRelativePadicMeasurable : MeasurableSpace ℚ_[p] := borel _
local instance squareBranchRelativePadicBorel : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The branch's last coordinate is its actual nonzero square-root coordinate. -/
theorem padicSquareBranch_last_coordinate (value : ℚ_[p])
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain p lastCoordinateVector value) :
    let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
    let y := q.padicSquareBranchFiberMap p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value z
    y.1 (Fin.last n) = Rat.padicUnitSquareTargetSupportedInverse p
      ((value - q.orthogonalRestriction lastCoordinateVector z.1) / q lastCoordinateVector) := by
  dsimp only [padicSquareBranchFiberMap]
  simp [lastCoordinateVector, W.lastOrthogonal_coordinate_zero a ha z.1]

/-- No regularity of the value is needed for the branch coordinate to be nonzero. -/
theorem padicSquareBranch_last_coordinate_ne_zero     (value : ℚ_[p])
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain p lastCoordinateVector value) :
    let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
    let y := q.padicSquareBranchFiberMap p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value z
    y.1 (Fin.last n) ≠ 0 := by
  dsimp only
  rw [W.padicSquareBranch_last_coordinate]
  rw [Rat.padicUnitSquareTargetSupportedInverse_eq p z.2]
  exact Rat.padicUnitSquareScalarSource_ne_zero p
    (Rat.padicUnitSquareScalarInverse_mem_and_sq p z.2).1

/-- The variable branch density is the modulus of the relative form at
every regular value and every point of the branch, on its tangent graph.
The statement retains the moving square-root coordinate, not its basepoint. -/
theorem padicSquareBranch_relativeForm_eq_jacobian (value : ℚ_[p])
    (z : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain p lastCoordinateVector value)
    (hvalue : value ≠ 0) :
    let q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]
    let y := q.padicSquareBranchFiberMap p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value z
    (‖q.relativeCoordinateTopForm y.1
      (fun i ↦ W.lastValueTangent a ha y.1 (W.padicSquareBranch_last_coordinate_ne_zero a ha p value z)
        (Pi.basisFun ℚ_[p] (Fin n) i))‖₊ : ℝ≥0∞) =
      q.padicSquareBranchFiberJacobianInverse p lastCoordinateVector value z.1 := by
  dsimp only
  rw [W.relativeCoordinateTopForm_lastValueTangent a ha _ _
    (by exact (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) value z).property.trans_ne hvalue), Module.Basis.det_self, mul_one]
  unfold padicSquareBranchFiberJacobianInverse
  rw [W.padicSquareBranch_last_coordinate, W.nonisotropicLastExtension_quadratic_last]
  simp only [nnnorm_div, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, one_div]
  apply ENNReal.coe_inv
  apply nnnorm_ne_zero_iff.mpr
  apply mul_ne_zero (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr ha))
  have h := W.padicSquareBranch_last_coordinate_ne_zero a ha p value z
  dsimp only at h
  rw [W.padicSquareBranch_last_coordinate, W.nonisotropicLastExtension_quadratic_last] at h
  exact h

end Padic

end RationalQuadraticSpaceMatrix
