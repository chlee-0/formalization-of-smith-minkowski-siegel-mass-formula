import SMSFormula.RationalCliffordReflectionPairArbitraryBase

/-!
# The alignment step for quadratic Cartan--Dieudonne

Over a characteristic-zero field, two anisotropic vectors of the same
quadratic value can be aligned by one or two quadratic reflections.  Applied
to an isometry `g` and an anisotropic vector `x`, the resulting correction
composed after `g` fixes `x`; it also preserves the polar-orthogonal
hyperplane at `x`.

This is the dimension-reduction precursor for a quadratic
Cartan--Dieudonne theorem.  It does not restrict the corrected isometry
to that hyperplane or carry out induction on dimension.
-/

noncomputable section

open CliffordAlgebra

namespace CliffordAlgebra

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

def quadraticReflectionOfNeZero (v : M) (hv : Q v ≠ 0) : M ≃ₗ[K] M := by
  letI : Invertible (Q v) := invertibleOfNonzero hv
  exact quadraticReflection Q v

omit [CharZero K] in
@[simp]
theorem quadraticReflectionOfNeZero_apply (v m : M) (hv : Q v ≠ 0) :
    quadraticReflectionOfNeZero Q v hv m =
      m - ((Q v)⁻¹ * QuadraticMap.polar Q v m) • v := by
  letI : Invertible (Q v) := invertibleOfNonzero hv
  rw [quadraticReflectionOfNeZero, quadraticReflection_apply]
  rw [invOf_eq_right_inv (mul_inv_cancel₀ hv)]

omit [CharZero K] in
theorem quadraticReflectionOfNeZero_map_app (v m : M) (hv : Q v ≠ 0) :
    Q (quadraticReflectionOfNeZero Q v hv m) = Q m := by
  letI : Invertible (Q v) := invertibleOfNonzero hv
  exact quadraticReflection_map_app Q v m

def quadraticReflectionIsometryEquivOfNeZero (v : M) (hv : Q v ≠ 0) :
    Q.IsometryEquiv Q where
  toLinearEquiv := quadraticReflectionOfNeZero Q v hv
  map_app' := fun m => quadraticReflectionOfNeZero_map_app Q v m hv

omit [CharZero K] in
theorem quadraticForm_sub_add_sum (x y : M) :
    Q (y - x) + Q (y + x) = 2 * Q y + 2 * Q x := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
    QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
  ring

omit [CharZero K] in
theorem quadraticForm_sub_add_sum_of_eq (x y : M) (hxy : Q y = Q x) :
    Q (y - x) + Q (y + x) = 4 * Q x := by
  rw [quadraticForm_sub_add_sum, hxy]
  ring

theorem quadraticForm_sub_ne_zero_or_add_ne_zero
    (x y : M) (hx : Q x ≠ 0) (hxy : Q y = Q x) :
    Q (y - x) ≠ 0 ∨ Q (y + x) ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum := quadraticForm_sub_add_sum_of_eq Q x y hxy
  rw [h.1, h.2, zero_add] at hsum
  have hfour : (4 : K) ≠ 0 := by norm_num
  exact hx (mul_eq_zero.mp hsum.symm |>.resolve_left hfour)

omit [CharZero K] in
theorem polar_sub_right_eq_quadraticForm_sub
    (x y : M) (hxy : Q y = Q x) :
    QuadraticMap.polar Q (y - x) y = Q (y - x) := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self]
  conv_rhs =>
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right]
  rw [QuadraticMap.polar_comm Q x y, hxy]
  simp only [nsmul_eq_mul]
  ring

omit [CharZero K] in
theorem polar_add_right_eq_quadraticForm_add
    (x y : M) (hxy : Q y = Q x) :
    QuadraticMap.polar Q (y + x) y = Q (y + x) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self]
  rw [QuadraticMap.map_add Q, QuadraticMap.polar_comm Q x y, hxy]
  simp only [nsmul_eq_mul]
  ring

omit [CharZero K] in
theorem quadraticReflection_sub_map_right
    (x y : M) (hxy : Q y = Q x) (hsub : Q (y - x) ≠ 0) :
    quadraticReflectionOfNeZero Q (y - x) hsub y = x := by
  rw [quadraticReflectionOfNeZero_apply,
    polar_sub_right_eq_quadraticForm_sub Q x y hxy]
  rw [inv_mul_cancel₀ hsub, one_smul]
  abel

omit [CharZero K] in
theorem quadraticReflection_add_map_right
    (x y : M) (hxy : Q y = Q x) (hadd : Q (y + x) ≠ 0) :
    quadraticReflectionOfNeZero Q (y + x) hadd y = -x := by
  rw [quadraticReflectionOfNeZero_apply,
    polar_add_right_eq_quadraticForm_add Q x y hxy]
  rw [inv_mul_cancel₀ hadd, one_smul]
  abel

theorem quadraticReflection_self_map_neg
    (x : M) (hx : Q x ≠ 0) :
    quadraticReflectionOfNeZero Q x hx (-x) = x := by
  rw [quadraticReflectionOfNeZero_apply]
  rw [QuadraticMap.polar_neg_right, QuadraticMap.polar_self]
  simp only [nsmul_eq_mul]
  change -x - ((Q x)⁻¹ * -((2 : K) * Q x)) • x = x
  have hcoef : (Q x)⁻¹ * -((2 : K) * Q x) = (-2 : K) := by
    calc
      (Q x)⁻¹ * -(2 * Q x) = -2 * ((Q x)⁻¹ * Q x) := by ring
      _ = -2 := by rw [inv_mul_cancel₀ hx, mul_one]
  rw [hcoef]
  module

inductive ReflectionAlignment (x y : M) : Type _
  | one (hsub : Q (y - x) ≠ 0)
      (map_right : quadraticReflectionOfNeZero Q (y - x) hsub y = x)
  | two (hadd : Q (y + x) ≠ 0) (hx : Q x ≠ 0)
      (map_right : quadraticReflectionOfNeZero Q x hx
        (quadraticReflectionOfNeZero Q (y + x) hadd y) = x)

def reflectionAlignment (x y : M) (hx : Q x ≠ 0) (hxy : Q y = Q x) :
    ReflectionAlignment Q x y := by
  by_cases hsub : Q (y - x) = 0
  · have hadd : Q (y + x) ≠ 0 := by
      exact (quadraticForm_sub_ne_zero_or_add_ne_zero Q x y hx hxy).resolve_left
        (not_ne_iff.mpr hsub)
    exact .two hadd hx (by
      rw [quadraticReflection_add_map_right Q x y hxy hadd]
      exact quadraticReflection_self_map_neg Q x hx)
  · exact .one hsub (quadraticReflection_sub_map_right Q x y hxy hsub)

def ReflectionAlignment.correction {x y : M}
    (a : ReflectionAlignment Q x y) : Q.IsometryEquiv Q := by
  cases a with
  | one hsub _ =>
      exact quadraticReflectionIsometryEquivOfNeZero Q (y - x) hsub
  | two hadd hx _ =>
      exact (quadraticReflectionIsometryEquivOfNeZero Q (y + x) hadd).trans
        (quadraticReflectionIsometryEquivOfNeZero Q x hx)

omit [CharZero K] in
@[simp]
theorem ReflectionAlignment.correction_map_source {x y : M}
    (a : ReflectionAlignment Q x y) :
    (ReflectionAlignment.correction Q a) y = x := by
  cases a with
  | one hsub hmap => exact hmap
  | two hadd hx hmap => exact hmap

def ReflectionAlignment.length {x y : M}
    (a : ReflectionAlignment Q x y) : ℕ := by
  cases a with
  | one => exact 1
  | two => exact 2

omit [CharZero K] in
theorem ReflectionAlignment.length_pos {x y : M}
    (a : ReflectionAlignment Q x y) : 0 < a.length := by
  cases a <;> simp [length]

omit [CharZero K] in
theorem ReflectionAlignment.length_le_two {x y : M}
    (a : ReflectionAlignment Q x y) : a.length ≤ 2 := by
  cases a <;> simp [length]

end CliffordAlgebra

namespace QuadraticMap.IsometryEquiv

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

def reflectionAlignmentAt
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) :
    ReflectionAlignment Q x (g x) :=
  reflectionAlignment Q x (g x) hx (g.map_app x)

def reflectionCorrectionAt
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) : Q.IsometryEquiv Q :=
  g.trans (g.reflectionAlignmentAt Q x hx).correction

@[simp]
theorem reflectionCorrectionAt_apply_self
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) :
    g.reflectionCorrectionAt Q x hx x = x := by
  exact (g.reflectionAlignmentAt Q x hx).correction_map_source

theorem reflectionAlignmentAt_length_pos
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) :
    0 < (g.reflectionAlignmentAt Q x hx).length :=
  (g.reflectionAlignmentAt Q x hx).length_pos

theorem reflectionAlignmentAt_length_le_two
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) :
    (g.reflectionAlignmentAt Q x hx).length ≤ 2 :=
  (g.reflectionAlignmentAt Q x hx).length_le_two

omit [CharZero K] in
theorem map_polar_self
    (g : Q.IsometryEquiv Q) (x y : M) :
    QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
  unfold QuadraticMap.polar
  have hsum : g (x + y) = g x + g y := g.toLinearEquiv.map_add x y
  rw [← hsum, g.map_app, g.map_app, g.map_app]

omit [CharZero K] in
theorem map_polar_eq_zero_of_fixed
    (g : Q.IsometryEquiv Q) (x y : M) (hfix : g x = x)
    (hy : QuadraticMap.polar Q x y = 0) :
    QuadraticMap.polar Q x (g y) = 0 := by
  calc
    QuadraticMap.polar Q x (g y) =
        QuadraticMap.polar Q (g x) (g y) := by rw [hfix]
    _ = QuadraticMap.polar Q x y := g.map_polar_self Q x y
    _ = 0 := hy

theorem reflectionCorrectionAt_map_polar_eq_zero
    (g : Q.IsometryEquiv Q) (x y : M) (hx : Q x ≠ 0)
    (hy : QuadraticMap.polar Q x y = 0) :
    QuadraticMap.polar Q x (g.reflectionCorrectionAt Q x hx y) = 0 :=
  (g.reflectionCorrectionAt Q x hx).map_polar_eq_zero_of_fixed Q x y
    (g.reflectionCorrectionAt_apply_self Q x hx) hy

end QuadraticMap.IsometryEquiv
