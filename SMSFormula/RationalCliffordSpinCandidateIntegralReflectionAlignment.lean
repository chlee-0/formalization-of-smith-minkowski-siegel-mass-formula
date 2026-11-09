import SMSFormula.RationalCliffordSpinCandidateIntegralOrthogonalComplementUnimodular

/-!
# Integral unit-reflection alignment for recursive p-adic forms

Every positive-rank symmetric unimodular form over `Z_p`, for odd `p`,
represents a unit.  A unit-norm vector defines a literal integral quadratic
reflection.  Two vectors of the same unit norm can then be aligned by one or
two such reflections, exactly as in the field Cartan--Dieudonne argument but
without leaving the integral module.

This is the alignment half of the recursive reflection-word induction.  The
restriction of the corrected isometry to the smaller complement and the
terminating induction remain separate.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

/-- Quadratic form represented by the finite-coordinate symmetric
unimodular matrix. -/
def LocalPadicIntegralUnimodularForm.quadraticForm
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) :
    QuadraticForm ℤ_[p] (Fin U.rank → ℤ_[p]) :=
  U.pairingMatrix.toQuadraticMap'

@[simp]
theorem LocalPadicIntegralUnimodularForm.quadraticForm_apply
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p]) :
    U.quadraticForm x = x ⬝ᵥ Matrix.mulVec U.pairingMatrix x := by
  simp only [LocalPadicIntegralUnimodularForm.quadraticForm,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap]
  exact Matrix.toLinearMap₂'_apply' U.pairingMatrix x x

/-- Integral vector whose value is a unit. -/
abbrev LocalPadicIntegralUnimodularForm.UnitVector
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) :=
  {x : Fin U.rank → ℤ_[p] // IsUnit (U.quadraticForm x)}

/-- Every positive-rank odd unimodular integral form represents a unit. -/
theorem LocalPadicIntegralUnimodularForm.unitVector_nonempty
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) [NeZero U.rank]
    (hpodd : p ≠ 2) : Nonempty U.UnitVector := by
  let A : Matrix (Fin U.rank) (Fin U.rank) (ZMod p) :=
    U.pairingMatrix.map PadicInt.toZMod
  have hA_symm : A.IsSymm := by
    simpa [A] using U.pairingMatrix_isSymm.map PadicInt.toZMod
  have hA_det : A.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod U.pairingMatrix.det) :=
      U.pairingMatrix_det_isUnit.map PadicInt.toZMod
    have hdet : A.det = PadicInt.toZMod U.pairingMatrix.det := by
      simpa [A] using
        (RingHom.map_det PadicInt.toZMod U.pairingMatrix).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨c, hc, r, hr⟩ :=
    exists_gramQuadraticValue_eq_ne_zero A hA_symm hA_det (by
      simpa [ZMod.ringChar_zmod_n] using hpodd)
  let w : Fin U.rank → ℤ_[p] := fun i ↦ (r i).val
  have hw_res (i : Fin U.rank) : PadicInt.toZMod (w i) = r i := by
    apply ZMod.val_injective
    simp [w]
  let q : ℤ_[p] := w ⬝ᵥ Matrix.mulVec U.pairingMatrix w
  have hq_res : PadicInt.toZMod q = c := by
    calc
      PadicInt.toZMod q = gramQuadraticValue A r := by
        simp only [q, gramQuadraticValue, dotProduct, Matrix.mulVec, A,
          Matrix.map_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_mul, hw_res]
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_mul, hw_res]
      _ = c := hr
  have hq_unit : IsUnit q := by
    by_contra hnot
    have hmem :
        q ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnot
    exact hc (hq_res ▸ hmem)
  exact ⟨⟨w, by simpa [q] using hq_unit⟩⟩

/-- Integral quadratic reflection in a unit-norm vector. -/
def LocalPadicIntegralUnimodularForm.unitReflection
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (x : U.UnitVector) :
    (Fin U.rank → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin U.rank → ℤ_[p]) := by
  letI : Invertible (U.quadraticForm x) := x.property.invertible
  exact CliffordAlgebra.quadraticReflection U.quadraticForm x

@[simp]
theorem LocalPadicIntegralUnimodularForm.quadraticForm_unitReflection
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (x : U.UnitVector)
    (y : Fin U.rank → ℤ_[p]) :
    U.quadraticForm (U.unitReflection x y) = U.quadraticForm y := by
  letI : Invertible (U.quadraticForm x) := x.property.invertible
  exact CliffordAlgebra.quadraticReflection_map_app U.quadraticForm x y

/-- A unit reflection as an integral quadratic self-isometry. -/
def LocalPadicIntegralUnimodularForm.unitReflectionIsometry
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (x : U.UnitVector) :
    U.quadraticForm.IsometryEquiv U.quadraticForm where
  toLinearEquiv := U.unitReflection x
  map_app' := U.quadraticForm_unitReflection x

/-- The sum of the difference and sum values is four times the common
quadratic value. -/
theorem LocalPadicIntegralUnimodularForm.quadraticForm_sub_add_sum_of_eq
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x) :
    U.quadraticForm (y - x) + U.quadraticForm (y + x) =
      4 * U.quadraticForm x := by
  let A := U.pairingMatrix
  have hbilin :
      x ⬝ᵥ Matrix.mulVec A y = y ⬝ᵥ Matrix.mulVec A x := by
    rw [Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul x A = Matrix.mulVec A x := by
      funext i
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [show A j i = A i j by
        exact U.pairingMatrix_isSymm.apply i j]
      ring
    rw [hvec, dotProduct_comm]
  simp only [U.quadraticForm_apply] at hxy ⊢
  change
    ((y - x) ⬝ᵥ Matrix.mulVec A (y - x)) +
        ((y + x) ⬝ᵥ Matrix.mulVec A (y + x)) =
      4 * (x ⬝ᵥ Matrix.mulVec A x)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub,
    sub_dotProduct, dotProduct_add, add_dotProduct]
  rw [hbilin, hxy]
  ring

/-- At an odd prime, equal unit values force the difference or sum value to
be a unit. -/
theorem LocalPadicIntegralUnimodularForm.isUnit_quadraticForm_sub_or_add_of_eq
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x)) :
    IsUnit (U.quadraticForm (y - x)) ∨
      IsUnit (U.quadraticForm (y + x)) := by
  have htwo : IsUnit (2 : ℤ_[p]) :=
    two_isUnit_padicInt_of_ne_two p hpodd
  have hfour : IsUnit (4 : ℤ_[p]) := by
    convert htwo.mul htwo using 1
    norm_num
  have hsum :
      IsUnit (U.quadraticForm (y - x) + U.quadraticForm (y + x)) := by
    rw [U.quadraticForm_sub_add_sum_of_eq x y hxy]
    exact hfour.mul hx
  exact isUnit_left_or_right_of_isUnit_add hsum

theorem LocalPadicIntegralUnimodularForm.polar_sub_right_eq_quadraticForm_sub
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x) :
    QuadraticMap.polar U.quadraticForm (y - x) y =
      U.quadraticForm (y - x) := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self]
  conv_rhs =>
    rw [sub_eq_add_neg, QuadraticMap.map_add U.quadraticForm,
      QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
  rw [QuadraticMap.polar_comm U.quadraticForm x y, hxy]
  simp only [nsmul_eq_mul]
  ring

theorem LocalPadicIntegralUnimodularForm.polar_add_right_eq_quadraticForm_add
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x) :
    QuadraticMap.polar U.quadraticForm (y + x) y =
      U.quadraticForm (y + x) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self]
  rw [QuadraticMap.map_add U.quadraticForm,
    QuadraticMap.polar_comm U.quadraticForm x y, hxy]
  simp only [nsmul_eq_mul]
  ring

/-- A unit reflection in `y-x` sends `y` to `x`. -/
theorem LocalPadicIntegralUnimodularForm.unitReflection_sub_map_right
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hsub : IsUnit (U.quadraticForm (y - x))) :
    U.unitReflection ⟨y - x, hsub⟩ y = x := by
  letI : Invertible (U.quadraticForm (y - x)) := hsub.invertible
  change CliffordAlgebra.quadraticReflection U.quadraticForm (y - x) y = x
  rw [CliffordAlgebra.quadraticReflection_apply,
    U.polar_sub_right_eq_quadraticForm_sub x y hxy]
  rw [invOf_mul_self, one_smul]
  abel

/-- A unit reflection in `y+x` sends `y` to `-x`. -/
theorem LocalPadicIntegralUnimodularForm.unitReflection_add_map_right
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hadd : IsUnit (U.quadraticForm (y + x))) :
    U.unitReflection ⟨y + x, hadd⟩ y = -x := by
  letI : Invertible (U.quadraticForm (y + x)) := hadd.invertible
  change CliffordAlgebra.quadraticReflection U.quadraticForm (y + x) y = -x
  rw [CliffordAlgebra.quadraticReflection_apply,
    U.polar_add_right_eq_quadraticForm_add x y hxy]
  rw [invOf_mul_self, one_smul]
  abel

/-- Reflection in a unit vector sends its negative back to itself. -/
theorem LocalPadicIntegralUnimodularForm.unitReflection_self_map_neg
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : Fin U.rank → ℤ_[p])
    (hx : IsUnit (U.quadraticForm x)) :
    U.unitReflection ⟨x, hx⟩ (-x) = x := by
  letI : Invertible (U.quadraticForm x) := hx.invertible
  change CliffordAlgebra.quadraticReflection U.quadraticForm x (-x) = x
  rw [CliffordAlgebra.quadraticReflection_apply,
    QuadraticMap.polar_neg_right, QuadraticMap.polar_self]
  simp only [nsmul_eq_mul]
  change -x - (⅟(U.quadraticForm x) *
      -((2 : ℤ_[p]) * U.quadraticForm x)) • x = x
  have hcoef :
      ⅟(U.quadraticForm x) * -((2 : ℤ_[p]) * U.quadraticForm x) = -2 := by
    calc
      ⅟(U.quadraticForm x) * -(2 * U.quadraticForm x) =
          -2 * (⅟(U.quadraticForm x) * U.quadraticForm x) := by ring
      _ = -2 := by rw [invOf_mul_self, mul_one]
  rw [hcoef]
  module

/-- Integral one- or two-reflection alignment of two equal unit-value
vectors. -/
inductive LocalPadicIntegralUnimodularForm.ReflectionAlignment
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x y : Fin U.rank → ℤ_[p]) : Type
  | one (hsub : IsUnit (U.quadraticForm (y - x)))
  | two (hadd : IsUnit (U.quadraticForm (y + x)))
      (hx : IsUnit (U.quadraticForm x))

/-- Choose the integral alignment supplied by the odd-prime unit
alternative. -/
def LocalPadicIntegralUnimodularForm.reflectionAlignment
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (x y : Fin U.rank → ℤ_[p])
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (hx : IsUnit (U.quadraticForm x)) :
    U.ReflectionAlignment x y := by
  classical
  by_cases hsub : IsUnit (U.quadraticForm (y - x))
  · exact .one hsub
  · exact .two
      ((U.isUnit_quadraticForm_sub_or_add_of_eq hpodd x y hxy hx).resolve_left
        hsub) hx

/-- Integral correction isometry attached to an alignment. -/
def LocalPadicIntegralUnimodularForm.ReflectionAlignment.correction
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) :
    U.quadraticForm.IsometryEquiv U.quadraticForm := by
  cases a with
  | one hsub =>
      exact U.unitReflectionIsometry ⟨y - x, hsub⟩
  | two hadd hx =>
      exact (U.unitReflectionIsometry ⟨y + x, hadd⟩).trans
        (U.unitReflectionIsometry ⟨x, hx⟩)

@[simp]
theorem LocalPadicIntegralUnimodularForm.ReflectionAlignment.correction_map_source
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (hxy : U.quadraticForm y = U.quadraticForm x)
    (a : U.ReflectionAlignment x y) :
    a.correction y = x := by
  cases a with
  | one hsub =>
      exact U.unitReflection_sub_map_right x y hxy hsub
  | two hadd hx =>
      change U.unitReflection ⟨x, hx⟩
        (U.unitReflection ⟨y + x, hadd⟩ y) = x
      rw [U.unitReflection_add_map_right x y hxy hadd]
      exact U.unitReflection_self_map_neg x hx

/-- Number of integral reflections in an alignment. -/
def LocalPadicIntegralUnimodularForm.ReflectionAlignment.length
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) : ℕ := by
  cases a with
  | one => exact 1
  | two => exact 2

theorem LocalPadicIntegralUnimodularForm.ReflectionAlignment.length_pos
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) : 0 < a.length := by
  cases a <;> simp [LocalPadicIntegralUnimodularForm.ReflectionAlignment.length]

theorem LocalPadicIntegralUnimodularForm.ReflectionAlignment.length_le_two
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) : a.length ≤ 2 := by
  cases a <;> simp [LocalPadicIntegralUnimodularForm.ReflectionAlignment.length]

/-- A word of integral unit-norm reflection vectors. -/
abbrev LocalPadicIntegralUnimodularForm.UnitReflectionWord
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) := List U.UnitVector

/-- Evaluate integral unit reflections from left to right. -/
def LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) :
    U.UnitReflectionWord → U.quadraticForm.IsometryEquiv U.quadraticForm
  | [] => .refl U.quadraticForm
  | x :: xs => (U.unitReflectionIsometry x).trans (eval U xs)

@[simp]
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_nil
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U [] =
      .refl U.quadraticForm := rfl

@[simp]
theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (x : U.UnitVector) (xs : U.UnitReflectionWord) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U (x :: xs) =
      (U.unitReflectionIsometry x).trans
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U xs) := rfl

theorem LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_append
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (xs ys : U.UnitReflectionWord) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U (xs ++ ys) =
      (LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U xs).trans
        (LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append,
        LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval_cons, ih]
      apply DFunLike.coe_injective
      funext y
      rfl

/-- Reflection word evaluating to the inverse of the alignment correction. -/
def LocalPadicIntegralUnimodularForm.ReflectionAlignment.inverseWord
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) : U.UnitReflectionWord := by
  cases a with
  | one hsub => exact [⟨y - x, hsub⟩]
  | two hadd hx => exact [⟨x, hx⟩, ⟨y + x, hadd⟩]

@[simp]
theorem LocalPadicIntegralUnimodularForm.ReflectionAlignment.length_inverseWord
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) : a.inverseWord.length = a.length := by
  cases a <;> rfl

theorem LocalPadicIntegralUnimodularForm.ReflectionAlignment.eval_inverseWord
    {p : ℕ} [Fact p.Prime]
    {U : LocalPadicIntegralUnimodularForm p}
    {x y : Fin U.rank → ℤ_[p]}
    (a : U.ReflectionAlignment x y) :
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U a.inverseWord =
      a.correction.symm := by
  cases a <;>
    apply DFunLike.coe_injective <;>
    funext z <;>
    rfl

/-- An integral isometry is generated by unit reflections when it is the
evaluation of an integral unit-reflection word. -/
def LocalPadicIntegralUnimodularForm.IsGeneratedByUnitReflections
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm) : Prop :=
  ∃ xs : U.UnitReflectionWord,
    LocalPadicIntegralUnimodularForm.UnitReflectionWord.eval U xs = g

/-- Rank-zero integral isometries are generated by the empty reflection
word. -/
theorem LocalPadicIntegralUnimodularForm.isGeneratedByUnitReflections_of_rank_eq_zero
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (hzero : U.rank = 0) : U.IsGeneratedByUnitReflections g := by
  refine ⟨[], ?_⟩
  apply DFunLike.coe_injective
  funext x
  haveI : Subsingleton (Fin U.rank → ℤ_[p]) := by
    rw [hzero]
    infer_instance
  exact Subsingleton.elim _ _

/-- Alignment selected at a unit vector for an integral quadratic
self-isometry. -/
def LocalPadicIntegralUnimodularForm.reflectionAlignmentAt
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (x : U.UnitVector) : U.ReflectionAlignment x (g x) :=
  U.reflectionAlignment hpodd x (g x) (g.map_app x) x.property

/-- Compose an integral isometry with its reflection correction. -/
def LocalPadicIntegralUnimodularForm.reflectionCorrectionAt
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (x : U.UnitVector) :
    U.quadraticForm.IsometryEquiv U.quadraticForm :=
  g.trans (U.reflectionAlignmentAt hpodd g x).correction

@[simp]
theorem LocalPadicIntegralUnimodularForm.reflectionCorrectionAt_apply_self
    {p : ℕ} [Fact p.Prime]
    (U : LocalPadicIntegralUnimodularForm p) (hpodd : p ≠ 2)
    (g : U.quadraticForm.IsometryEquiv U.quadraticForm)
    (x : U.UnitVector) :
    U.reflectionCorrectionAt hpodd g x x = x := by
  exact (U.reflectionAlignmentAt hpodd g x).correction_map_source
    (g.map_app x)

end PositiveDefiniteIntegralLattice
