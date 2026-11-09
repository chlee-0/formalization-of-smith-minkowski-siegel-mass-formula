import SMSFormula.RationalCliffordSpinCandidateAffineScheme
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Clifford operations on the finite rational coordinate base change

For an arbitrary commutative rational algebra `A`, this file puts the grade
involution and reverse anti-involution on

```text
A ⊗[ℚ] CliffordAlgebra V.quadraticForm.
```

The reverse is proved anti-multiplicative directly by tensor induction.  The
finite coordinate basis also gives a faithful left-regular matrix
representation.  Since matrices over a commutative ring are Dedekind finite,
the base-changed Clifford algebra is Dedekind finite as well.  Consequently
the one-sided norm equation used by the affine Spin candidate really makes
`reverse(x)` a two-sided inverse over every commutative rational algebra.

This is the operation and inverse precursor for the candidate group law.  It
does not bundle candidate points as a group or construct a group scheme.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

abbrev cliffordCoordinateBaseChangeAlgebra :=
  A ⊗[ℚ] CliffordAlgebra V.quadraticForm

def cliffordCoordinateBaseChangeInvolute :
    V.cliffordCoordinateBaseChangeAlgebra A →ₐ[A]
      V.cliffordCoordinateBaseChangeAlgebra A :=
  Algebra.TensorProduct.map (AlgHom.id A A)
    (CliffordAlgebra.involute :
      CliffordAlgebra V.quadraticForm →ₐ[ℚ]
        CliffordAlgebra V.quadraticForm)

@[simp]
theorem cliffordCoordinateBaseChangeInvolute_tmul
    (a : A) (x : CliffordAlgebra V.quadraticForm) :
    V.cliffordCoordinateBaseChangeInvolute A (a ⊗ₜ[ℚ] x) =
      a ⊗ₜ[ℚ] CliffordAlgebra.involute x := by
  simp [cliffordCoordinateBaseChangeInvolute]

def cliffordCoordinateBaseChangeReverse :
    V.cliffordCoordinateBaseChangeAlgebra A →ₗ[A]
      V.cliffordCoordinateBaseChangeAlgebra A :=
  (CliffordAlgebra.reverse :
    CliffordAlgebra V.quadraticForm →ₗ[ℚ]
      CliffordAlgebra V.quadraticForm).baseChange A

@[simp]
theorem cliffordCoordinateBaseChangeReverse_tmul
    (a : A) (x : CliffordAlgebra V.quadraticForm) :
    V.cliffordCoordinateBaseChangeReverse A (a ⊗ₜ[ℚ] x) =
      a ⊗ₜ[ℚ] CliffordAlgebra.reverse x := by
  exact LinearMap.baseChange_tmul _ _ _

@[simp]
theorem cliffordCoordinateBaseChangeReverse_zero :
    V.cliffordCoordinateBaseChangeReverse A 0 = 0 :=
  map_zero _

@[simp]
theorem cliffordCoordinateBaseChangeReverse_add
    (x y : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeReverse A (x + y) =
      V.cliffordCoordinateBaseChangeReverse A x +
        V.cliffordCoordinateBaseChangeReverse A y :=
  map_add _ _ _

@[simp]
theorem cliffordCoordinateBaseChangeReverse_one :
    V.cliffordCoordinateBaseChangeReverse A 1 = 1 := by
  change V.cliffordCoordinateBaseChangeReverse A
      (1 ⊗ₜ[ℚ] (1 : CliffordAlgebra V.quadraticForm)) = 1
  rw [V.cliffordCoordinateBaseChangeReverse_tmul]
  rw [CliffordAlgebra.reverse.map_one]
  rfl

theorem cliffordCoordinateBaseChangeReverse_mul
    (x y : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeReverse A (x * y) =
      V.cliffordCoordinateBaseChangeReverse A y *
        V.cliffordCoordinateBaseChangeReverse A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [add_mul, map_add, hx, hy, mul_add]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [mul_add, map_add, hy, hz, add_mul]
      | tmul b y =>
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            V.cliffordCoordinateBaseChangeReverse_tmul,
            V.cliffordCoordinateBaseChangeReverse_tmul,
            V.cliffordCoordinateBaseChangeReverse_tmul,
            CliffordAlgebra.reverse.map_mul,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_comm a b]

@[simp]
theorem cliffordCoordinateBaseChangeReverse_reverse
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeReverse A
        (V.cliffordCoordinateBaseChangeReverse A x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [V.cliffordCoordinateBaseChangeReverse_tmul,
        V.cliffordCoordinateBaseChangeReverse_tmul,
        CliffordAlgebra.reverse_reverse]

theorem cliffordCoordinateBaseChangeReverse_involute
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeReverse A
        (V.cliffordCoordinateBaseChangeInvolute A x) =
      V.cliffordCoordinateBaseChangeInvolute A
        (V.cliffordCoordinateBaseChangeReverse A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [V.cliffordCoordinateBaseChangeInvolute_tmul,
        V.cliffordCoordinateBaseChangeReverse_tmul,
        V.cliffordCoordinateBaseChangeReverse_tmul,
        V.cliffordCoordinateBaseChangeInvolute_tmul,
        CliffordAlgebra.reverse_involute]

@[simp]
theorem cliffordCoordinateBaseChangeInvolute_involute
    (x : V.cliffordCoordinateBaseChangeAlgebra A) :
    V.cliffordCoordinateBaseChangeInvolute A
        (V.cliffordCoordinateBaseChangeInvolute A x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [V.cliffordCoordinateBaseChangeInvolute_tmul,
        V.cliffordCoordinateBaseChangeInvolute_tmul]
      simp

theorem cliffordCoordinateBaseChangeBasis_involute_eq_sum
    (s : Finset (Fin n)) :
    V.cliffordCoordinateBaseChangeInvolute A
        (V.cliffordCoordinateBaseChangeBasis A s) =
      ∑ u, V.cliffordInvoluteStructureConstant s u •
        V.cliffordCoordinateBaseChangeBasis A u := by
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    V.cliffordCoordinateBaseChangeInvolute_tmul,
    V.cliffordCoordinateBasis_involute_eq_sum]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    Algebra.smul_def, ← TensorProduct.tmul_smul]
  congr 1

theorem cliffordCoordinateBaseChangeBasis_reverse_eq_sum
    (s : Finset (Fin n)) :
    V.cliffordCoordinateBaseChangeReverse A
        (V.cliffordCoordinateBaseChangeBasis A s) =
      ∑ u, V.cliffordReverseStructureConstant s u •
        V.cliffordCoordinateBaseChangeBasis A u := by
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    V.cliffordCoordinateBaseChangeReverse_tmul,
    V.cliffordCoordinateBasis_reverse_eq_sum]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [V.cliffordCoordinateBaseChangeBasis_apply,
    Algebra.smul_def, ← TensorProduct.tmul_smul]
  congr 1

def cliffordCoordinateBaseChangeLeftRegularMatrix :
    V.cliffordCoordinateBaseChangeAlgebra A →ₐ[A]
      Matrix (Finset (Fin n)) (Finset (Fin n)) A :=
  (LinearMap.toMatrixAlgEquiv
      (V.cliffordCoordinateBaseChangeBasis A)).toAlgHom.comp
    (Algebra.lsmul A A (V.cliffordCoordinateBaseChangeAlgebra A))

theorem cliffordCoordinateBaseChangeLeftRegularMatrix_injective :
    Function.Injective (V.cliffordCoordinateBaseChangeLeftRegularMatrix A) := by
  intro x y hxy
  have hlinear :
      (Algebra.lsmul A A (V.cliffordCoordinateBaseChangeAlgebra A)) x =
        (Algebra.lsmul A A (V.cliffordCoordinateBaseChangeAlgebra A)) y :=
    (LinearMap.toMatrixAlgEquiv
      (V.cliffordCoordinateBaseChangeBasis A)).injective hxy
  have hone := LinearMap.congr_fun hlinear 1
  simpa using hone

noncomputable instance cliffordCoordinateBaseChange_isDedekindFiniteMonoid :
    IsDedekindFiniteMonoid (V.cliffordCoordinateBaseChangeAlgebra A) :=
  IsDedekindFiniteMonoid.of_injective
    (V.cliffordCoordinateBaseChangeLeftRegularMatrix A)
    (V.cliffordCoordinateBaseChangeLeftRegularMatrix_injective A)

theorem cliffordCoordinateBaseChange_reverse_mul_eq_one_of_mul_reverse_eq_one
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (h : x * V.cliffordCoordinateBaseChangeReverse A x = 1) :
    V.cliffordCoordinateBaseChangeReverse A x * x = 1 :=
  mul_eq_one_symm h

theorem cliffordCoordinateBaseChange_isUnit_of_mul_reverse_eq_one
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (h : x * V.cliffordCoordinateBaseChangeReverse A x = 1) :
    IsUnit x :=
  IsUnit.of_mul_eq_one (V.cliffordCoordinateBaseChangeReverse A x) h

def cliffordCoordinateBaseChangeUnitOfMulReverseEqOne
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (h : x * V.cliffordCoordinateBaseChangeReverse A x = 1) :
    (V.cliffordCoordinateBaseChangeAlgebra A)ˣ :=
  Units.mkOfMulEqOne x (V.cliffordCoordinateBaseChangeReverse A x) h

@[simp]
theorem cliffordCoordinateBaseChangeUnitOfMulReverseEqOne_val
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (h : x * V.cliffordCoordinateBaseChangeReverse A x = 1) :
    ↑(V.cliffordCoordinateBaseChangeUnitOfMulReverseEqOne A x h) = x :=
  rfl

@[simp]
theorem cliffordCoordinateBaseChangeUnitOfMulReverseEqOne_inv_val
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (h : x * V.cliffordCoordinateBaseChangeReverse A x = 1) :
    ↑((V.cliffordCoordinateBaseChangeUnitOfMulReverseEqOne A x h)⁻¹) =
      V.cliffordCoordinateBaseChangeReverse A x :=
  rfl

end RationalQuadraticSpaceMatrix
