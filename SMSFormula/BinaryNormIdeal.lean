import SMSFormula.BinaryPrimitiveDiscriminant
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# The norm ideal of a primitive binary polynomial

For Q(x,y)=ax²+bxy+cy², use the rank-two integral algebra with
θ²=bθ-ac. The ideal with basis (a,θ) has norm aQ. Primitivity gives
I conjugate(I)=(a). This uses the original polynomial coefficients and
does not assume a maximal order, an odd conductor, or an inverse of 2.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

/-- The integral coefficient presentation of the quadratic order. -/
abbrev CoefficientOrder (a b c : ℤ) := QuadraticAlgebra ℤ (-a * c) b

/-- The ideal (a,θ), described by divisibility of the real coefficient. -/
def normIdeal (a b c : ℤ) : Ideal (CoefficientOrder a b c) where
  carrier := {z | a ∣ z.re}
  zero_mem' := dvd_zero _
  add_mem' hz hw := dvd_add hz hw
  smul_mem' r z hz := by
    obtain ⟨x, hx⟩ := hz
    refine ⟨r.re * x - c * r.im * z.im, ?_⟩
    change (r * z).re = _
    simp only [QuadraticAlgebra.re_mul, hx]
    ring

/-- The conjugate ideal, in the same order and without changing the norm scale. -/
def conjugateNormIdeal (a b c : ℤ) : Ideal (CoefficientOrder a b c) where
  carrier := {z | a ∣ z.re + b * z.im}
  zero_mem' := by simp
  add_mem' {z} {w} hz hw := by
    change a ∣ (z + w).re + b * (z + w).im
    simpa only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, mul_add,
      add_add_add_comm] using dvd_add hz hw
  smul_mem' r z hz := by
    obtain ⟨x, hx⟩ := hz
    refine ⟨(r.re + b * r.im) * x - c * r.im * z.im, ?_⟩
    change (r * z).re + b * (r * z).im = _
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (r.re + b * r.im) * hx

@[simp] lemma mem_normIdeal (a b c : ℤ) (z : CoefficientOrder a b c) :
    z ∈ normIdeal a b c ↔ a ∣ z.re := Iff.rfl

@[simp] lemma mem_conjugateNormIdeal (a b c : ℤ) (z : CoefficientOrder a b c) :
    z ∈ conjugateNormIdeal a b c ↔ a ∣ z.re + b * z.im := Iff.rfl

/-- This is the conjugate ideal under the fixed algebra involution. -/
lemma mem_conjugateNormIdeal_iff_star (a b c : ℤ) (z : CoefficientOrder a b c) :
    z ∈ conjugateNormIdeal a b c ↔ star z ∈ normIdeal a b c := Iff.rfl

/-- Exact coordinates on the ideal, on the same binary integer carrier. -/
def coordinates (a b c : ℤ) (ha : a ≠ 0) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] normIdeal a b c where
  toFun x := ⟨⟨a * x 0, x 1⟩, by exact ⟨x 0, rfl⟩⟩
  invFun z := ![z.val.re / a, z.val.im]
  left_inv x := by
    ext i
    fin_cases i
    · exact Int.mul_ediv_cancel_left _ ha
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · exact Int.mul_ediv_cancel' z.prop
    · rfl
  map_add' x y := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext <;> simp [mul_add]
  map_smul' r x := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext <;> simp [mul_left_comm]

@[simp] lemma coordinates_apply (a b c : ℤ) (ha : a ≠ 0) (x : Fin 2 → ℤ) :
    (coordinates a b c ha x).val = (⟨a * x 0, x 1⟩ : CoefficientOrder a b c) := rfl

/-- The ideal norm is exactly a times the original primitive polynomial. -/
theorem norm_coordinates (a b c : ℤ) (ha : a ≠ 0) (x : Fin 2 → ℤ) :
    (coordinates a b c ha x).val.norm =
      a * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) := by
  rw [coordinates_apply, QuadraticAlgebra.norm_def]
  simp only
  ring

/-- The divisibility description is exactly the two-generator order ideal. -/
theorem normIdeal_eq_span (a b c : ℤ) :
    normIdeal a b c = Ideal.span {(a : CoefficientOrder a b c), QuadraticAlgebra.omega} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz
    have hrepr : z = (x : CoefficientOrder a b c) * (a : CoefficientOrder a b c) +
        (z.im : CoefficientOrder a b c) * QuadraticAlgebra.omega := by
      apply QuadraticAlgebra.ext <;> simp [hx, CoefficientOrder, mul_comm]
    rw [hrepr]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · change a ∣ a; exact dvd_refl _
    · obtain rfl := Set.mem_singleton_iff.mp hz
      change a ∣ 0
      exact dvd_zero _

/-- Multiplication on the ideal basis (a,θ), with no denominator in the matrix. -/
def multiplicationMatrix (a b c : ℤ) (z : CoefficientOrder a b c) :
    Matrix (Fin 2) (Fin 2) ℤ := !![z.re, -c * z.im; a * z.im, z.re + b * z.im]

/-- The matrix is the actual order multiplication on ideal coordinates. -/
lemma coordinates_multiplicationMatrix (a b c : ℤ) (ha : a ≠ 0)
    (z : CoefficientOrder a b c) (x : Fin 2 → ℤ) :
    (coordinates a b c ha ((multiplicationMatrix a b c z).mulVec x)).val =
      z * (coordinates a b c ha x).val := by
  rw [coordinates_apply, coordinates_apply]
  apply QuadraticAlgebra.ext <;>
    simp [multiplicationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Its binary determinant is the algebra norm, without a scale change. -/
lemma det_multiplicationMatrix (a b c : ℤ) (z : CoefficientOrder a b c) :
    (multiplicationMatrix a b c z).det = z.norm := by
  simp [multiplicationMatrix, Matrix.det_fin_two, QuadraticAlgebra.norm_def]
  ring

/-- Multiplication preserves the polynomial up to its exact norm multiplier. -/
lemma polynomial_multiplicationMatrix (a b c : ℤ) (ha : a ≠ 0)
    (z : CoefficientOrder a b c) (x : Fin 2 → ℤ) :
    let y := (multiplicationMatrix a b c z).mulVec x
    a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2 =
      z.norm * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) := by
  have hh := congrArg QuadraticAlgebra.norm (coordinates_multiplicationMatrix a b c ha z x)
  rw [norm_coordinates, map_mul, norm_coordinates] at hh
  apply mul_left_cancel₀ ha
  linear_combination hh

/-- The integral algebra embeds in its rational coefficient algebra. -/
def rationalMap (a b c : ℤ) :
    CoefficientOrder a b c →+* QuadraticAlgebra ℚ (-(a : ℚ) * (c : ℚ)) (b : ℚ) where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by apply QuadraticAlgebra.ext <;> norm_num [CoefficientOrder]
  map_mul' z w := by apply QuadraticAlgebra.ext <;> simp
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp

theorem rationalMap_injective (a b c : ℤ) : Function.Injective (rationalMap a b c) := by
  intro z w h
  apply QuadraticAlgebra.ext
  · have hh : (z.re : ℚ) = (w.re : ℚ) := congrArg QuadraticAlgebra.re h
    exact_mod_cast hh
  · have hh : (z.im : ℚ) = (w.im : ℚ) := congrArg QuadraticAlgebra.im h
    exact_mod_cast hh

/-- Negative discriminant makes the rational coefficient algebra a field.
The field structure is explicit; it adds no new global inference rule. -/
@[reducible] noncomputable def rationalField (a b c : ℤ) (hD : b ^ 2 - 4 * a * c < 0) :
    Field (QuadraticAlgebra ℚ (-(a : ℚ) * (c : ℚ)) (b : ℚ)) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ -(a : ℚ) * (c : ℚ) + (b : ℚ) * r) := ⟨by
    intro r hr
    have hneg : (b : ℚ) ^ 2 - 4 * (a : ℚ) * (c : ℚ) < 0 := by exact_mod_cast hD
    nlinarith [sq_nonneg (2 * r - (b : ℚ))]⟩
  infer_instance

private lemma primitive_bezout (a b c : ℤ) (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    ∃ r s t : ℤ, a * r + b * s + c * t = 1 := by
  have h1 := Int.gcd_eq_gcd_ab a (Int.gcd b c : ℤ)
  have h2 := Int.gcd_eq_gcd_ab b c
  rw [hprim] at h1
  refine ⟨Int.gcdA a (Int.gcd b c : ℤ),
    Int.gcdA b c * Int.gcdB a (Int.gcd b c : ℤ),
    Int.gcdB b c * Int.gcdB a (Int.gcd b c : ℤ), ?_⟩
  linear_combination -h1 - Int.gcdB a (Int.gcd b c : ℤ) * h2

/-- Primitivity gives the exact ideal inverse up to the nonzero leading
coefficient. This is an equality of integral ideals in the actual order. -/
theorem normIdeal_mul_conjugate (a b c : ℤ)
    (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    normIdeal a b c * conjugateNormIdeal a b c =
      Ideal.span {(a : CoefficientOrder a b c)} := by
  let O := CoefficientOrder a b c
  let I := normIdeal a b c
  let J := conjugateNormIdeal a b c
  have hIa : (a : O) ∈ I := by change a ∣ a; exact dvd_refl _
  have hJa : (a : O) ∈ J := by change a ∣ a + b * 0; simp
  have hIt : (QuadraticAlgebra.omega : O) ∈ I := by simp [I]
  have hJt : star (QuadraticAlgebra.omega : O) ∈ J := by simp [J]
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro z hz w hw
    obtain ⟨x, hx⟩ := hz
    obtain ⟨y, hy⟩ := hw
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨x * w.re - c * z.im * w.im, x * w.im + z.im * y⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · change (z * w).re = _
      simp only [QuadraticAlgebra.re_mul, hx]
      simp only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id]
      ring
    · change (z * w).im = _
      simp only [QuadraticAlgebra.im_mul]
      simp only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
      linear_combination w.im * hx + z.im * hy
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    obtain ⟨r, s, t, hbez⟩ := primitive_bezout a b c hprim
    have haa : (a : O) * (a : O) ∈ I * J := Ideal.mul_mem_mul hIa hJa
    have hab : (a : O) * (b : O) ∈ I * J := by
      have hsum := (I * J).add_mem (Ideal.mul_mem_mul hIa hJt) (Ideal.mul_mem_mul hIt hJa)
      have hid : (a : O) * star (QuadraticAlgebra.omega : O) +
          (QuadraticAlgebra.omega : O) * (a : O) = (a : O) * (b : O) := by
        apply QuadraticAlgebra.ext <;> simp [O, CoefficientOrder]
      rwa [hid] at hsum
    have hac : (a : O) * (c : O) ∈ I * J := by
      have hprod := Ideal.mul_mem_mul hIt hJt
      have hid : (QuadraticAlgebra.omega : O) * star QuadraticAlgebra.omega =
          (a : O) * (c : O) := by
        apply QuadraticAlgebra.ext <;> simp [O, CoefficientOrder]
      rwa [hid] at hprod
    have hsum := (I * J).add_mem
      ((I * J).add_mem ((I * J).mul_mem_left (r : O) haa)
        ((I * J).mul_mem_left (s : O) hab)) ((I * J).mul_mem_left (t : O) hac)
    have hid : (r : O) * ((a : O) * (a : O)) + (s : O) * ((a : O) * (b : O)) +
        (t : O) * ((a : O) * (c : O)) = (a : O) := by
      have h : (a : O) * (r : O) + (b : O) * (s : O) + (c : O) * (t : O) = 1 := by
        apply QuadraticAlgebra.ext
        · simpa [O, CoefficientOrder] using hbez
        · simp [O, CoefficientOrder]
      linear_combination (a : O) * h
    rwa [hid] at hsum

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The coefficient presentation θ²=Bθ-AC of the actual primitive norm order. -/
abbrev binaryCoefficientOrder (K : PositiveDefiniteIntegralLattice 2) :=
  BinaryNormIdeal.CoefficientOrder
    (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
    ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
    (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))

/-- The actual primitive norm ideal, with its original coordinate carrier. -/
def binaryNormIdeal (K : PositiveDefiniteIntegralLattice 2) : Ideal K.binaryCoefficientOrder :=
  BinaryNormIdeal.normIdeal
    (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
    ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
    (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))

/-- The original integer coordinates form a basis presentation of the norm ideal. -/
def binaryNormIdealCoordinates (K : PositiveDefiniteIntegralLattice 2) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] K.binaryNormIdeal :=
  BinaryNormIdeal.coordinates _ _ _ (ne_of_gt K.binaryPrimitivePolynomial_leading_pos)

/-- The ideal norm identifies the same primitive polynomial, with exact factor A. -/
theorem norm_binaryNormIdealCoordinates (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → ℤ) :
    (K.binaryNormIdealCoordinates x).val.norm =
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) * K.binaryPrimitivePolynomial x := by
  simpa only [binaryPrimitivePolynomial_apply] using
    BinaryNormIdeal.norm_coordinates _ _ _ (ne_of_gt K.binaryPrimitivePolynomial_leading_pos) x

/-- The actual primitive coefficients give I conjugate(I)=(A), over every
discriminant and content allowed by the original lattice model. -/
theorem binaryNormIdeal_mul_conjugate (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryNormIdeal * BinaryNormIdeal.conjugateNormIdeal
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
      ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
      (K.pairingMatrix 1 1 / (K.binaryContent : ℤ)) =
      Ideal.span {((K.pairingMatrix 0 0 / (K.binaryContent : ℤ) : ℤ) : K.binaryCoefficientOrder)} :=
  BinaryNormIdeal.normIdeal_mul_conjugate _ _ _ K.binaryPrimitivePolynomial_coefficients_gcd_eq_one

/-- A norm-one order unit gives an actual proper automorphism of the original
lattice, through multiplication on its primitive norm ideal. -/
noncomputable def binaryNormOneUnitToProperIsometry (K : PositiveDefiniteIntegralLattice 2)
    (u : {u : K.binaryCoefficientOrderˣ // (u.val : K.binaryCoefficientOrder).norm = 1}) :
    K.ProperIsometryGroup := by
  let a := K.pairingMatrix 0 0 / (K.binaryContent : ℤ)
  let b := (2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)
  let c := K.pairingMatrix 1 1 / (K.binaryContent : ℤ)
  let U := BinaryNormIdeal.multiplicationMatrix a b c (u.val : K.binaryCoefficientOrder)
  have hd : U.det = 1 := (BinaryNormIdeal.det_multiplicationMatrix a b c _).trans u.prop
  have hunit : IsUnit U := by rw [Matrix.isUnit_iff_isUnit_det, hd]; exact isUnit_one
  refine ⟨U, ⟨hunit, ?_⟩, hd⟩
  have hp : ∀ x, K.binaryPrimitivePolynomialOver ℤ (U.mulVec x) =
      K.binaryPrimitivePolynomialOver ℤ x := by
    intro x
    rw [binaryPrimitivePolynomialOver_int, binaryPrimitivePolynomial_apply, binaryPrimitivePolynomial_apply]
    have h := BinaryNormIdeal.polynomial_multiplicationMatrix a b c
      (ne_of_gt K.binaryPrimitivePolynomial_leading_pos) (u.val : K.binaryCoefficientOrder) x
    rw [u.prop, one_mul] at h
    exact h
  have hm := (binaryPrimitivePolynomialOver_matrix_congruence_iff K K rfl U).mpr hp
  simpa only [Int.cast_id, Matrix.map_id] using hm

/-- Distinct norm-one order units act by distinct original proper matrices. -/
theorem binaryNormOneUnitToProperIsometry_injective (K : PositiveDefiniteIntegralLattice 2) :
    Function.Injective K.binaryNormOneUnitToProperIsometry := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply QuadraticAlgebra.ext
  · have hh := congrArg (fun U : K.ProperIsometryGroup => U.val 0 0) h
    exact hh
  · have hh := congrArg (fun U : K.ProperIsometryGroup => U.val 1 0) h
    change (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) * (u.val : K.binaryCoefficientOrder).im =
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) * (v.val : K.binaryCoefficientOrder).im at hh
    exact mul_left_cancel₀ (ne_of_gt K.binaryPrimitivePolynomial_leading_pos) hh

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.CoefficientOrder
#assert_standard_axioms BinaryNormIdeal.normIdeal
#assert_standard_axioms BinaryNormIdeal.conjugateNormIdeal
#assert_standard_axioms BinaryNormIdeal.mem_normIdeal
#assert_standard_axioms BinaryNormIdeal.mem_conjugateNormIdeal
#assert_standard_axioms BinaryNormIdeal.mem_conjugateNormIdeal_iff_star
#assert_standard_axioms BinaryNormIdeal.coordinates
#assert_standard_axioms BinaryNormIdeal.coordinates_apply
#assert_standard_axioms BinaryNormIdeal.norm_coordinates
#assert_standard_axioms BinaryNormIdeal.normIdeal_eq_span
#assert_standard_axioms BinaryNormIdeal.multiplicationMatrix
#assert_standard_axioms BinaryNormIdeal.coordinates_multiplicationMatrix
#assert_standard_axioms BinaryNormIdeal.det_multiplicationMatrix
#assert_standard_axioms BinaryNormIdeal.polynomial_multiplicationMatrix
#assert_standard_axioms BinaryNormIdeal.rationalMap
#assert_standard_axioms BinaryNormIdeal.rationalMap_injective
#assert_standard_axioms BinaryNormIdeal.rationalField
#assert_standard_axioms BinaryNormIdeal.normIdeal_mul_conjugate
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCoefficientOrder
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormIdeal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormIdealCoordinates
#assert_standard_axioms PositiveDefiniteIntegralLattice.norm_binaryNormIdealCoordinates
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormIdeal_mul_conjugate
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormOneUnitToProperIsometry
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormOneUnitToProperIsometry_injective
