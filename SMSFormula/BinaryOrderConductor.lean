import SMSFormula.BinaryOrderIndex

/-!
# The conductor of the original quadratic order

An integer basis containing one identifies the original order image with
the integers plus its actual quotient index times the maximal order.
-/

namespace BinaryNormIdeal

open Module

/-- The coordinates of one in any rank-two integer algebra basis are
coprime. The integral norm excludes a nontrivial common integer divisor. -/
theorem gcd_basis_one {B : Type*} [CommRing B] [Nontrivial B]
    (e : Basis (Fin 2) ℤ B) : Int.gcd (e.repr 1 0) (e.repr 1 1) = 1 := by
  letI := Module.Free.of_basis e
  letI := Module.Finite.of_basis e
  let d := Int.gcd (e.repr 1 0) (e.repr 1 1)
  obtain ⟨x,hx⟩ := Int.gcd_dvd_left (e.repr 1 0) (e.repr 1 1)
  obtain ⟨y,hy⟩ := Int.gcd_dvd_right (e.repr 1 0) (e.repr 1 1)
  have hz : (d : B) * (x • e 0 + y • e 1) = 1 := by
    calc
      _ = (d : ℤ) • (x • e 0 + y • e 1) := by simp only [zsmul_eq_mul,Int.cast_natCast,mul_add]
      _ = (e.repr 1 0) • e 0 + (e.repr 1 1) • e 1 := by
        rw [smul_add,smul_smul,smul_smul,← hx,← hy]
      _ = 1 := by simpa [Fin.sum_univ_two] using e.sum_repr 1
  have hn := congrArg (Algebra.norm ℤ) hz
  simp only [map_mul,Algebra.norm_natCast,Module.finrank_eq_card_basis e,Fintype.card_fin,
    map_one] at hn
  have hd : (d : ℤ) ∣ 1 := ⟨(d : ℤ) * Algebra.norm ℤ (x • e 0 + y • e 1), by
    nlinarith only [hn]⟩
  exact Nat.dvd_one.mp (by exact_mod_cast hd)

/-- Every rank-two integer algebra has a basis whose first vector is one. -/
theorem exists_basis_one {B : Type*} [CommRing B] [Nontrivial B]
    (e : Basis (Fin 2) ℤ B) : ∃ f : Basis (Fin 2) ℤ B, f 0 = 1 := by
  let u := e.repr 1 0
  let v := e.repr 1 1
  have hbez : u * Int.gcdA u v + v * Int.gcdB u v = 1 := by
    rw [← Int.gcd_eq_gcd_ab, gcd_basis_one e]
    rfl
  let P : Matrix (Fin 2) (Fin 2) ℤ := !![u,-Int.gcdB u v;v,Int.gcdA u v]
  have hP : IsUnit P.det := by
    convert isUnit_one (M := ℤ) using 1
    simp only [P,Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
    nlinarith only [hbez]
  refine ⟨e.map (Matrix.toLinearEquiv e P hP), ?_⟩
  apply e.repr.injective
  ext i
  fin_cases i <;> simp [Basis.map_apply,Matrix.toLinearEquiv_apply,
    Matrix.toLin_apply,Matrix.mulVec,Fin.sum_univ_two,P,u,v, -zsmul_eq_mul]

/-- In bases beginning with one, the second coordinate detects the actual
additive index. Both lattices and the quotient are the original carriers. -/
theorem mem_iff_index_dvd_coordinate {B : Type*} [CommRing B]
    (e : Basis (Fin 2) ℤ B) (he : e 0 = 1)
    (N : Submodule ℤ B) (f : Basis (Fin 2) ℤ N) (hf : (f 0 : B) = 1) (z : B) :
    z ∈ N ↔ (Nat.card (B ⧸ N) : ℤ) ∣ e.repr z 1 := by
  letI := Module.Free.of_basis e
  letI := Module.Finite.of_basis e
  let s := e.repr (f 1 : B) 1
  have hrepr : e.repr (f 0 : B) = Finsupp.single 0 1 := by rw [hf,← he]; simp
  have hdet : e.det (fun i => (f i : B)) = s := by
    rw [Basis.det_apply,Matrix.det_fin_two]
    simp [Basis.toMatrix_apply,hrepr,s]
  have hindex : Nat.card (B ⧸ N) = s.natAbs := by
    rw [← Submodule.natAbs_det_basis_change e N f]
    change (e.det (fun i => (f i : B))).natAbs = s.natAbs
    rw [hdet]
  rw [hindex,Int.natCast_natAbs,abs_dvd]
  constructor
  · intro hz
    refine ⟨f.repr ⟨z,hz⟩ 1, ?_⟩
    have hsum : (f.repr ⟨z,hz⟩ 0) • (f 0 : B) +
        (f.repr ⟨z,hz⟩ 1) • (f 1 : B) = z := by
      exact congrArg (fun w : N => (w : B))
        (by simpa only [Fin.sum_univ_two] using f.sum_repr ⟨z,hz⟩)
    have h := congrArg (fun w : B => e.repr w 1) hsum
    simpa [hrepr,s,mul_comm,-zsmul_eq_mul] using h.symm
  · rintro ⟨y,hy⟩
    let w : N := (e.repr z 0 - y * e.repr (f 1 : B) 0) • f 0 + y • f 1
    have hw : (w : B) = z := by
      apply e.repr.injective
      ext i
      fin_cases i <;> simp [w,hrepr,hy,s,mul_comm,-zsmul_eq_mul]
    exact hw ▸ w.property

/-- A unital rank-two lattice is the integers plus its actual index times
the ambient integer algebra. No maximality or conductor premise is used. -/
theorem mem_iff_int_add_index_mul {B : Type*} [CommRing B]
    (e : Basis (Fin 2) ℤ B) (he : e 0 = 1)
    (N : Submodule ℤ B) (f : Basis (Fin 2) ℤ N) (hf : (f 0 : B) = 1) (z : B) :
    z ∈ N ↔ ∃ m : ℤ, ∃ w : B, z = (m : B) + (Nat.card (B ⧸ N) : B) * w := by
  have hrepr : e.repr (1 : B) = Finsupp.single 0 1 := by rw [← he]; simp
  rw [mem_iff_index_dvd_coordinate e he N f hf]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨e.repr z 0, y • e 1, ?_⟩
    apply e.repr.injective
    have hm (m : ℤ) : (m : B) = m • (1 : B) := by simp [zsmul_eq_mul]
    have hmul (w : B) : (Nat.card (B ⧸ N) : B) * w =
        (Nat.card (B ⧸ N) : ℤ) • w := by simp [zsmul_eq_mul]
    rw [hm,hmul]
    ext i
    fin_cases i <;>
      simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,Basis.repr_self,hrepr] <;>
      norm_num [hy]
  · rintro ⟨m,w,rfl⟩
    refine ⟨e.repr w 1, ?_⟩
    have hm : (m : B) = m • (1 : B) := by simp [zsmul_eq_mul]
    have hmul : (Nat.card (B ⧸ N) : B) * w =
        (Nat.card (B ⧸ N) : ℤ) • w := by simp [zsmul_eq_mul]
    rw [hm,hmul]
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,hrepr]
    norm_num

/-- The conductor is the actual ambient ideal of all multipliers that send
the whole ambient ring into the given integer submodule. -/
def conductorOfSubmodule {B : Type*} [CommRing B] (N : Submodule ℤ B) : Ideal B where
  carrier := {x | ∀ y : B, x*y ∈ N}
  zero_mem' := by intro y; simp
  add_mem' := by intro x y hx hy z; simpa [add_mul] using N.add_mem (hx z) (hy z)
  smul_mem' := by
    intro r x hx y
    simpa [smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hx (r*y)

/-- The conductor of a unital rank-two lattice is its actual index times
the ambient ring, proved by testing the second basis vector. -/
theorem conductorOfSubmodule_eq_span_index {B : Type*} [CommRing B]
    (e : Basis (Fin 2) ℤ B) (he : e 0 = 1)
    (N : Submodule ℤ B) (f : Basis (Fin 2) ℤ N) (hf : (f 0 : B) = 1) :
    conductorOfSubmodule N = Ideal.span {(Nat.card (B ⧸ N) : B)} := by
  have hcoord := mem_iff_index_dvd_coordinate e he N f hf
  have hnormal := mem_iff_int_add_index_mul e he N f hf
  ext x
  constructor
  · intro hx
    have hxN : x ∈ N := by simpa using hx 1
    obtain ⟨m,w,hxrep⟩ := (hnormal x).mp hxN
    have htest := (hcoord (x * e 1)).mp (hx (e 1))
    have hmul : (Nat.card (B ⧸ N) : B) * (w * e 1) =
        (Nat.card (B ⧸ N) : ℤ) • (w * e 1) := by simp [zsmul_eq_mul]
    have hm : (m : B) * e 1 = m • e 1 := by simp [zsmul_eq_mul]
    rw [hxrep,add_mul,mul_assoc,hm,hmul] at htest
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,Basis.repr_self] at htest
    have hmdiv : (Nat.card (B ⧸ N) : ℤ) ∣ m := by
      have hh : (Nat.card (B ⧸ N) : ℤ) ∣
          m + (Nat.card (B ⧸ N) : ℤ) * e.repr (w * e 1) 1 := by
        simpa using htest
      convert dvd_sub hh (dvd_mul_right (Nat.card (B ⧸ N) : ℤ)
        (e.repr (w * e 1) 1)) using 1
      ring
    obtain ⟨k,hk⟩ := hmdiv
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(k : B)+w, ?_⟩
    rw [hxrep,hk]
    simp only [Int.cast_mul,Int.cast_natCast,mul_add]
  · intro hx y
    obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp hx
    apply (hnormal (x*y)).mpr
    refine ⟨0,w*y,?_⟩
    simp only [Int.cast_zero,zero_add,hw,mul_assoc]

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- A basis of the same maximal order beginning with one. -/
noncomputable def maximalOrderBasisOne (hD : b^2-4*a*c < 0) :
    letI := fractionNumberField a b c hD
    Basis (Fin 2) ℤ (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :=
  Classical.choose (exists_basis_one (maximalOrderBasis a b c hD))

theorem maximalOrderBasisOne_zero (hD : b^2-4*a*c < 0) :
    maximalOrderBasisOne a b c hD 0 = 1 :=
  Classical.choose_spec (exists_basis_one (maximalOrderBasis a b c hD))

/-- Actual original order membership is divisibility by its actual index. -/
theorem mem_orderImage_iff_index_dvd (hD : b^2-4*a*c < 0)
    (z : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :
    z ∈ orderImage a b c ↔
      (orderIndex a b c : ℤ) ∣ (maximalOrderBasisOne a b c hD).repr z 1 := by
  letI := fractionNumberField a b c hD
  apply mem_iff_index_dvd_coordinate _ (maximalOrderBasisOne_zero a b c hD)
    _ (orderImageBasis a b c)
  rw [orderImageBasis_coe]
  convert (orderToRingOfIntegers a b c).map_one using 2
  simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
  rfl

/-- The original order is exactly Z plus its already defined positive
quotient index times the same maximal order. -/
theorem mem_orderImage_iff_int_add_index_mul (hD : b^2-4*a*c < 0)
    (z : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :
    z ∈ orderImage a b c ↔ ∃ m : ℤ, ∃ w,
      z = (m : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) +
        (orderIndex a b c : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) * w := by
  letI := fractionNumberField a b c hD
  apply mem_iff_int_add_index_mul _ (maximalOrderBasisOne_zero a b c hD)
    _ (orderImageBasis a b c)
  rw [orderImageBasis_coe]
  convert (orderToRingOfIntegers a b c).map_one using 2
  simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
  rfl

/-- The actual conductor of the original image in the same maximal order. -/
noncomputable def orderConductor : Ideal (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c))) :=
  conductorOfSubmodule (orderImage a b c)

/-- The literal conductor equals the ideal generated by the actual positive
quotient index, including dyadic and nonmaximal orders. -/
theorem orderConductor_eq_span_index (hD : b^2-4*a*c < 0) :
    orderConductor a b c =
      Ideal.span {(orderIndex a b c : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))} := by
  letI := fractionNumberField a b c hD
  apply conductorOfSubmodule_eq_span_index _ (maximalOrderBasisOne_zero a b c hD)
    _ (orderImageBasis a b c)
  rw [orderImageBasis_coe]
  convert (orderToRingOfIntegers a b c).map_one using 2
  simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
  rfl

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The literal conductor of K's original discriminant order inside the
maximal order of the same quadratic field. -/
noncomputable def binaryOrderConductor (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Ideal (NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderConductor 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)

theorem binaryOrderConductor_eq_span_index (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryOrderConductor = Ideal.span {(K.binaryOrderIndex :
      NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))} := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact orderConductor_eq_span_index _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- Original content does not change the discriminant order. Its actual
image is Z plus its positive quotient index times the same maximal order. -/
theorem mem_binaryOrderImage_iff_int_add_index_mul (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∀ z : NumberField.RingOfIntegers (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)),
      z ∈ orderImage 1 (K.binaryPrimitiveDiscriminant%2)
        (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ↔
      ∃ m : ℤ, ∃ w, z = (m : _) + (K.binaryOrderIndex : _) * w := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact mem_orderImage_iff_int_add_index_mul _ _ _ K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.gcd_basis_one
#assert_standard_axioms BinaryNormIdeal.exists_basis_one
#assert_standard_axioms BinaryNormIdeal.mem_iff_index_dvd_coordinate
#assert_standard_axioms BinaryNormIdeal.maximalOrderBasisOne
#assert_standard_axioms BinaryNormIdeal.maximalOrderBasisOne_zero
#assert_standard_axioms BinaryNormIdeal.mem_orderImage_iff_index_dvd
#assert_standard_axioms BinaryNormIdeal.mem_iff_int_add_index_mul
#assert_standard_axioms BinaryNormIdeal.conductorOfSubmodule
#assert_standard_axioms BinaryNormIdeal.conductorOfSubmodule_eq_span_index
#assert_standard_axioms BinaryNormIdeal.mem_orderImage_iff_int_add_index_mul
#assert_standard_axioms BinaryNormIdeal.orderConductor
#assert_standard_axioms BinaryNormIdeal.orderConductor_eq_span_index
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderConductor
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderConductor_eq_span_index
#assert_standard_axioms PositiveDefiniteIntegralLattice.mem_binaryOrderImage_iff_int_add_index_mul
