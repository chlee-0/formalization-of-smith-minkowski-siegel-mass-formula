import SMSFormula.BinaryConductorResidueRing

/-!
# Actual quadratic coordinates for maximal-order residues

A basis beginning with one gives a quadratic presentation of the same
maximal order. Reduction uses the actual scalar ideal, including modulus one.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

section BasisModel

variable {B : Type*} [CommRing B] (e : Module.Basis (Fin 2) ℤ B)

/-- The constant coefficient of the actual square of the second basis vector. -/
noncomputable def basisSquareConstant : ℤ := e.repr (e 1*e 1) 0

/-- The linear coefficient of the actual square of the second basis vector. -/
noncomputable def basisSquareTrace : ℤ := e.repr (e 1*e 1) 1

theorem basis_expansion (he : e 0=1) (z : B) : z=e.repr z 0 • (1 : B)+e.repr z 1 • e 1 := by
  simpa [Fin.sum_univ_two,he] using (e.sum_repr z).symm

/-- The original basis determines an integral quadratic algebra equivalence. -/
noncomputable def basisQuadraticEquiv (he : e 0=1) :
    QuadraticAlgebra ℤ (basisSquareConstant e) (basisSquareTrace e) ≃ₐ[ℤ] B := by
  let f := QuadraticAlgebra.lift (R := ℤ) ⟨e 1,basis_expansion e he (e 1*e 1)⟩
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    change x.re • (1 : B)+x.im • e 1=y.re • (1 : B)+y.im • e 1 at h
    rw [← he] at h
    have hr := congrArg (fun z => e.repr z 0) h
    have hi := congrArg (fun z => e.repr z 1) h
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self] at hr hi
    apply QuadraticAlgebra.ext
    · simpa using hr
    · simpa using hi
  · intro z
    exact ⟨⟨e.repr z 0,e.repr z 1⟩,(basis_expansion e he z).symm⟩

/-- The coordinate map keeps the original integral action. -/
theorem basisQuadraticEquiv_apply (he : e 0=1)
    (z : QuadraticAlgebra ℤ (basisSquareConstant e) (basisSquareTrace e)) :
    basisQuadraticEquiv e he z=z.re • (1 : B)+z.im • e 1 := rfl

end BasisModel

/-- Literal coefficient reduction, with no inverse of two or discriminant. -/
def quadraticResidueHom (A T : ℤ) (n : ℕ) :
    QuadraticAlgebra ℤ A T →+* QuadraticAlgebra (ZMod n) (A : ZMod n) (T : ZMod n) where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem quadraticResidueHom_surjective (A T : ℤ) (n : ℕ) :
    Function.Surjective (quadraticResidueHom A T n) := by
  intro z
  obtain ⟨x,hx⟩ := ZMod.intCast_surjective z.re
  obtain ⟨y,hy⟩ := ZMod.intCast_surjective z.im
  refine ⟨⟨x,y⟩,?_⟩
  apply QuadraticAlgebra.ext <;> assumption

/-- The kernel is exactly the actual scalar ideal, not a substitute quotient. -/
theorem quadraticResidueHom_ker (A T : ℤ) (n : ℕ) :
    RingHom.ker (quadraticResidueHom A T n)=Ideal.span {(n : QuadraticAlgebra ℤ A T)} := by
  ext z
  change quadraticResidueHom A T n z=0 ↔ _
  rw [Ideal.mem_span_singleton]
  constructor
  · intro h
    have hr : (z.re : ZMod n)=0 := congrArg QuadraticAlgebra.re h
    have hi : (z.im : ZMod n)=0 := congrArg QuadraticAlgebra.im h
    obtain ⟨x,hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re n).mp hr
    obtain ⟨y,hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im n).mp hi
    refine ⟨⟨x,y⟩,?_⟩
    apply QuadraticAlgebra.ext
    · simpa using hx
    · simpa using hy
  · rintro ⟨w,rfl⟩
    rw [map_mul,map_natCast]
    have hn : (n : QuadraticAlgebra (ZMod n) (A : ZMod n) (T : ZMod n))=0 := by
      apply QuadraticAlgebra.ext <;> simp
    rw [hn,zero_mul]

/-- Exact quadratic presentation of the actual scalar quotient. -/
noncomputable def quadraticResidueEquiv (A T : ℤ) (n : ℕ) :
    (QuadraticAlgebra ℤ A T ⧸ Ideal.span {(n : QuadraticAlgebra ℤ A T)}) ≃+*
      QuadraticAlgebra (ZMod n) (A : ZMod n) (T : ZMod n) :=
  (Ideal.quotEquivOfEq (quadraticResidueHom_ker A T n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (quadraticResidueHom_surjective A T n))

/-- Every actual scalar quotient is identified in the original basis. -/
noncomputable def basisResidueEquiv {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (he : e 0=1) (n : ℕ) :
    (B ⧸ Ideal.span {(n : B)}) ≃+*
      QuadraticAlgebra (ZMod n) (basisSquareConstant e : ZMod n) (basisSquareTrace e : ZMod n) := by
  let f := basisQuadraticEquiv e he
  have h : Ideal.span {(n : B)} =
      (Ideal.span {(n : QuadraticAlgebra ℤ (basisSquareConstant e) (basisSquareTrace e))}).map
        f.toRingHom := by simp [Ideal.map_span]
  exact (Ideal.quotientEquiv _ _ f.toRingEquiv h).symm.trans
    (quadraticResidueEquiv _ _ n)

/-- The same integral basis binds the quadratic parameters to its trace discriminant. -/
theorem discr_basis_one {B : Type*} [CommRing B]
    (e : Module.Basis (Fin 2) ℤ B) (he : e 0=1) :
    Algebra.discr ℤ e=(basisSquareTrace e)^2+4*basisSquareConstant e := by
  let A := basisSquareConstant e
  let T := basisSquareTrace e
  let f := basisQuadraticEquiv e he
  have hb : f ∘ QuadraticAlgebra.basis A T = e := by
    funext i
    fin_cases i <;> simp [Function.comp_def,f,basisQuadraticEquiv_apply,
      QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd,he]
  have hm : Algebra.traceMatrix ℤ (QuadraticAlgebra.basis A T)=!![2,T;T,T^2+2*A] := by
    ext i j
    rw [Algebra.traceMatrix_apply,Algebra.traceForm_apply,algebraTrace_eq_coefficients]
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticAlgebra.basis,QuadraticAlgebra.linearEquivTuple,QuadraticAlgebra.equivProd]
    all_goals ring
  have h := Algebra.discr_eq_discr_of_algEquiv (QuadraticAlgebra.basis A T) f
  rw [hb] at h
  rw [← h,Algebra.discr_def,hm]
  simp [Matrix.det_fin_two,A,T]
  ring

/-- Units of a quadratic algebra are exactly pairs with unit norm. -/
noncomputable def quadraticUnitsEquivNormPairs {R : Type*} [CommRing R] (A T : R) :
    (QuadraticAlgebra R A T)ˣ ≃
      {p : R × R // IsUnit (p.1*p.1+T*p.1*p.2-A*p.2*p.2)} where
  toFun z := ⟨⟨z.val.re,z.val.im⟩,by
    have h := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp z.isUnit
    simpa only [QuadraticAlgebra.norm_def] using h⟩
  invFun p := (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
    (show IsUnit (⟨p.val.1,p.val.2⟩ : QuadraticAlgebra R A T).norm from p.prop)).unit
  left_inv z := by apply Units.ext; exact IsUnit.unit_spec _
  right_inv p := by
    apply Subtype.ext
    change _ = p.val
    have h := IsUnit.unit_spec (QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (show IsUnit (⟨p.val.1,p.val.2⟩ : QuadraticAlgebra R A T).norm from p.prop))
    exact congrArg (fun z : QuadraticAlgebra R A T => (z.re,z.im)) h

/-- All four dyadic coefficient cases, including the repeated-root algebra. -/
theorem card_quadraticUnits_mod_two (A T : ZMod 2) :
    Nat.card (QuadraticAlgebra (ZMod 2) A T)ˣ =
      if T=0 then 2 else if A=0 then 1 else 3 := by
  rw [Nat.card_congr (quadraticUnitsEquivNormPairs A T)]
  simp only [isUnit_iff_ne_zero]
  fin_cases A <;> fin_cases T <;> rw [Nat.card_eq_fintype_card] <;> decide

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- Quadratic coordinates of the same actual maximal order modulo any n. -/
noncomputable def maximalOrderResidueEquiv (hD : b^2-4*a*c<0) (n : ℕ) :
    (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {(n : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))}) ≃+*
      QuadraticAlgebra (ZMod n)
        (basisSquareConstant (maximalOrderBasisOne a b c hD) : ZMod n)
        (basisSquareTrace (maximalOrderBasisOne a b c hD) : ZMod n) :=
  basisResidueEquiv _ (maximalOrderBasisOne_zero a b c hD) n

/-- The quadratic parameters use the same field discriminant, not D. -/
theorem maximalOrder_parameters_discriminant (hD : b^2-4*a*c<0) :
    letI := fractionNumberField a b c hD
    (basisSquareTrace (maximalOrderBasisOne a b c hD))^2+
      4*basisSquareConstant (maximalOrderBasisOne a b c hD)=
        NumberField.discr (FractionRing (CoefficientOrder a b c)) := by
  letI := fractionNumberField a b c hD
  rw [← discr_basis_one _ (maximalOrderBasisOne_zero a b c hD)]
  exact NumberField.discr_eq_discr _ (maximalOrderBasisOne a b c hD)

/-- The actual maximal conductor residue ring in its original field coordinates. -/
noncomputable def maximalConductorResidueEquiv (hD : b^2-4*a*c<0) :
    (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸ orderConductor a b c) ≃+*
      QuadraticAlgebra (ZMod (orderIndex a b c))
        (basisSquareConstant (maximalOrderBasisOne a b c hD) : ZMod (orderIndex a b c))
        (basisSquareTrace (maximalOrderBasisOne a b c hD) : ZMod (orderIndex a b c)) :=
  (Ideal.quotEquivOfEq (orderConductor_eq_span_index a b c hD)).trans
    (maximalOrderResidueEquiv a b c hD _)

/-- The unevaluated maximal residue-unit numerator is exactly the norm-unit pair count. -/
theorem card_maximalConductorResidueUnits_eq_normPairs (hD : b^2-4*a*c<0) :
    Nat.card (ConductorResidueUnits a b c)=
      Nat.card {p : ZMod (orderIndex a b c) × ZMod (orderIndex a b c) //
        IsUnit (p.1*p.1+(basisSquareTrace (maximalOrderBasisOne a b c hD) : ZMod (orderIndex a b c))*p.1*p.2-
          (basisSquareConstant (maximalOrderBasisOne a b c hD) : ZMod (orderIndex a b c))*p.2*p.2)} :=
  Nat.card_congr ((Units.mapEquiv (maximalConductorResidueEquiv a b c hD).toMulEquiv).toEquiv.trans
    (quadraticUnitsEquivNormPairs _ _))

/-- Dyadic units of the same maximal order, without a conductor or maximality certificate. -/
theorem card_maximalOrderResidueUnits_mod_two (hD : b^2-4*a*c<0) :
    Nat.card (NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)) ⧸
      Ideal.span {(2 : NumberField.RingOfIntegers (FractionRing (CoefficientOrder a b c)))})ˣ =
      if (basisSquareTrace (maximalOrderBasisOne a b c hD) : ZMod 2)=0 then 2
      else if (basisSquareConstant (maximalOrderBasisOne a b c hD) : ZMod 2)=0 then 1 else 3 := by
  simpa only [Nat.cast_ofNat] using
    (Nat.card_congr (Units.mapEquiv (maximalOrderResidueEquiv a b c hD 2).toMulEquiv).toEquiv).trans
      (card_quadraticUnits_mod_two _ _)

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.basisSquareConstant
#assert_standard_axioms BinaryNormIdeal.basisSquareTrace
#assert_standard_axioms BinaryNormIdeal.basis_expansion
#assert_standard_axioms BinaryNormIdeal.basisQuadraticEquiv
#assert_standard_axioms BinaryNormIdeal.basisQuadraticEquiv_apply
#assert_standard_axioms BinaryNormIdeal.quadraticResidueHom
#assert_standard_axioms BinaryNormIdeal.quadraticResidueHom_surjective
#assert_standard_axioms BinaryNormIdeal.quadraticResidueHom_ker
#assert_standard_axioms BinaryNormIdeal.quadraticResidueEquiv
#assert_standard_axioms BinaryNormIdeal.basisResidueEquiv
#assert_standard_axioms BinaryNormIdeal.discr_basis_one
#assert_standard_axioms BinaryNormIdeal.quadraticUnitsEquivNormPairs
#assert_standard_axioms BinaryNormIdeal.card_quadraticUnits_mod_two
#assert_standard_axioms BinaryNormIdeal.maximalOrderResidueEquiv
#assert_standard_axioms BinaryNormIdeal.maximalOrder_parameters_discriminant
#assert_standard_axioms BinaryNormIdeal.maximalConductorResidueEquiv
#assert_standard_axioms BinaryNormIdeal.card_maximalConductorResidueUnits_eq_normPairs
#assert_standard_axioms BinaryNormIdeal.card_maximalOrderResidueUnits_mod_two
